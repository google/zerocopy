# High- and Mid-Level IR Optimizations, Lowering, and Transformations: Real-World Tools, Historical Failures, and Anneal Refinement Mapping

## Summary

### Part I — Real-World Verification Tools and Refinement Architecture Mapping

High- and mid-level compiler transformations—spanning Rust HIR/THIR,
`Runtime(PostCleanup)` MIR, block-argument SSA (`AnSSA`), LLVM IR, MLIR, and
CompCert `Clight`/`RTL`/`BTL`—alter local state representations (stack slots vs.
SSA registers, aggregates vs. scalar leaves, closures and coroutines vs.
first-order state machines, primal scalars vs. dual numbers or reverse-mode
tapes) and internal step counts ($1 \to 0$ dead-code deletion, $1 \to k$
lowering and unrolling, $k \to 1$ vectorization and strength reduction) while
preserving external observable behavior. Across all 23 transformation use cases
in Sub-Domain 3 and seven cross-cutting industrial and mechanized compiler
frameworks (`Alive2`, `Crellvm`, `Vellvm`/`VIR`, `CompCert`/`CompCertSSA` and
`Chamois-CompCert`, `Peggy`/`egg`/`egglog`/Cranelift `aegraphs`, `Lean-MLIR`,
and `CakeML`), every tool's verification contract reduces to Anneal's four
orthogonal `trusted/lean/` primitives without introducing pass-specific trusted
axioms:

1. **Directional behavioral refinement (`Language SemObs`, `BehaviorCodec`, and
   `Compiles` / `Abstracts`):**
   Every IR instantiates `Language SemObs` with
   `sem : Prog → Query → Partial (Out → Prop)`. Because `Compiles L₁ L₂ codec s t`
   is the directional preorder inequality
   `L₂.sem t ≤ codec.toMorphism (L₁.sem s)` where Undefined Behavior
   (`Partial.ub`, `defined = False`) is the top element, optimizations that
   reduce UB—such as `mem2reg` refining an uninitialized stack read into a
   frozen SSA value (`mem2reg_uninit_refines`), Tree Borrows redundant-read
   elimination avoiding conflicting tag invalidation, Function-Entry `Protector`
   removal during function inlining (`inline_drops_protector_refines`), or
   C-to-Rust signed-overflow wrapping—are sound refinements even where
   symmetric equivalence (`=`) fails (`mem2reg_uninit_not_symmetric`,
   `inline_protector_not_reversible`). Conversely, operations that terminate via
   defined Rust panics (`.terminated trace .unwind` on division by zero or slice
   bounds checks) carry a distinct observable spine (`SemObs`) from normal
   return, so `Compiles` structurally rejects deleting unused panicking
   operations (`dce_panicking_div_unsound`) or hoisting trapping operations
   above zero-trip loops (`licm_trapping_zero_trip_unsound`) unless accompanied
   by a non-trapping or trip-count dominance witness (`dce_guarded_div_compiles`).
2. **Step-count elasticity without coinduction (`SmallStepMachine` and
   `EventualBehaviorOf`):**
   Moving the finite step count inside the outcome constructor
   `EventualOut Obs Val` (`.terminated (trace : List Obs) (term : TerminationKind Val)`
   with existential step count `∃ n` vs. `.diverges` with universal step count
   `∀ n`) decouples internal silent step counts ($1 \to 0$, $1 \to k$,
   $k \to 1$, and polyhedral iteration permutations) from the external
   `BehaviorCodec` while strictly preserving bidirectional termination
   (`Term ↔ Term`, `Div ↔ Div`) and finite-prefix safety.
3. **Open-world call framing and immediate protector enforcement
   (`StepResult.externalCall`):**
   Modeling opaque foreign or indirect calls via
   `StepResult.externalCall (boundaryInv : Bool) (branches : State → Prop)`
   enforces caller-side ABI, aliasing, and Tree-Borrows `Protector` invariants
   at the call boundary. Eliminating a store `*x = 1` before
   `opaque_ext_call(); *x = 2;` when `opaque_ext_call()` may diverge or exit is
   sound if and only if `StepResult.externalCall` and active caller protectors
   forbid foreign reads of caller-protected `&mut T` *at the moment of the
   foreign access* rather than only at function return
   (`dse_across_diverging_external_call_unsound_if_late_protector`).
4. **Anti-degeneracy, non-vacuity, and fine-grained obligation accounting
   (`ProductiveOn`, `InhabitedPre`, and `VerificationResult`):**
   Pairing `Compiles` with `InhabitedPre pre ∧ L₁.ProductiveOn pre s` blocks
   vacuous compilation of unconditionally UB source programs (such as UB C
   functions in `c2rust` migration, `c2rust_productiveOn_blocks_ub_source`) and
   encodes stateful resumption invariants (such as `Pin<&mut Self>` address
   stability across coroutine `.await` points, `coroutine_pinned_productive`),
   while `VerificationResult` and `CertifiedOptimizationPass` audit each pass's
   side-condition certificates and syntactic/cost normal-form obligations.

### Part II — Historical Verification Failures, Postmortems, and Architectural Defenses

Mid-level intermediate representation (IR) optimizers and high-level language
lowering pipelines sit at the most error-prone seam in modern compilers: they
must preserve high-level language invariants (such as Rust ownership, borrow
protectors, pin stability, drop ordering, and forward progress) while rewriting
control-flow graphs, promoting stack memory to SSA registers, and eliminating
redundant computations. Across three decades of production compilers (`LLVM`,
`rustc`, `GCC`) and formal verification systems (`CompCert`, `Vellvm`,
`Crellvm`, `Alive2`, `Simuliris`, `C2Rust`/`CROWN`), historical failures in this
domain cluster into fifteen recurring root causes across three structural axes:

1. **Non-compositional semantics and broken refinement preorders in IR
   optimizations:**
   - **Dual `undef` / `poison` instability (`PLDI 2017`, `PLDI 2021`):**
     Giving uninitialized or overflowed values per-use angelic nondeterminism
     (`undef`) alongside tainting deferred undefined behavior (`poison`) makes
     the composition of individually plausible passes—Specifically Global Value
     Numbering (`GVN`), `LoopUnswitch`, Scalar Replacement of Aggregates
     (`SROA`), and `InstCombine` (`select`-to-branch)—end-to-end unsound on
     well-defined source programs, forcing the introduction of `freeze` and the
     deprecation of `undef`.
   - **Pointer-integer congruence collapse (`OOPSLA 2018`):** Replacing a
     pointer `p` with `q` under an equality branch `ptrtoint(p) == ptrtoint(q)`
     in `GVN` substitutes a one-past-the-end provenance tag for a valid adjacent
     object's provenance tag, turning a valid dereference into out-of-bounds UB.
   - **`rustc` MIR optimizer and `noalias` miscompilations (`#54878`, `#63818`,
     `#63934`, `#110947`, `#118328`, `#120613`, `#141038`, `#146383`):**
     Emitting LLVM `noalias` on `&mut Self` for self-referential coroutine state
     machines broke `async`/`await` for years until `!Unpin` suppression and
     `PtrMetadata` fixes landed; within `rustc_mir_transform`, `GVN`,
     `ConstProp`, `DestinationPropagation`, and `DeadStoreElimination` (`DSE`)
     repeatedly miscompiled partial moves, mutating borrows, pointer-typed enum
     niches, and `StorageLive`/`StorageDead` stack-slot reuse ranges.
   - **Call-boundary protector failure under divergence (`POPL 2020`,
     `PLDI 2025`, `Simuliris`):** Mechanizing Stacked Borrows and Tree Borrows
     in Rocq/Simuliris revealed that eliminating a dead store `*x = v₁` before
     an unknown external call `ext(); *x = v₂` is **unsound** if `ext()` never
     returns (`loop {}` or `abort()`) unless function-entry protectors enforce
     disjointness eagerly at the foreign access (`Strong` protectors) or emit a
     virtual write on function entry.
   - **Forward-progress infinite-loop deletion (`rust-lang/rust#28728`):**
     Applying C++11's forward-progress assumption (`[intro.progress]`) to Rust
     caused LLVM to delete side-effect-free `loop {}` blocks and execute
     unreachable basic blocks after them until LLVM 12 separated `mustprogress`
     and `willreturn` from default CFG semantics.

2. **State-corruption hazards during SSA destruction, control-flow lowering, and
   high-level desugaring:**
   - **Briggs/Boissinot `Lost-Copy` and `Swap` hazards (`SPE 1998`, `JAR 2008`,
     `CGO 2009`):** Naively sequentializing $\phi$-nodes during out-of-SSA
     translation without critical-edge splitting and cycle-breaking scratch
     moves overwrites live source operands on loop backedges.
   - **Tail-call stack-escape use-after-free (`LLVM tailcallelim`):** Converting
     a tail call `return f(&local)` into a frame-reusing jump or loop when a
     stack local's address or `byval` slot escapes into `f` clobbers the pointee
     during `f`'s prologue.
   - **Coroutine field packing and drop-elaboration unwind hazards (`#24292`,
     `#63616`, `ElaborateDrops`):** Desynchronized `StorageLive`/`StorageDead`
     markers across `Yield` points pack simultaneously live coroutine locals
     into overlapping union offsets; omitting drop-flag updates or panic guards
     during `ElaborateDrops` causes double-drops on unwind or use-after-free
     when safe code bypasses `Drop` ("Leakpocalypse").

3. **Architectural limits of external translation validators, proof-hint
   compilers, and automated C-to-Rust lifters:**
   - **Bounded SMT validation (`Alive2`, `PLDI 2021`):** Unrolling loops to a
     fixed bound $k$ (`-tv-unroll=k`) misses loop-carried miscompilations at
     iteration $k + 1$, while bit-blasting nonlinear integer multiplication,
     floating-point reductions, and wide SIMD permutes triggers SMT timeouts.
   - **Intrusive proof-hint maintenance collapse (`Crellvm`, `PLDI 2018`) and
     pass-coverage limits (`Vellvm`, `ICFP 2021`):** Instrumenting C++ LLVM
     passes to emit step-by-step relational proof hints proved brittle under
     upstream LLVM churn, while full monadic/ITree LLVM semantics remain too
     heavy to verify production C++ optimization passes directly.
   - **Vacuity and raw-pointer fallbacks in C-to-Rust lifting (`C2Rust`,
     `CROWN`, `CAV 2023`):** Ownership-guided lifters cannot safely translate C
     `union`s, non-tree aliasing, or variadics, and naive C-to-Rust refinement
     proofs either hold vacuously when the C source exhibits signed-overflow UB
     or introduce fresh Rust UB by translating valid C `(NULL, 0)` empty buffers
     into `core::slice::from_raw_parts(null(), 0)`.

In Anneal (`trusted/lean` at `24367bd1a8c784f2578535954f9915e24894a56f` and
`MIR-to-x86-64` at `5fc1139f2208b3c9cfb513573c4a731cc32bb457`), all fifteen
failure classes are ruled out structurally by the four orthogonal `trusted/lean/`
primitives—`Language SemObs` + `BehaviorCodec` + `Compiles`/`Abstracts`,
`ProductiveOn` + `InhabitedPre`, `SmallStepMachine` + `EventualBehaviorOf` +
`StepResult.externalCall`, and positive per-obligation `VerificationResult`—as
mechanized in the zero-axiom Lean 4.34.1 canary development in
[`support/MidLevelIrFailureCanaries.lean`](support/MidLevelIrFailureCanaries.lean).

## Applicability

This package unifies the real-world verification tool mapping and the historical verification failure postmortems for this domain against the durable `joshlf/anneal` repository revisions (`24367bd1a8c784f2578535954f9915e24894a56f`, `5fc1139f2208b3c9cfb513573c4a731cc32bb457`, and `c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`) and the self-contained Lean 4 (`v4.34.1`, `5045d0056413266e57c625dcd7c365b10e377c52`) refinement definitions below.

### Self-Contained Anneal Refinement Primitives (`Language`, `Behavior`, `StepResult`, `VerificationResult`)

To ensure this report is self-contained without depending on unmerged development branches, the core Lean 4 refinement definitions referenced throughout Part I and Part II are given inline below:

```lean
/-- Constructive partial behavior cell representing `B ∪ {UB}`. -/
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

/-- Pointwise refinement preorder on `Partial (Out → Prop)`:
`p₁ ≤ p₂` iff every defined specification query `h₂ : p₂.defined` is defined in
`p₁` (`h₁ : p₁.defined`) and every outcome permitted by `p₁` satisfies `p₂`. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

structure Language (SemObs : Type := Unit) where
  Prog  : Type
  Query : Type
  Out   : Type
  dom   : Prog → Query → Prop := fun _ _ => True
  obs   : Out → SemObs
  sem   : Prog → Behavior Query Out

def Language.SpecOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    Behavior L.Query L.Out :=
  fun q => { defined := pre q, val := fun _ o => post q o }

/-- Non-vacuity witness: at least one query in `dom` satisfies `pre`. -/
def NonVacuousOn {Query : Type} (dom pre : Query → Prop) : Prop :=
  ∃ q, dom q ∧ pre q

abbrev InhabitedPre {Query : Type} (pre : Query → Prop) : Prop :=
  ∃ q, pre q

/-- Dijkstra's Law of the Excluded Miracle: every admitted query has at least
one defined outcome. -/
def Language.ProductiveOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o

/-- Complete, non-vacuous behavioral verification of `prog` against `(pre, post)`
within `prog`'s own domain `L.dom prog`. -/
def Language.Verified {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  NonVacuousOn (L.dom prog) pre ∧
  L.ProductiveOn pre prog ∧
  L.sem prog ≤ L.SpecOn pre post

/-- Partial behavior codec between two languages `L₁` and `L₂` sharing `SemObs`. -/
structure BehaviorCodec {SemObs : Type} (L₁ L₂ : Language SemObs) where
  encodeQuery : L₁.Query → L₂.Query
  decodeQuery : L₂.Query → L₁.Query
  decode_encode_query : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁
  encodeOut : L₁.Out → L₂.Out
  decodeOut : L₂.Out → Option L₁.Out
  decode_encode_out : ∀ o₁, decodeOut (encodeOut o₁) = some o₁
  encode_of_decode_some : ∀ {o₂ o₁}, decodeOut o₂ = some o₁ → encodeOut o₁ = o₂
  obs_decodeOut : ∀ {o₂ o₁}, decodeOut o₂ = some o₁ → L₂.obs o₂ = L₁.obs o₁

/-- Right-nested conjunction of a list of propositions. -/
def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

/-- A named proof obligation with a private constructor so proof authors cannot
forge weaker propositions under a trusted obligation identifier. -/
structure Obligation (Id : Type) where
  private mk ::
  id   : Id
  prop : Prop

abbrev Obligation.assumed {Id : Type} (id : Id) : Obligation Id :=
  ⟨id, False⟩

structure TrustPolicy (Id : Type) where
  isAllowed : Id → Prop

/-- Positive per-obligation verification gate preventing Principle-of-Explosion
contamination from waived or assumed obligations. -/
def VerificationResult {Id : Type} [DecidableEq Id]
    (policy : TrustPolicy Id) (waived : List Id)
    (obligations : List (Obligation Id)) : Prop :=
  AllHold (waived.map policy.isAllowed) ∧
  AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))

inductive ChoiceKind where
  | demonic
  | angelic

inductive FailureKind where
  | ub
  | fuelExhausted

inductive Terminal (Val : Type) where
  | normal (v : Val)
  | panic
  | abort

/-- Single-step operational outcome for `SmallStepMachine`. -/
inductive StepResult (State Obs Val : Type) where
  | step (next : State) (obs : List Obs := [])
  | choice (kind : ChoiceKind) (branches : State → List Obs → Prop)
  | terminated (term : Terminal Val) (obs : List Obs := [])
  | failed (kind : FailureKind)
  | stuck

/-- Structural external-call boundary guard checking `boundaryInv` at the call
transition before branching demonically over environment return states. -/
def StepResult.externalCall {State Obs Val : Type}
    (boundaryInv : Bool) (branches : State → List Obs → Prop) :
    StepResult State Obs Val :=
  if boundaryInv then .choice .demonic branches else .failed .ub

inductive EventualOut (Obs Val : Type) where
  | terminated (trace : List Obs) (term : Terminal Val)
  | diverges
```

### Part I Applicability — Real-World Verification Tools

The findings in this report apply to the 15 subjects recorded in `REPORT.json`
and establish how real-world mid-level IR optimization, language lowering, and
relational equivalence tools map onto Anneal's verification architecture:

- **Anneal core and compiler branches:**
  `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`
  (`trusted/lean/Trusted/Refinement.lean`,
  `trusted/lean/Trusted/StepResult.lean`,
  `trusted/lean/Trusted/MirSemantics.lean`) and
  `joshlf/anneal@5fc1139f2208b3c9cfb513573c4a731cc32bb457`
  (`theory/Anneal/Compiler/NaiveCodegen.lean`,
  `theory/Anneal/Compiler/Peephole.lean`), evaluated alongside the
  `BehaviorCodec`, `EventualBehaviorOf`, `ProductiveOn`, and
  `CertifiedOptimizationPass` extensions established in companion report
  `anneal-behavior-codec-and-progress-refinement-2026`.
- **Verification and compiler toolchains:**
  `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`,
  invoked with `-DElab.async=false -Ddebug.skipKernelTC=false`) and
  `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`,
  specifically `compiler/rustc_mir_transform/`, `compiler/rustc_monomorphize/`,
  and `compiler/rustc_codegen_llvm/`).
- **External IR verification, optimization, and lowering tools:**
  The eleven external tool families identified in `REPORT.json` (`Alive2`,
  `Crellvm`, `Vellvm`/`VIR`, `CompCert`/`CompCertSSA`/`Chamois-CompCert`,
  `Peggy`/`egg`/`egglog`/Cranelift `aegraphs`, `Lean-MLIR`, `CakeML`,
  `Stacked Borrows`/`Tree Borrows`/`Miri`/`SimulIris`,
  `PolyVerify`/`Pluto`/`ISL`/`Polly`/`Polygeist`/`HELIX`/`VeGen`/`Diospyros`,
  `CertiCoq`/Maranget/`Enzyme`/`Tapenade`/`CertiGrad`/`SciLean`, and
  `SymDiff`/`LLReve`/`UC-KLEE`/`C2Rust`/`CROWN`/`Laertes`/`TCE`) are analyzed
  as comparative architectural subjects and candidate untrusted certificate
  producers or verified pass architectures for Anneal's `theory/` layer.

All seven core semantic discriminators and counterexamples in this report are
mechanized in the preserved standalone Lean 4 probe
[MidLevelOptimizationAndLoweringProbes.lean](support/MidLevelOptimizationAndLoweringProbes.lean).

### Part II Applicability — Historical Verification Failures and Postmortems

This report applies to the design and verification of mid-level IR optimization
passes, high-level Rust/MIR lowering transformations, and cross-language
translation validators targeting Anneal's `trusted/` semantic kernel. The fifteen
subjects recorded in `REPORT.json` fall into four groups:

1. **Anneal's Pinned `trusted/` Foundation (`joshlf/anneal`):**
   - `trusted/lean` at `24367bd1a8c784f2578535954f9915e24894a56f`
     (`trusted/lean/Trusted/Refinement.lean`,
     `trusted/lean/Trusted/StepResult.lean`,
     `trusted/lean/Trusted/MirSemantics.lean`), and
   - `MIR-to-x86-64` at `5fc1139f2208b3c9cfb513573c4a731cc32bb457`
     (`trusted/lean/Trusted/Refinement.lean`,
     `trusted/lean/Trusted/X86Semantics.lean`,
     `trusted/audit/TrustedBoundary.lean`).
2. **Primary Literature on LLVM IR Undefined Behavior, Memory Models, and
   Rust Aliasing:**
   - Lee et al., *Taming Undefined Behavior in LLVM*, PLDI 2017 (`10.1145/3062341.3062343`);
   - Lee et al., *Reconciling High-Level Optimizations and Low-Level Code in
     LLVM*, OOPSLA 2018 (`10.1145/3276495`);
   - Lopes et al., *Alive2: Bounded Translation Validation for LLVM*, PLDI 2021
     (`10.1145/3453483.3454030`);
   - Jung et al., *Stacked Borrows: An Aliasing Model for Rust*, POPL 2020
     (`10.1145/3371109`);
   - Villani et al., *Tree Borrows*, PLDI 2025 (`10.1145/3735592`); and
   - `Simuliris` mechanized Rocq development at
     `e3abfcdc301f92250d4227fc03c00463bf57b982`.
3. **Primary Literature on SSA Destruction, Credible Compilation, Mechanized IR
   Semantics, and C-to-Rust Lifting:**
   - Briggs et al., *Practical Improvements to the Construction and Destruction
     of Static Single Assignment Form*, SPE 1998
     (`10.1002/(SICI)1097-024X(199807)28:8<859::AID-SPE175>3.0.CO;2-Z`);
   - Rideau, Serpette, and Leroy, *Tilting at Windmills with Coq: Formal
     Verification of a Compilation Algorithm for Parallel Moves*, JAR 2008
     (`10.1007/s10817-008-9097-3`);
   - Boissinot et al., *Revisiting Out-of-SSA Translation for Correctness, Code
     Quality, and Efficiency*, CGO 2009 (`10.1109/CGO.2009.19`);
   - Kang et al., *Crellvm: Verified Credible Compilation for LLVM*, PLDI 2018
     (`10.1145/3192366.3192398`);
   - Zakowski et al., *Modular, Compositional, and Executable Formal Semantics
     for LLVM IR* (`Vellvm`), ICFP 2021 (`10.1145/3473572`); and
   - Zhang et al., *Ownership Guided C to Rust Translation* (`CROWN`), CAV 2023
     (`10.1007/978-3-031-37709-9_22`).
4. **Historical `rust-lang/rust` Soundness and Miscompilation Issues:**
   - Issues `#24292` (Drop leakpocalypse / `Vec::drain`), `#28728` (infinite
     loop miscompilation), `#54878` / `#63818` / `#63934` (`mutable-noalias` on
     self-referential generators/Futures), `#63616` (partial initialization in
     generators), `#110947` / `#118328` (`ConstProp` miscompilations), `#120613`
     / `#141038` (`GVN` partial-move and aliasing miscompilations), and
     `#146383` (`DestinationPropagation` miscompilation).

Claims about upstream compiler bugs are scoped to the specific paper models or
issue revisions cited under **Evidence**. Claims about Anneal's prevention
mechanisms apply to the four `trusted/` primitives and are mechanically checked
by the Lean 4.34.1 kernel in `support/MidLevelIrFailureCanaries.lean`.

## Findings

### Part I — Real-World Verification Tools Mapped to Anneal's Refinement Primitives

### 1. Cross-Cutting IR Optimization and Verification Frameworks

Before examining individual optimization categories, seven cross-cutting
frameworks define the design space for verifying mid-level IR transformations.

```
Basis: documentation + source + execution + derived
```

#### 1.1 `Alive2` (`AliveToolkit/alive2`)

1. **Goals and Target Users:** Bounded SMT-based translation validator for
   intra-procedural LLVM IR transformations (`InstCombine`, `GVN`, `SROA`,
   `LoopVectorize`, `SLPVectorizer`), used by LLVM compiler engineers to catch
   miscompilations (`llvm-tv`) and check Alive DSL peephole rules.
2. **History and Lineage:** Evolved from the original `Alive` DSL verifier
   (Lopes, Menendez, Nagarakatte, Regehr, PLDI 2015, DOI
   `10.1145/2737924.2737965`) into `Alive2` (Lopes, Lee, Hur, Liu, Regehr,
   PLDI 2021, DOI `10.1145/3453483.3454030`) after the LLVM community
   formalized `poison`, `undef`, and the `freeze` instruction (Lee et al., PLDI
   2017, DOI `10.1145/3062341.3062343`).
3. **Design Philosophy and Tradeoffs:** Fully automatic push-button SMT
   encoding into `QF_UFBV` / `QF_ABV` (discharged via Z3) with bounded loop
   unrolling. Trades unbounded loop completeness and proof-assistant kernel
   certificates for immediate bug-finding coverage across production LLVM passes
   and full byte-level `poison`/provenance memory modeling.
4. **Ecosystem Comparison:** Unlike `Vellvm` or `CompCert` (which require
   manual Coq proofs per pass) and `Crellvm` (which requires pass instrumentation
   to emit relational hints), `Alive2` operates as a black-box validator over
   unmodified LLVM passes, but trusts Z3 and bounds loops to $k$ iterations.
5. **Formal Theory and TCB:** Encodes directional refinement $t \sqsubseteq s$
   over a three-tiered domain: immediate Undefined Behavior ($\mathsf{UB}$),
   delayed per-bit/per-value `poison` (absorbing non-trapping arithmetic
   overflows), and non-deterministic `undef` sets, together with a twin-allocation
   pointer provenance and byte-level memory model (`util/smt.cpp`, `ir/memory.cpp`).
   Its TCB comprises the C++ VC generator and Z3.
6. **Mapping onto Anneal's 4 `trusted/` Primitives:**
   - `Alive2`'s directional refinement relation ($s \text{ is non-UB} \implies
     t \text{ is non-UB} \land \text{vals}(t) \subseteq \text{vals}(s)$) is
     isomorphic to `Compiles L_MIR L_MIR idCodec s t` in
     `Trusted/Refinement.lean` (lines 267–275, 368–373), where `Partial.ub` is
     $\top$ and `Partial.val` holds the set of non-deterministic outcomes.
   - To eliminate Z3 and `Alive2`'s C++ encoder from Anneal's TCB, `Alive2`-style
     bounded bitvector and array VCs are discharged in `theory/` via
     bit-blasting + `LRAT` or `Alethe` certificates checked inside the Lean 4
     kernel, surfacing per-block obligations in `VerificationResult`.

#### 1.2 `Crellvm` (`snu-sf/crellvm`)

1. **Goals and Target Users:** Credible compilation framework for LLVM (Kang,
   Kim, Song, Mullen, Hur, PLDI 2018, DOI `10.1145/3192366.3192377`) enabling
   pass authors to instrument production C++ LLVM passes (`GVN`, `LICM`, `SROA`,
   `InstCombine`) to emit compact relational simulation witnesses checked in Coq.
2. **History and Lineage:** Developed at Seoul National University's Software
   Foundations Lab (`snu-sf`), building on `Vellvm`, parameterized simulation
   (`paco`, Hur et al., POPL 2013), and the Twin-Allocation LLVM memory model
   (Lee et al., PLDI 2017).
3. **Design Philosophy and Tradeoffs:** Separates heuristic optimization search
   (untrusted C++) from post-hoc relational verification (Coq-verified validator).
   Avoids reimplementing LLVM in Coq while avoiding `Alive2`'s SMT loop bounds,
   at the engineering cost of instrumenting LLVM C++ passes to record hint logs.
4. **Ecosystem Comparison:** Bridges the gap between `CompCert` (constructive
   Coq compiler) and `Alive2` (unverified SMT translation validator) by
   producing machine-checkable Coq proofs for real LLVM passes.
5. **Formal Theory and TCB:** Relational Hoare logic over CFG simulation slices
   with ghost relational invariants (`MayDiff` sets tracking registers that
   intentionally differ between source and target, plus private stack/heap block
   injections). The TCB is restricted to the Coq LLVM IR semantics (` Vellvm`-derived)
   and the Coq theorem statement.
6. **Mapping onto Anneal's 4 `trusted/` Primitives:**
   - `Crellvm`'s relational simulation with `MayDiff` sets and private memory
     injections maps directly to `Compiles L_MIR L_MIR codec s t` over
     `EventualBehaviorOf`, where `codec` projects out frame-private allocations
     at function exit and `EventualBehaviorOf` absorbs silent step-count shifts.
   - Its Coq hint-checking boolean validator maps to a certifying checker
     `checkCrellvmCert s t cert = true → Compiles ... s t` in `theory/`, gated
     by `CertifiedOptimizationPass`.

#### 1.3 `Vellvm` and `VIR` (`vellvm/vellvm`)

1. **Goals and Target Users:** Mechanized formal semantics of LLVM SSA IR in Coq/Rocq
   for proving correctness of LLVM-targeting compilers (`Helix`, `CertiCoq`) and
   LLVM optimization passes (`vmem2reg`).
2. **History and Lineage:** `Vellvm` (Zhao, Nagarakatte, Martin, Zdancewic, POPL
   2012, DOI `10.1145/2103656.2103709`) mechanized operational SSA semantics and
   verified `vmem2reg` (PLDI 2013, DOI `10.1145/2491956.2462164`). Re-architected
   into `VIR` (Zakowski, Beck, Yoon, Zaichuk, Zaliva, Zdancewic, ICFP 2021, DOI
   `10.1145/3473572`) using modular **Interaction Trees (`ITrees`)** (Xia et
   al., POPL 2020, DOI `10.1145/3371119`).
3. **Design Philosophy and Tradeoffs:** `VIR` decomposes semantics into
   uninterpreted free monad event trees (`ITree E R`) interpreted through a
   layered stack of state, memory, `pick` (`undef` non-determinism), UB, and
   external I/O handlers, reasoned about via weak bisimulation (`eutt`,
   equivalence up to tau steps).
4. **Ecosystem Comparison:** Provides a compositional denotational/coinductive
   alternative to `CompCert`'s small-step labeled transition systems (`LTS`).
5. **Formal Theory and TCB:** Coinductive `ITree` monad with $\tau$-stuttering
   refinement (`eutt`). Its TCB includes Coq's coinductive guard checker and the
   top-level `VIR` handler stack.
6. **Mapping onto Anneal's 4 `trusted/` Primitives:**
   - Anneal's `SmallStepMachine` + `EventualBehaviorOf` (`EventualOut.terminated
     (trace : List Obs) (term : TerminationKind Val)` | `EventualOut.diverges`)
     achieves the exact same silent $\tau$-compression as `VIR`'s `eutt` without
     coinductive types or `Classical.choice` in `trusted/lean/`: `StepResult.step`
     emits `Obs`, `StepResult.choice` handles `pick` non-determinism,
     `StepResult.failed` handles UB, and `StepResult.externalCall` models
     uninterpreted external call events.

#### 1.4 `CompCert`, `CompCertSSA`, and `Chamois-CompCert` (`AbsInt/CompCert`)

1. **Goals and Target Users:** Safety-critical C compilation (`CompCert`, Leroy,
   CACM 2009, DOI `10.1145/1538788.1538814`; `AbsInt` commercial qualification
   for DO-178C aviation and nuclear systems), middle-end SSA optimizations
   (`CompCertSSA`, Barthe, Demange, Pichardie, ESOP 2012 / TOPLAS 2014, DOI
   `10.1145/2579080`), and aggressive block/superblock optimizations
   (`Chamois-CompCert`, Boulmé, Monniaux, Six, Gourdin et al., OOPSLA 2023, DOI
   `10.1145/3622840`).
2. **History and Lineage:** Initiated by Xavier Leroy at INRIA in 2005; extended
   with a verified SSA middle-end (`CompCertSSA`, INRIA Celtique) and superblock
   symbolic simulation (`RTLpath` and Block-Translational Language `BTL` in
   `Chamois-CompCert`, Verimag).
3. **Design Philosophy and Tradeoffs:** Combines **constructive verified passes**
   (for simple structural lowerings like `SimplLocals`, `Inlining`, `Tailcall`)
   with **verified translation validators** (`check s t = true → simulation s t`)
   for complex graph/polyhedral/scheduling algorithms (`SSA` construction,
   `Lazy Code Motion`, `BTL` superblock scheduling, register allocation).
4. **Ecosystem Comparison:** The gold standard for end-to-end verified
   compilation; `Chamois-CompCert`'s `BTL` single pass unifies value numbering,
   lazy code motion, strength reduction, and instruction scheduling via
   hash-consed symbolic execution trees.
5. **Formal Theory and TCB:** Forward simulation diagrams (lockstep, plus, star,
   and measure-indexed stuttering diagrams) flipped to backward simulations via
   target receptiveness and determinism (`common/Smallstep.v`), sharing a uniform
   block/offset/permission memory model (`common/Memory.v`, Leroy & Blazy, JAR
   2008).
6. **Mapping onto Anneal's 4 `trusted/` Primitives:**
   - Because Anneal's `Behavior` natively models demonic non-determinism via
     `Out → Prop` (`instPreorderFun` + `instPreorderProp`), forward simulation
     in `theory/` directly implies `Compiles L₁ L₂ codec s t` (`L₂.sem t ≤
     codec.toMorphism (L₁.sem s)`) **without** requiring target determinism to
     flip forward simulations into backward simulations!
   - `Chamois-CompCert`'s `BTL` block simulation checker maps directly to a
     kernel-reducible boolean validator in `theory/` discharging multi-step block
     transitions under `EventualBehaviorOf`.

#### 1.5 Equality Saturation and E-Graph Frameworks (`Peggy`, `egg`, `egglog`, Cranelift `aegraphs`)

1. **Goals and Target Users:** Mitigate the compiler phase-ordering problem by
   applying bidirectional algebraic and dataflow rewrites simultaneously over a
   compact congruence graph (`e-graph`) and extracting a minimum-cost target
   program.
2. **History and Lineage:** Pioneered for CFG/PEG compiler optimization by
   `Peggy` (Tate, Stepp, Tatlock, Lerner, POPL 2009, DOI
   `10.1145/1480881.1480915`); modernized with fast rebuilt congruence closure
   and e-class analyses in `egg` (`egraphs-good/egg`, Willsey et al., POPL 2021,
   DOI `10.1145/3434304`), unified with Datalog in `egglog`
   (`egraphs-good/egglog`, Zhang et al., PLDI 2023, DOI `10.1145/3591239`), and
   deployed in production in Cranelift's acyclic e-graph pass (`aegraphs`,
   Fallin, `bytecodealliance/wasmtime` `cranelift/codegen/src/egraph.rs`).
3. **Design Philosophy and Tradeoffs:** Purely functional e-graphs (`egg`/`egglog`)
   handle cyclic loops via $\theta$-nodes (PEGs) or scoped regions (`RVSDG`),
   whereas Cranelift's `aegraphs` embeds e-classes directly into the dominator
   tree of an SSA CFG for single-pass $O(N)$ compile-time budgets, Elaborating
   side-effecting and trapping instructions along a linear state skeleton.
4. **Ecosystem Comparison:** Replaces destructive sequential pass pipelines
   (`InstCombine` + `GVN` + `CSE` + `LICM`) with a single saturation + extraction
   phase (`Diospyros` and `Herbie` also build on `egg`).
5. **Formal Theory and TCB:** Congruence closure over term equivalence classes.
   Instead of verifying the complex e-graph union-find and ILP/greedy extractor,
   an e-graph solver emits a linear or DAG **rewrite explanation certificate**
   ($s = e_0 \to e_1 \to \dots \to e_k = t$).
6. **Mapping onto Anneal's 4 `trusted/` Primitives:**
   - The untrusted `egg`/`egglog`/`aegraphs` optimizer searches for the lowest-cost
     MIR/AnSSA body `t` and emits a DAG rewrite trace `cert`.
   - A small checker in `theory/` verifies each local step $e_i \to e_{i+1}$
     against verified directional refinement lemmas (`Compiles L L idCodec e_i
     e_{i+1}`) and composes them by transitivity (`Preorder.le_trans`,
     `Trusted/Refinement.lean` line 210), while `CertifiedOptimizationPass`
     audits `cost(t) < cost(s)` in `VerificationResult`.

#### 1.6 `Lean-MLIR` (`opencompl/lean-mlir`)

1. **Goals and Target Users:** Mechanized semantics and peephole verification
   framework in Lean 4 for MLIR dialects (`arith`, `comb`, `llvm`, `scf`),
   created by Siddharth Bhat, Alex Keizer, Chris Hughes, Andrés Goens, and
   Tobias Grosser (ITP 2024, `opencompl/lean-mlir@ae0dd933`, tag `ITP24`).
2. **History and Lineage:** Built directly in Lean 4 on top of intrinsically
   typed de Bruijn / SSA region calculi and Lean 4's `bv_decide` bitvector
   automation.
3. **Design Philosophy and Tradeoffs:** Uses intrinsically well-typed ASTs
   (`Com Γ eff ty`) parameterized by dialect operation signatures and purity
   effects (`EffectKind.pure` vs. `EffectKind.impure`), proving a generic lifting
   theorem (`denote_rewritePeepholeAt`) that lifts local DAG peephole refinements
   to full SSA regions with nested sub-regions, alongside verified `DCE` and
   `CSE`.
4. **Ecosystem Comparison:** Whereas `Alive2` uses external SMT and `Vellvm` uses
   Coq over flat LLVM CFGs, `Lean-MLIR` is native to Lean 4 and models MLIR's
   hierarchical region-based SSA directly.
5. **Formal Theory and TCB:** Denotational valuation into `Option`/`Poison`
   monads inside Lean 4; its TCB is Lean 4's kernel (plus `bv_decide`'s LRAT
   reflector when used).
6. **Mapping onto Anneal's 4 `trusted/` Primitives:**
   - `Lean-MLIR` dialect regions instantiate `Trusted.Language` directly in Lean 4,
     and its `Poison`/refinement ordering embeds into Anneal's `Partial`
     preorder (`instPreorderPartial`), allowing `Lean-MLIR` peephole theorems
     (`denote_rewritePeepholeAt`) to discharge `Compiles` obligations in
     `theory/` for Anneal's `AnSSA` dialect without translation across proof
     assistants.

#### 1.7 `CakeML` Verified Multi-IR Middle-End (`CakeML/cakeml`)

1. **Goals and Target Users:** End-to-end verified compiler from Standard ML to
   machine code (`x86-64`, `ARM`, `RISC-V`, `MIPS`) mechanized in HOL4 (Tan,
   Myreen, Kumar, Fox, Owens, Norrish, ICFP 2016 / JFP 2019, DOI
   `10.1017/S0956796818000229`).
2. **History and Lineage:** Developed across Cambridge, Chalmers, ANU, Data61,
   and UNSW, pioneering **functional big-step semantics** (Owens, Myreen, Kumar,
   Tan, ESOP 2016, DOI `10.1007/978-3-662-49498-1_23`).
3. **Design Philosophy and Tradeoffs:** Decomposes high-to-low lowering across a
   tower of 12 specialized intermediate languages—including `flatLang` (pattern
   compilation), `closLang` (closure conversion), `bvl` (Bytecode-Value Language
   for inlining and expression optimization), `bvi` (exception-handling and
   tail-call normalization), `dataLang` (explicit call stack and abstract GC
   heap), and `wordLang` (word-level SSA/register allocation and bitvector
   optimizations).
4. **Ecosystem Comparison:** Demonstrates how high-level language features
   (algebraic datatypes, pattern matching, higher-order closures, exceptions) are
   systematically lowered before backend codegen, complementing `CompCert`'s
   C-level pipeline.
5. **Formal Theory and TCB:** Functional clock-indexed big-step evaluators
   (`evaluate (s with clock := k) env exp`) where divergence occurs iff every
   clock `k` returns `Rerr (Rabort Rtimeout_error)`.
6. **Mapping onto Anneal's 4 `trusted/` Primitives:**
   - `CakeML`'s functional clock-indexed evaluator is the exact big-step dual of
     Anneal's `BehaviorOf` (`ExecQuery State` with `steps : Nat`) and
     `EventualBehaviorOf`: clock exhaustion (`Rtimeout_error`) corresponds to
     `PrefixOutcome.running` in `Trusted/StepResult.lean` (lines 77–98), and
     each IR transition (`flatLang → closLang → bvl → bvi → dataLang → wordLang`)
     is a compositional `Compiles L_i L_{i+1} codec_i` link with a dedicated
     value/environment `BehaviorCodec`.

---

### 2. Category A: SSA Construction, Destruction, and Scalar Promotion (Use Cases 3.1–3.4)

```
Basis: source + execution + derived
```

#### 2.1 Use Case 3.1: `mem2reg` Stack-Slot-to-Block-Argument SSA Promotion (`MemToAnSSA`)

- **Real-World Tools Analyzed:**
  1. **`Vellvm vmem2reg` (`vellvm/vellvm`):** Zhao, Nagarakatte, Martin, and
     Zdancewic (PLDI 2013, DOI `10.1145/2491956.2462164`) formalized and proved
     LLVM's `PromoteMemToReg` in Coq. To achieve fast compilation without
     verifying Cytron et al.'s iterated dominance frontier (`IDF`) algorithm,
     `vmem2reg` decomposes promotion into micro-steps (alloca elimination, dead
     load/store elimination, and $\phi$-node pruning) backed by lightweight
     witness checks.
  2. **`CompCertSSA` Validator:** Barthe, Demange, and Pichardie (ESOP 2012 /
     TOPLAS 2014, DOI `10.1145/2579080`) validate RTL-to-SSA conversion via a
     Coq-verified structural dominator and $\phi$-placement validator (`SSAvalid.v`).
  3. **Braun et al. Online SSA & Isabelle Mechanization:** Braun, Buchwald, Hack,
     Leißa, Mallon, and Zwinkau (CC 2013, DOI `10.1007/978-3-642-37051-9_6`)
     designed a backward-lookup online SSA construction algorithm (used by `firm`,
     Cranelift `cranelift-frontend`, and Go's SSA backend) that avoids computing
     the dominator tree or `IDF`, mechanized in Isabelle/HOL by Buchwald, Lohner,
     and Ullrich (CC 2016, DOI `10.1145/2892208.2892211`).
  4. **Production Unverified Passes:** `LLVM PromoteMemToReg`
     (`llvm/lib/Transforms/Utils/PromoteMemoryToRegister.cpp`) and `rustc` MIR
     `PromoteTemps` / `PromoteConsts` (`compiler/rustc_mir_transform/src/promote_consts.rs`).
- **Mapping onto Anneal's 4 `trusted/` Primitives (`MemToAnSSA`):**
  - **Languages and `BehaviorCodec`:** `Compiles L_MIR L_AnSSA mem2regCodec s t`
    where `L_MIR := EventualLang MirMachine` and `L_AnSSA := EventualLang AnSSAMachine`.
    `mem2regCodec.encodeQuery` strips the frame-local stack allocations for the
    promoted local set $P \subseteq \text{Locals}$ (requiring `¬AddressTaken s l`
    for all $l \in P$), and `decodeOut` is the identity on caller-visible return
    values and heap state.
  - **`EventualBehaviorOf` Step Elasticity:** Absorbs $1 \to 0$ deletion of
    `StorageLive(l)`, `StorageDead(l)`, and stack load/store instructions as well
    as atomic block-argument binding on `Goto(bb, args)`.
  - **`StepResult.externalCall` & `VerificationResult`:** Forbids promoting any
    local whose address could reach `StepResult.externalCall`, and audits the
    anti-degeneracy normal form `MemoryLoadStoreCount t P = 0` in
    `VerificationResult`.
- **Mechanized Stress Test (`mem2reg_uninit_refines` and `mem2reg_uninit_not_symmetric`):**
  In [MidLevelOptimizationAndLoweringProbes.lean](support/MidLevelOptimizationAndLoweringProbes.lean)
  (lines 167–218), reading an uninitialized stack slot in `L_MIR` triggers UB
  (`Partial.ub`), whereas promoting that local to an `AnSSA` block parameter
  initialized to default/frozen `0` along the uninitialized edge is defined
  (`Partial.pure`). Under `Compiles`, `mem2reg_uninit_refines` holds
  constructively because `Partial.ub` is $\top$, whereas the reverse refinement
  `mem2reg_uninit_not_symmetric` is refuted.

#### 2.2 Use Case 3.2: Scalar Replacement of Aggregates (`SROA` / `SROACertifier`)

- **Real-World Tools Analyzed:**
  1. **`rustc` MIR `SROA` (`compiler/rustc_mir_transform/src/sroa.rs`):**
     Flattens non-escaping `struct` and tuple locals into separate scalar MIR
     locals for each field (`PlaceElem::Field(idx, ty)`), eliminating composite
     locals whenever no raw pointer, slice projection, or multi-variant enum
     downcast prevents decomposition.
  2. **`LLVM SROA` (`llvm/lib/Transforms/Scalar/SROA.cpp`):** Rewrites `alloca`
     byte slices accessed via `getelementptr`, `load`, `store`, and `memcpy` into
     disjoint scalar partitions (inserting bitcasts or integer bit-field
     extractions when loads/stores overlap partially) before invoking
     `PromoteMemToReg`.
  3. **`MLIR SROA` (`mlir/lib/Transforms/SROA.cpp`):** Generalizes `SROA` across
     arbitrary MLIR dialects via `DestructurableAllocationOpInterface` and
     `DestructurableTypeInterface` (`MemorySlotInterface.td`).
  4. **`CompCert SimplLocals` (`cfrontend/SimplLocalsproof.v`):** Lifts
     non-address-taken `Clight` local variables from the in-memory frame block
     into abstract temporary registers (`temp_env`) using a memory injection
     $\delta$ that maps remaining stack blocks while hiding lifted variables.
- **Mapping onto Anneal's 4 `trusted/` Primitives (`SROACertifier`):**
  - **Languages and `BehaviorCodec`:** `Compiles L_MIR L_MIR sroaCodec s t`
    backed by a layout-tree partition witness `cert : SROACert`.
  - **`EventualBehaviorOf` Step Elasticity:** Absorbs $1 \to m$ expansion of a
    whole-struct assignment `*dst = *src` into $m$ leaf-field assignments and
    $1 \to 0$ deletion of dead unread fields.
  - **Padding-Byte and Variant-Overlap Insight:** In Rust, a whole-struct copy
    at the byte level copies uninitialized padding bytes (`AbstractByte.Uninit`),
    whereas field-wise `SROA` copies only typed fields. If `s` later inspects
    struct bytes via `*const u8` or passes the struct's raw pointer to
    `StepResult.externalCall`, `SROA` is unsound. `SROACertifier` therefore
    checks in `VerificationResult` that every access to $a \in A_{\text{target}}$
    factors strictly through typed `PlaceElem::Field` projections with disjoint
    byte ranges and that `AggregateEliminated t A_target` holds.

#### 2.3 Use Case 3.3: SSA Destruction, Block-Argument Coalescing, and Parallel-Move Sequentialization (`SSADestructCertifier`)

- **Real-World Tools Analyzed:**
  1. **Rideau, Serpette, and Leroy Windmill Algorithm (`Coq`):** "Tilting at
     Windmills with Coq: Formal Verification of a Compilation Algorithm for
     Parallel Moves" (JAR 2008, DOI `10.1007/s10817-007-9096-8`) mechanized that
     any parallel register transfer graph decomposes into a tree/forest of reads
     (leaves first) plus disjoint cycles ("blades of the windmill") broken by a
     single temporary register `tmp` or `xchg`.
  2. **`CompCertSSA` CSSA Out-of-SSA (`Midend/CSSA.v`, `CSSAproof.v`):** Demange,
     Pichardie, and Stefanesco (CC 2015, DOI `10.1007/978-3-662-46663-6_5`)
     verified SSA destruction via Conventional SSA (`CSSA`) intermediate form,
     where $\phi$-web resources are isolated by parallel copy blocks before
     coalescing non-interfering webs.
  3. **Boissinot et al. Out-of-SSA (CGO 2009, DOI `10.1109/CGO.2009.19`):**
     Demonstrated that classic Sreedhar and Briggs out-of-SSA algorithms suffer
     from the **Lost-Copy Problem** and **Swap Problem** on critical edges and
     backedges (`Goto(hdr, [b, a])` into `(a, b)`), solving it via CSSA isolation
     followed by dominance-forest $O(1)$ interference tests and parallel-copy
     sequentialization.
- **Mapping onto Anneal's 4 `trusted/` Primitives (`SSADestructCertifier`):**
  - **Languages and `BehaviorCodec`:** `Compiles L_AnSSA L_MIR ssaDestructCodec s t`
    where `L_AnSSA` executes parallel block-argument assignments atomically on
    `Goto(bb, [e₁, ..., e_k])` and `L_MIR` executes sequential `Assign(l_i, r_i)`
    statements.
  - **`EventualBehaviorOf` Step Elasticity:** Directly exercises $1 \to k+1$
    silent step dilation on every CFG edge transition.
  - **`VerificationResult` Anti-Degeneracy:** Checks both symbolic state
    equivalence of the sequentialized move list against simultaneous parallel
    substitution (`checkParallelMoveSeq`) and the syntactic normal form
    `ZeroBlockParams t = true`.

#### 2.4 Use Case 3.4: Critical-Edge Splitting and CFG Normalization (`CFGNormValidator`)

- **Real-World Tools Analyzed:**
  1. **`LLVM BreakCriticalEdges` (`llvm/lib/Transforms/Utils/BreakCriticalEdges.cpp`):**
     Splits edges $(u \to v)$ where $\text{outdeg}(u) > 1$ and
     $\text{indeg}(v) > 1$ to provide safe placement blocks for `PRE`, `LICM`,
     and out-of-SSA copies.
  2. **`LLVM LoopSimplify` (`llvm/lib/Transforms/Utils/LoopSimplify.cpp`):**
     Canonicalizes natural loops to have a single dedicated preheader, a single
     backedge latch, and dedicated loop-exit blocks dominated by the loop header.
  3. **`LLVM LCSSA` (`llvm/lib/Transforms/Utils/LCSSA.cpp`):** Inserts
     single-operand $\phi$-nodes (or 1-argument block parameters) at loop exits
     for every value defined inside a loop and used outside it, isolating inner
     loop mutations (`ScalarEvolution`, `LoopUnroll`, `LICM`) from outer users.
- **Mapping onto Anneal's 4 `trusted/` Primitives (`CFGNormValidator`):**
  - **Languages and `BehaviorCodec`:** `Compiles L_AnSSA L_AnSSA idCodec s t`.
  - **`EventualBehaviorOf` Step Elasticity:** Splitting a critical edge or
    routing through an `LCSSA` exit block adds $+1$ silent `Goto` step. Even
    when a loop backedge latch is split inside an infinite loop,
    `EventualBehaviorOf` preserves `.diverges` (`∀ n, ∃ s', StepsN M n s (.running s')`)
    because adding $1$ step per iteration preserves infinite productivity.
  - **Unwind Edge Subtlety:** In Rust MIR (`Call` and `Assert` terminators),
    splitting a critical `unwind` cleanup edge requires `MirMachine` to carry
    the in-flight panic payload explicitly in machine `State` so the newly
    inserted landing block forwards unwinding state and preserves drop-flag
    liveness invariants, audited alongside `NoCriticalEdges t && HasCanonicalLoops t && IsLCSSA t`
    in `VerificationResult`.

---

### 3. Category B: Value Numbering, Redundancy, and Dead-Code Passes (Use Cases 3.5–3.9)

```
Basis: source + execution + derived
```

#### 3.1 Use Case 3.5: Global Value Numbering (`GVN` / `GVNCertifier`)

- **Real-World Tools Analyzed:**
  1. **Tristan and Leroy Verified GVN Validator:** "Verified Validation of Lazy
     Code Motion" (PLDI 2009, DOI `10.1145/1542476.1542512`) and "Formal
     Verification of Translation Validators" (POPL 2008 / JACM 2010, DOI
     `10.1145/1328438.1328485`) verify value numbering in Coq via symbolic
     evaluation of basic blocks and dominator-tree equality propagation.
  2. **`Chamois-CompCert CSE2` and `BTL` Value Numbering:** Monniaux and Boulmé
     (ESOP 2022) and Gourdin et al. (OOPSLA 2023, DOI `10.1145/3622840`) use
     hash-consed symbolic execution DAGs over extended basic blocks with
     non-trapping condition guards (`Ok`).
  3. **`CompCert ValueAnalysis.v` and `CSE.v` (`backend/CSEproof.v`):**
     Soundness-proved abstract value numbering and common subexpression
     elimination over CompCert `RTL`, tracking abstract pointer provenance and
     memory alias domains (`ValueDomain.v`).
  4. **Production Passes:** `rustc` MIR `GVN`
     (`compiler/rustc_mir_transform/src/gvn.rs`), `LLVM GVN`
     (`llvm/lib/Transforms/Scalar/GVN.cpp`), and `LLVM NewGVN` (`NewGVN.cpp`,
     Implementing optimistic congruence closure over SSA value graphs).
- **Mapping onto Anneal's 4 `trusted/` Primitives (`GVNCertifier`):**
  - **Languages and `BehaviorCodec`:** `Compiles L_AnSSA L_AnSSA idCodec s t`
    validated via a dominator-scoped congruence witness `cert : GVNCert`.
  - **`EventualBehaviorOf` Step Elasticity:** Absorbs $1 \to 0$ deletion of
    redundant instructions replaced by dominating SSA value identifiers `v_dom`.
  - **`StepResult.externalCall` and IEEE-754 Bit-Exactness:** `externalCall`
    kills all non-protected memory value numbers. In `GVNCertifier`, algebraic
    identities must hold under `Trusted/MirSemantics.lean`'s bit-exact semantics:
    for example, IEEE-754 floating-point `x + 0.0` is **not** congruent to `x`
    when `x = -0.0` (`-0.0 + +0.0 = +0.0`, which alters sign-bit inspection via
    `f64::to_bits`), and `CheckedAdd(a, b)` is only congruent to `WrappingAdd(a, b)`
    along paths dominated by the non-overflow assertion.

#### 3.2 Use Case 3.6: Partial Redundancy Elimination (`PRE` / `PREValidator`)

- **Real-World Tools Analyzed:**
  1. **Knoop, Rüthing, and Steffen Lazy Code Motion (`LCM`):** "Lazy Code Motion"
     (PLDI 1992, DOI `10.1145/143095.143136`) formulated `PRE` via four
     bidirectional bitvector dataflow equations (`DownSafe` / anticipability,
     `Earliest`, `Later`, and `Insert`/`Delete`) that achieve both computational
     optimality and minimum register lifetimes.
  2. **Tristan and Leroy LCM Validator (`PLDI 2009`):** Proved in Coq that
     instead of verifying the four-pass bitvector fixpoint solver, a translation
     validator only needs to check two post-facto equations (`Anticipated` and
     `Available`) on the transformed graph to guarantee semantic preservation.
  3. **`Chamois-CompCert BTL_LCM`:** Integrates lazy code motion into `BTL`
     block simulation, using auxiliary ghost registers and symbolic invariants
     at block boundaries.
- **Mapping onto Anneal's 4 `trusted/` Primitives (`PREValidator`):**
  - **Languages and `BehaviorCodec`:** `Compiles L_AnSSA L_AnSSA idCodec s t`.
  - **`EventualBehaviorOf` Step Elasticity:** Shifts evaluations earlier onto
    split incoming edges ($0 \to 1$ earlier, $1 \to 0$ at the original site, net
    $2 \to 1$ along redundant paths) while preserving `EventualOut Obs Val`.
  - **Down-Safety and Trapping Operations Across `StepResult.externalCall`:**
    Because `PRE` inserts an expression `e` onto an edge where `e` did not
    previously execute at that program point, inserting a potentially panicking
    or trapping operation (`a / b` or an unvalidated load `*p`) above an
    `externalCall` or a potentially diverging loop violates `Compiles` unless
    `e` is proven non-trapping (`IsSafeToSpeculate e`) or `e` is strictly
    anticipated prior to any `Obs`-emitting call or backedge.

#### 3.3 Use Case 3.7: Sparse Conditional Constant Propagation (`SCCP` / `SCCPValidator`)

- **Real-World Tools Analyzed:**
  1. **Wegman and Zadeck `SCCP`:** "Constant Propagation with Conditional
     Branches" (TOPLAS 1991, DOI `10.1145/103135.103136`) jointly propagates
     values over the 3-point flat lattice ($\top \sqsupset c \sqsupset \bot$,
     where $\top$ is uninitialized/optimistic and $\bot$ is overdefined) and
     reachability over CFG edges, discovering constants inside loops and pruning
     unreachable subgraphs that neither constant propagation nor dead-branch
     elimination can find alone.
  2. **`CompCertSSA SCCP` (`Midend/SCCP.v`, `SCCPproof.v`) & `CompCert Constprop.v`:**
     Mechanized optimistic sparse constant propagation in Coq by validating the
     post-fixpoint of `(valMap, execEdges)` before rewriting instructions and
     folding conditional branches.
  3. **Production Passes:** `LLVM SCCP` and interprocedural `IPSCCP`
     (`llvm/lib/Transforms/Scalar/SCCP.cpp`), and `rustc` MIR
     `DataflowConstProp` (`compiler/rustc_mir_transform/src/dataflow_const_prop.rs`).
- **Mapping onto Anneal's 4 `trusted/` Primitives (`SCCPValidator`):**
  - **Languages and `BehaviorCodec`:** `Compiles L_MIR L_MIR idCodec s t` paired
    with `checkSCCPFixedPoint s valMap execEdges = true` and anti-degeneracy
    obligation `BranchCount t < BranchCount s ∨ ConstFoldedCount t > 0` in
    `VerificationResult`.
  - **`StepResult.externalCall` Role:** Models the return value of any
    unverified `externalCall` as $\bot$ (overdefined).
  - **Resolving the `undef` Branching Paradox:** In LLVM, if an executable edge
    carries `undef` and merges with constant $c$ at $\phi(\text{undef}, c)$,
    folding $\phi$ to $c$ without freezing `undef` is unsound if `undef` was
    also used prior to the $\phi$ or if two downstream uses pick different values.
    In Anneal, reading uninitialized memory in `L_MIR` is `Partial.ub`, and any
    nondeterministic choice via `StepResult.choice` commits to a concrete state
    `s'` at the step point (`ReachesPrefix.choice`, `Trusted/StepResult.lean`
    lines 148–153), structurally preventing inconsistent multi-use folding.

#### 3.4 Use Case 3.8: Dead Code Elimination (`DCE`) and Dead Store Elimination (`DSE` / `DCEDSEValidator`)

- **Real-World Tools Analyzed:**
  1. **Benton's Relational Hoare Logic (`RHL`):** "Simple Relational Correctness
     Proofs for Static Analyses and Program Transformations" (POPL 2004, DOI
     `10.1145/964001.964003`) formalized backward dependency/liveness analysis
     and proved `DCE` sound as a relational judgment $\vdash C_1 \sim C_2 :
     \Phi \Rightarrow \Psi$ over partial equivalence relations (`PER`s) that
     demand equality only on live variables.
  2. **`CompCert Deadcode.v` and `NeedDomain.v` (`backend/Deadcodeproof.v`):**
     Combines backward bitwise liveness ("neededness" masks tracking which bits
     of a register are observed downstream) with memory alias domains to
     eliminate dead instructions, masked high bits, and overwritten stack stores.
  3. **Production Passes:** `rustc` MIR `DeadStoreElimination`
     (`compiler/rustc_mir_transform/src/dead_store_elimination.rs`), `LLVM ADCE`
     (`AggressiveDCE.cpp`), `BDCE` (`BitTrackingDCE.cpp`), and `DSE`
     (`DeadStoreElimination.cpp`).
- **Mapping onto Anneal's 4 `trusted/` Primitives (`DCEDSEValidator`):**
  - **Languages and `BehaviorCodec`:** `Compiles L_MIR L_MIR idCodec s t` backed
    by a backward variable/memory liveness certificate `cert : LivenessCert`.
  - **`EventualBehaviorOf` Step Elasticity:** Absorbs $1 \to 0$ deletion of dead
    assignments and overwritten stores while forbidding deletion of infinite
    loops (`Div ↔ Div`).
- **Mechanized Stress Test (`dce_panicking_div_unsound` vs. `dce_guarded_div_compiles`):**
  In [MidLevelOptimizationAndLoweringProbes.lean](support/MidLevelOptimizationAndLoweringProbes.lean)
  (lines 220–279), Rust MIR operations that can panic (`x / d` when `d = 0`,
  checked arithmetic, slice bounds checks) produce `.terminated [] .unwind`—a
  **defined** outcome with a distinct observable spine (`SemObs`) from
  `.terminated [] (.normal x)`. Therefore, `dce_panicking_div_unsound` proves
  that deleting an unused `let _ = x / d` without proving `d ≠ 0` violates
  `Compiles`! Conversely, once a dominating `CVP` guard restricts the path to
  `d ≠ 0`, `dce_guarded_div_compiles` verifies that deleting the dead division
  satisfies `Compiles`. Similarly, `DSE` cannot eliminate a store `*p = 1`
  before a potentially panicking call if an `unwind` landing pad or `Drop`
  handler reads `*p`.

#### 3.5 Use Case 3.9: Dominance-Based Correlated Value Propagation (`CVP`) and Range-Check Elimination (`CVPRangeEliminator`)

- **Real-World Tools Analyzed:**
  1. **Bodík, Gupta, and Sarkar `ABCD` & GraalVM `ABCD`:** "ABCD: Eliminating
     Array Bounds Checks on Demand" (PLDI 2000, DOI `10.1145/349299.349342`)
     builds an Extended SSA (`e-SSA`) inequality distance graph (splitting
     variables at conditional branches `if i < n`) and decides bounds checks
     $0 \le i < \text{len}$ via shortest-path difference constraints in $O(V)$
     per query, used in HotSpot/GraalVM JIT compilation.
  2. **`LLVM CorrelatedValuePropagation` (`CVP`) and `LazyValueInfo` (`LVI`):**
     Propagates constant-range intervals (`ConstantRange`, 2's-complement modular
     wrapping intervals) down the dominator tree to fold comparisons, narrow
     `sdiv`/`udiv` widths, and remove redundant `llvm.assume` / trap guards.
  3. **`LLVM InductiveRangeCheckElimination` (`IRCE`):** Splits a loop with
     bounds check $0 \le i + c < L$ into a pre-loop, a bounds-check-free main
     loop over the safe intersection $[\max(0, -c), \min(N, L - c))$, and a
     post-loop.
- **Mapping onto Anneal's 4 `trusted/` Primitives (`CVPRangeEliminator`):**
  - **Languages and `BehaviorCodec`:** `Compiles L_MIR L_MIR idCodec s t`,
    replacing `Assert(cond, msg, target, cleanup)` terminators with unconditional
    `Goto(target)` when dominated by path conditions implying `cond`.
  - **2's-Complement Bitvector Wrap-Around:** In Rust, `i + 1 < len` over
    `usize` does **not** imply `i < len` when `i == usize::MAX` and wrapping
    addition occurs. `CVPRangeEliminator` therefore checks all range-check
    certificates over fixed-width bitvectors (`BitVec 64` / `BitVec 32`) via
    `bv_decide` / `LRAT` in `VerificationResult` (`AssertCount t < AssertCount s`).

---

### 4. Category C: Alias- and Borrow-Aware Memory Optimizations (Use Cases 3.10–3.12)

```
Basis: normative + source + execution + derived
```

#### 4.1 Use Case 3.10: Unique-`&mut` and Shared-`&` Load Hoisting, Redundant Load Elimination, and Store-to-Load Forwarding (`BorrowMemoryOpt`)

- **Real-World Tools Analyzed:**
  1. **`Stacked Borrows` (`POPL 2020`, DOI `10.1145/3371109`):** Jung, Dang,
     Kang, and Dreyer defined the first operational aliasing model for Rust,
     maintaining a per-byte borrow stack of tags (`Unique`, `SharedReadOnly`,
     `SharedReadWrite`, `Disabled`) and proving load hoisting and store
     forwarding in Coq via `Iris`.
  2. **`Tree Borrows` (`PLDI 2025`, DOI `10.1145/3729269`):** Villani, Hostert,
     Dreyer, and Jung replaced the linear borrow stack with a **tree state
     machine** (`Reserved` with lazy two-phase activation, `Active`, `Frozen`,
     `Disabled`), rejecting 54% fewer real-world crates in `Miri` while proving
     in Rocq (`SimulIris`) that read-read reorderings, redundant load
     elimination, and store forwarding remain sound.
  3. **`Miri` (`rust-lang/miri`):** Reference operational interpreter for Rust
     MIR executing both Stacked Borrows (`src/borrow_tracker/stacked_borrows/`)
     and Tree Borrows (`src/borrow_tracker/tree_borrows/`).
  4. **`SimulIris` (`POPL 2022`, DOI `10.1145/3498687`):** Gäher, Sammler,
     Spies, Jung, Dang, Krebbers, Jee, and Dreyer built a separation-logic
     simulation framework in Coq for proving contextual refinement of local
     optimizations in the presence of Undefined Behavior.
- **Mapping onto Anneal's 4 `trusted/` Primitives (`BorrowMemoryOpt`):**
  - **Languages and `BehaviorCodec`:** `Compiles L_MIR L_MIR idCodec s t` over
    tag-equipped `MirMachine`, paired with `DerefLoadCount t < DerefLoadCount s`.
  - **Why Directional Refinement (`≤`) Validates Read Elimination in Tree Borrows:**
    Suppose `s` executes `let x = *r; *raw_ptr = 42; let y = *r;` where
    `r : &i32` (`Freeze`). Under Tree Borrows, if `raw_ptr` aliases `r`, the
    write `*raw_ptr = 42` sets $\tau_r$ to `Disabled` so the second read
    `let y = *r` triggers `Partial.ub`. Whenever `s` is defined, `raw_ptr` did
    not mutate `*r`, so `y == x`. Moreover, deleting the second read `let y = *r`
    (replacing it with `let y = x`) means `t` performs *fewer* reads: in Tree
    Borrows, reads only weaken permissions of conflicting sibling/cousin tags
    (`Active → Frozen`), never strengthening them. Thus deleting a read can only
    make `t` *more defined* than `s` (`L₂.sem t ≤ L₁.sem s`), which is mechanized
    in `inline_drops_protector_refines`
    ([MidLevelOptimizationAndLoweringProbes.lean](support/MidLevelOptimizationAndLoweringProbes.lean),
    lines 281–327).

#### 4.2 Use Case 3.11: `noalias` and Tree-Borrows Protector-Guided Reordering Across Opaque External Calls (`ExternalCallMotionValidator`)

- **Real-World Tools Analyzed:**
  1. **Tree Borrows and Stacked Borrows Function-Entry `Protector`s (`POPL 2020`, `POPL 2022`, `PLDI 2025`):**
     When a function `fn foo(x: &mut i32)` is entered, a fresh call-frame ID $c$
     is added to the `Protector` set and attached to `x`'s borrow tag $\tau_x$
     for the entire lifetime of the call `foo`. Any foreign access that would
     force a protected tag $\tau_x$ into `Disabled` (or violate `Frozen` for
     `&T` where `T : Freeze`) triggers immediate Undefined Behavior.
  2. **LLVM `noalias` and `scoped_noalias` Metadata (`ScopedNoAliasAA`):**
     Emitted by `rustc` (`-Zmutable-noalias=yes`) for all `&mut T` and `&T`
     (`Freeze`) reference parameters to enable LLVM `LICM`, `GVN`, and `DSE`
     across opaque function calls.
- **Mapping onto Anneal's 4 `trusted/` Primitives (`ExternalCallMotionValidator`):**
  - **Direct Exercising of `StepResult.externalCall`:** In `MirMachine`, calling
    an opaque external function executes:
    ```lean
    StepResult.externalCall (boundaryInv : Bool) (branches : State → Prop)
    ```
    where `branches` ranges over all post-call states that preserve caller-local
    registers and preserve memory locations guarded by active caller
    Function-Entry `Protector`s not passed to the external call.
- **Mechanized Stress Test (`dse_across_diverging_external_call_unsound_if_late_protector`):**
  In [MidLevelOptimizationAndLoweringProbes.lean](support/MidLevelOptimizationAndLoweringProbes.lean)
  (lines 329–366), consider:
  ```rust
  pub fn foo(x: &mut i32) {
      *x = 1;
      opaque_ext_call(); // May diverge or exit early after reading a global raw ptr!
      *x = 2;
  }
  ```
  If a `Protector` only checked at `foo`'s return whether $\tau_x$ was disabled,
  then when `opaque_ext_call()` reads a stashed raw pointer to `x`, prints `1`,
  and diverges or halts, `s` would be defined and emit `1`, whereas `t` (after
  eliminating `*x = 1`) would emit the prior value `0`! Theorem
  `dse_across_diverging_external_call_unsound_if_late_protector` proves that
  `DSE` across a potentially diverging `externalCall` is sound **if and only if**
  `StepResult.externalCall`'s `branches` contract (and Tree Borrows protectors,
  coupled with an initial virtual access on function entry) forbids foreign
  reads of caller-protected `&mut T` **at the moment of the foreign access**,
  making the conflicting path in `opaque_ext_call()` immediately `Partial.ub`.

#### 4.3 Use Case 3.12: Escape Analysis and Heap-to-Stack (`Box::new` → Stack Local) Promotion (`HeapToStackPromoter`)

- **Real-World Tools Analyzed:**
  1. **`LLVM Attributor AAHeapToStack` (`llvm/lib/Transforms/IPO/AttributorAttributes.cpp`):**
     Interprocedural fixpoint analysis that replaces `malloc`/`calloc` + `free`
     (or Rust `__rust_alloc` + `__rust_dealloc`) with `alloca` when the pointer
     does not escape the frame (`nocapture`) and its allocation size is bounded.
  2. **GraalVM Partial Escape Analysis (`PEA`, Stadler, Würthinger, Mössenböck, CGO 2014, DOI `10.1145/2544137.2544157`):**
     Flow-sensitively virtualizes heap allocations into register-level
     `VirtualObjectNode` representations along non-escaping control-flow paths
     and materializes heap allocations lazily only on cold escaping branches.
  3. **Go Compiler Escape Analysis (`cmd/compile/internal/escape`):**
     Dataflow-graph points-to escape analyzer deciding stack vs. GC heap
     placement for all variable declarations and `new()` / composite literals.
  4. **Twin-Allocation and Quasi-Concrete Memory Models (`Kang et al. PLDI 2015`, DOI `10.1145/2737924.2738005`; `Lee et al. PLDI 2017`, DOI `10.1145/3062341.3062343`):**
     Demonstrated that if an allocator returns concrete integer addresses, casting
     a pointer to `usize` (`expose_provenance`) can observe whether an object was
     placed on the heap vs. stack or whether OOM occurred.
- **Mapping onto Anneal's 4 `trusted/` Primitives (`HeapToStackPromoter`):**
  - **Languages and `BehaviorCodec`:** `Compiles L_MIR L_MIR heapToStackCodec s t`
    where `heapToStackCodec` relates the heap `AllocId` in `s` to the frame-local
    stack `Local` in `t` via a private allocation-relocation bijection that
    vanishes upon function return (`decodeOut = some`).
  - **OOM Refinement and Provenance Exposure:** Under `Compiles`, replacing a
    heap allocation that may fail with OOM in `s` with an infallible stack
    `StorageLive` in `t` is a valid refinement (`L₂.sem t ≤ L₁.sem s`) **provided**
    `L_MIR` models heap allocation as a demonic choice (`StepResult.choice`)
    between `{alloc_ok, alloc_oom}` and `cert : NonEscapeCert` proves
    `¬AddressExposed s alloc_id` (`HeapAllocCount t < HeapAllocCount s`).

---

### 5. Category D: Loop Transformations and Vectorization (Use Cases 3.13–3.16)

```
Basis: source + execution + derived
```

#### 5.1 Use Case 3.13: Loop-Invariant Code Motion (`LICM` / `LICMValidator`) with Trapping-Operation Safety Guards

- **Real-World Tools Analyzed:**
  1. **Tristan and Leroy Verified `LICM` (`POPL 2008` / `JACM 2010`):**
     Validated loop-invariant code motion in Coq by decomposing the transformation
     into trace-preserving block moves guarded by dominance and non-trapping
     side conditions.
  2. **`Chamois-CompCert` `BTL` `LICM` and Loop Hoisting (`OOPSLA 2023`):**
     Verifies invariant hoisting into loop preheaders using `BTL` block
     simulations annotated with symbolic loop invariants and explicit `Ok`
     non-trapping guards.
  3. **`Crellvm` `LICM` (`PLDI 2018`) & `LLVM LICM` (`llvm/lib/Transforms/Scalar/LICM.cpp`):**
     Uses `AliasSetTracker` / `MemorySSA` to hoist loop-invariant loads and
     expressions into the loop preheader and sink loop-invariant stores to
     dedicated loop exit blocks (`isSafeToExecuteUnconditionally`).
- **Mapping onto Anneal's 4 `trusted/` Primitives (`LICMValidator`):**
  - **Languages and `BehaviorCodec`:** `Compiles L_AnSSA L_AnSSA idCodec s t`.
  - **`EventualBehaviorOf` Step Elasticity:** Hoisting an instruction out of an
    $N$-trip loop compresses $N$ in-loop steps into $1$ preheader step ($N \to 1$
    for $N \ge 1$, or $0 \to 1$ for $N = 0$), which `EventualBehaviorOf` absorbs
    transparently.
- **Mechanized Stress Test (`licm_trapping_zero_trip_unsound`):**
  In [MidLevelOptimizationAndLoweringProbes.lean](support/MidLevelOptimizationAndLoweringProbes.lean)
  (lines 368–405), hoisting a loop-invariant division `100 / d` into the loop
  preheader when `tripCount = 0` and `d = 0` transforms a normally returning
  0-trip execution (`.terminated [] (.normal 0)`) into an immediate preheader
  panic (`.terminated [] .unwind`), refuting `Compiles`
  (`licm_trapping_zero_trip_unsound`). Consequently, `LICMValidator` requires
  `cert : LICMCert` in `VerificationResult` to prove either
  `IsSafeToSpeculate inst` (total, non-panicking, UB-free) or that `TripCount ≥ 1`
  and `inst` dominates all loop exits, `StepResult.externalCall` sites, and
  diverging backedges.

#### 5.2 Use Case 3.14: Loop Unrolling, Peeling, and Unswitching (`LoopStructureOpt`)

- **Real-World Tools Analyzed:**
  1. **`LLVM SimpleLoopUnswitch` and the `freeze` Instruction (`Lee et al. PLDI 2017`, DOI `10.1145/3062341.3062343`):**
     Hoists a loop-invariant conditional `if (inv_cond)` outside loop $L$ by
     duplicating $L$ into `L_true` and `L_false`. Historically, unswitching an
     uninitialized or `poison`/`undef` condition `inv_cond` in LLVM when the
     loop executed $0$ iterations introduced branching on `undef`/`poison` (a
     famous source of LLVM miscompilations when combined with `GVN` and `mem2reg`),
     requiring `SimpleLoopUnswitch` to insert `freeze(inv_cond)` or place the
     unswitched branch inside a zero-trip guard.
  2. **`LLVM LoopUnroll` and `LoopPeel` (`llvm/lib/Transforms/Utils/LoopUnroll.cpp`, `LoopPeel.cpp`):**
     Peels the first $p$ iterations (to resolve initial $\phi$ constants) and
     replicates the loop body $k$ times per backedge with an epilogue remainder
     loop.
- **Mapping onto Anneal's 4 `trusted/` Primitives (`LoopStructureOpt`):**
  - **Languages and `BehaviorCodec`:** `Compiles L_AnSSA L_AnSSA idCodec s t`.
  - **`EventualBehaviorOf` Step Elasticity:** $k$-way loop unrolling eliminates
    $k - 1$ backedge branch steps every $k$ iterations ($k \cdot m \to k \cdot m
    - (k - 1)$ steps). Because `EventualBehaviorOf` universally quantifies step
    counts in `.diverges` (`∀ n, ∃ s', StepsN M n s (.running s')`), an unrolled
    infinite loop in `t` matches `.diverges` in `s` without any clock-rescaling
    parameter in the external theorem.
  - **`VerificationResult` Guard:** Requires loop unswitching either to occur
    downstream of the zero-trip loop entry guard or to prove `inv_cond` is
    initialized and non-trapping at the preheader.

#### 5.3 Use Case 3.15: Loop Fusion, Fission, and Polyhedral Affine Schedule Validation (`PolyhedralScheduleValidator`)

- **Real-World Tools Analyzed:**
  1. **`PolyVerify` (`Courant & Leroy, POPL 2021`, DOI `10.1145/3434321`):**
     "Verified Code Generation for the Polyhedral Model" mechanized a Coq
     translation validator for polyhedral loop nest transformations (loop fusion,
     fission/distribution, interchange, skewing, strip-mining, and tiling). An
     untrusted polyhedral code generator (`CLOOG`/`ISL`) produces the target loop
     nest and a polyhedral witness; `PolyVerify` checks in Coq via verified
     linear programming / Farkas certificates that the schedule map is bijective
     on the iteration domain $\mathcal{D}$ and strictly respects all RAW, WAR,
     and WAW data dependences.
  2. **`Pluto` (`bondhugula/pluto`, Bondhugula et al., PLDI 2008, DOI `10.1145/1375581.1375595`):**
     Automatic polyhedral parallelizer and locality optimizer using the Farkas
     Lemma to formulate tileable affine hyperplanes $\theta(\vec{i})$ as an
     Integer Linear Program (`ILP`).
  3. **`ISL` (Verdoolaege, ICMS 2010), `LLVM Polly` (Grosser et al., IMPACT 2012), and `Polygeist` (Moses et al., PACT 2021):**
     Presburger integer set library (`ISL`) and LLVM/MLIR `affine` dialect
     frontends for Static Control Parts (`SCoP`s).
- **Mapping onto Anneal's 4 `trusted/` Primitives (`PolyhedralScheduleValidator`):**
  - **Languages and `BehaviorCodec`:** `Compiles L_MIR L_MIR idCodec s t` backed
    by `cert : PolyhedralCert` (containing iteration polyhedra $\mathcal{D}$,
    affine schedules $\theta_s, \theta_t$, dependence polyhedra
    $\mathcal{R}_{\text{dep}}$, and non-negative Farkas multipliers checked in
    Lean's kernel).
  - **`EventualBehaviorOf` Step Elasticity:** Reordering iterations permutes
    internal silent array loads and stores and fuses/splits loop control steps;
    `EventualBehaviorOf` relates the complete SCoP entry-to-exit transition in
    `s` and `t`.
  - **In-Loop Rust Bounds-Check Panic Ordering:** Unlike C (where out-of-bounds
    array accesses are UB), safe Rust slice accesses `a[i * stride + j]` execute
    `Assert` bounds checks that panic deterministically! If loop interchange or
    loop fission executes iteration $\vec{i}_2$ (or statement $S_1$ for all $N$
    iterations) before iteration $\vec{i}_1$ (or statement $S_2$ at iteration
    $0$) panics, `t` can panic with a different message or after mutating
    caller-visible state. `PolyhedralScheduleValidator` therefore requires
    `VerificationResult` to discharge affine bounds-check freedom across the
    entire domain $\mathcal{D}$ before permitting iteration reordering.

#### 5.4 Use Case 3.16: Induction-Variable Strength Reduction (`IVSR`) and Loop/SLP SIMD Auto-Vectorization (`SIMDAndIVValidator`)

- **Real-World Tools Analyzed:**
  1. **`Chamois-CompCert` Lazy Strength Reduction (`Gourdin et al., OOPSLA 2023`, DOI `10.1145/3622840`):**
     Verifies induction-variable strength reduction (`idx = base + i * stride`
     replaced by an additive recurrence `acc += stride`) inside `BTL` via
     relational loop-invariant register equations.
  2. **`HELIX` (`Zaliva & Franchetti, ITP 2018`):** Mechanized Spiral-style DSP
     loop and vector lowering in Coq targeting `Vellvm`/`VIR`.
  3. **`Alive2` SIMD/SLP Validation (`PLDI 2021`), `VeGen` (`Chen, Mendis, Amarasinghe, ASPLOS 2021`, DOI `10.1145/3445814.3446692`), and `Diospyros` (`VanHattum et al., ASPLOS 2021`, DOI `10.1145/3445814.3446707`):**
     Validate or synthesize Superword-Level Parallelism (`SLP`) and loop
     vectorization—with `Diospyros` using `egg` equality saturation to pack
     scalar loops into hardware vector lanes (`Simd<T, W>`).
- **Mapping onto Anneal's 4 `trusted/` Primitives (`SIMDAndIVValidator`):**
  - **Languages and `BehaviorCodec`:** `Compiles L_MIR L_MIR idCodec s t` where
    `EventualBehaviorOf` compresses $W$ scalar loop iterations into $1$ vector
    iteration ($W \to 1$ step compression).
  - **Modular Arithmetic vs. Checked Overflow and IEEE-754 Non-Associativity:**
    1. In `IVSR`, `(base + i * stride) + stride = base + (i + 1) * stride` holds
       unconditionally over modular `BitVec 64` **wrapping** arithmetic, but
       fails if `s` used `CheckedMul` unless no-overflow bounds are proven in
       `VerificationResult`.
    2. In SIMD floating-point horizontal reductions (`sum += a[i]`), lane-wise
       vector accumulation changes the addition association tree. Because
       IEEE-754 `f32`/`f64` addition is non-associative, `SIMDAndIVValidator`
       rejects reassociated FP reductions unless the source specification
       explicitly permits `reassoc` nondeterminism or `t` uses strict ordered
       reductions.

---

### 6. Category E: Interprocedural and Control-Flow Transformations (Use Cases 3.17–3.19)

```
Basis: source + execution + derived
```

#### 6.1 Use Case 3.17: Function Inlining and Devirtualization (`InlineAndDevirtValidator`)

- **Real-World Tools Analyzed:**
  1. **`CompCert Inliningproof.v` (`backend/Inlining.v`, `Inliningproof.v`):**
     Proves function inlining in Coq by splicing a renamed copy of the callee's
     `RTL` CFG into the caller's CFG, merging the callee's private stack block
     into a sub-region of the caller's stack block via a structured memory
     injection (`Mem.extends` / `Mem.inject`).
  2. **`CakeML bvl_inlineScript.sml` (`compiler/backend/bvl_inlineScript.sml`):**
     Verifies function inlining and dead-function elimination at the `bvl`
     (Bytecode-Value Language) middle-end layer using clock-indexed big-step
     simulation.
  3. **`SimulIris` Protector Removal During Inlining (`Gäher et al. POPL 2022`; `Villani et al. PLDI 2025`) & `rustc` `Inline` / `Devirt` (`compiler/rustc_mir_transform/src/inline.rs`):**
     Proved in Rocq that inlining a function in Stacked Borrows / Tree Borrows
     is a valid contextual refinement even though inlining deletes the callee's
     Function-Entry `Protector`.
- **Mapping onto Anneal's 4 `trusted/` Primitives (`InlineAndDevirtValidator`):**
  - **Languages and `BehaviorCodec`:** `Compiles L_MIR L_MIR idCodec s t`, where
    `EventualBehaviorOf` absorbs the $2 \to 0$ removal of administrative call and
    return transitions (`CallSiteCount t < CallSiteCount s`).
- **Mechanized Stress Test (`inline_drops_protector_refines` and `inline_protector_not_reversible`):**
  In [MidLevelOptimizationAndLoweringProbes.lean](support/MidLevelOptimizationAndLoweringProbes.lean)
  (lines 281–327), when `callee(x: &mut T)` is called in `s`, `x` carries a
  Function-Entry `Protector` for the duration of `callee`. When `callee` is
  inlined into `caller` in `t`, the call boundary—and thus `callee`'s
  protector—disappears, making `t` strictly *more defined* (less UB) than `s`.
  Theorem `inline_drops_protector_refines` proves that `Compiles` (`≤`) validates
  inlining unconditionally, whereas `inline_protector_not_reversible` proves that
  the inverse transformation (**outlining** code into a helper function with
  `&mut T` parameters) does **not** unconditionally satisfy `Compiles` because
  adding a new protector can introduce UB on aliased raw-pointer paths.

#### 6.2 Use Case 3.18: Monomorphization and Polymorphization (`MonoPolyValidator`)

- **Real-World Tools Analyzed:**
  1. **`rustc` Monomorphization Collector (`compiler/rustc_monomorphize/src/collector.rs`) and Polymorphization (`compiler/rustc_mir_transform/src/polymorphize.rs`, Wood, 2020):**
     `rustc_monomorphize` instantiates generic MIR bodies `f⟨T₁, ..., T_k⟩` at
     concrete types $\sigma = [T_i \mapsto \tau_i]$, while `polymorphize`
     analyzes whether type/const parameters are unused (or used only via
     identical-layout phantom markers) to share a single codegen instance across
     multiple monomorphizations.
  2. **`.NET CLR` Generic Sharing (`Kennedy & Syme, PLDI 2001`, DOI `10.1145/378795.378797`):**
     Shares a single native JIT body across all reference-type instantiations
     `List<string>`, `List<object>` (passing a hidden runtime dictionary pointer
     when type metadata is needed) while generating specialized bodies for
     distinct value types (`List<int>`, `List<double>`).
- **Mapping onto Anneal's 4 `trusted/` Primitives (`MonoPolyValidator`):**
  - **Non-Trivial `BehaviorCodec`:** `Compiles (L_PolyMIR σ) L_MIR layoutIsoCodec s t`
    where `layoutIsoCodec` applies the representation isomorphism
    $\phi : \text{Val}_{\tau_1} \cong \text{Val}_{\tau_{\text{canon}}}$ while
    preserving the type-erased observable spine `SemObs`.
  - **Layout, Alignment, ZST, and `UnsafeCell` Niche Audit:** Two types of the
    same byte size—such as `[u8; 4]` (align 1) vs. `u32` (align 4), ZST `()`
    (align 1) vs. `[u64; 0]` (align 8), or `&i32` (`Freeze`) vs.
    `&Cell<i32>` (non-`Freeze` `UnsafeCell`)—cannot be polymorphized into a
    shared body if that body performs alignment checks (`AlignCheck`), pointer
    stride offsets (`Offset`), or `Freeze`-dependent borrow transitions.
    `MonoPolyValidator` audits exact equality of `(size, align, abi, isFreeze)`
    in `VerificationResult`.

#### 6.3 Use Case 3.19: Tail-Call Optimization (`TCO`), Jump Threading, and Switch Lowering (`ControlAndTailLowering`)

- **Real-World Tools Analyzed:**
  1. **`CompCert Tailcallproof.v` (`backend/Tailcall.v`, `Tailcallproof.v`):**
     Replaces `call + return` sequences in `RTL` with `Itailcall` (deallocating
     the caller's stack block before transferring control to the callee), guarded
     by the crucial syntactic check `stacksize f == 0` so no pointer into the
     caller's stack frame can escape to the tail-called callee!
  2. **`CompCert Tunnelingproof.v` (`backend/Tunneling.v`) & `rustc` MIR `JumpThreading` (`compiler/rustc_mir_transform/src/jump_threading.rs`):**
     Collapse chains of empty basic blocks (`Lb1 → Lb2 → Lb3`, verified via an
     acyclic measure decreasing along branch chains) and thread known path
     constants through join blocks containing `SwitchInt`.
  3. **`CompCert Switch.v` (`backend/Switch.v`, `cfrontend/SimplExprproof.v`):**
     Lowers multi-way `switch` statements into balanced binary decision trees of
     comparisons and jump tables (`Ijtable`).
- **Mapping onto Anneal's 4 `trusted/` Primitives (`ControlAndTailLowering`):**
  - **Languages and `BehaviorCodec`:** `Compiles L_MIR L_MIR idCodec s t`.
  - **`EventualBehaviorOf` Step Elasticity:** Absorbs $k \to 1$ branch-chain
    tunneling/threading and $1 \to \lceil \log_2 n \rceil$ binary-search switch
    lowering.
  - **Stack-Escape Guard for `TCO` (`become`):** In Rust MIR, a tail call can
    only reuse/deallocate the caller's stack frame if every caller stack local is
    already `StorageDead`, has no pending `Drop` glue, and has no active borrow
    tag reachable from the callee's arguments in `StepResult.externalCall`,
    verified as an explicit obligation in `VerificationResult`.

---

### 7. Category F: High-Level Desugaring and State-Machine Lowering (Use Cases 3.20–3.22)

```
Basis: source + execution + derived
```

#### 7.1 Use Case 3.20: Async/Await and Coroutine/Generator State-Machine Lowering (`CoroutineLoweringValidator`)

- **Real-World Tools Analyzed:**
  1. **`rustc StateTransform` (`compiler/rustc_mir_transform/src/coroutine.rs`):**
     Lowers pre-transform coroutine/async MIR containing `TerminatorKind::Yield`
     suspension points into a synchronous state-machine enum `CoroutineState`
     (with discriminant `0 = Unresumed`, `1 = Returned`, `2 = Panicked`,
     `3..k = Suspended_i`) and generates `Future::poll(Pin<&mut Self>, &mut Context)`
     and `Drop::drop`. Uses bitset cross-yield liveness analysis to pack
     non-simultaneously-live locals into overlapping storage offsets.
  2. **`Pin<&mut Self>` in `RustBelt` (`Jung, Jourdan, Krebbers, Dreyer, POPL 2018`, DOI `10.1145/3158154`):**
     Semantic type soundness proof in Iris/Coq formalizing the `Pin<P>` contract:
     once a potentially self-referential state machine enters a pinned state, its
     backing memory must never be moved or deallocated without first running
     `Drop::drop` in place.
  3. **`LLVM CoroSplit` and `CoroElide` (`llvm/lib/Transforms/Coroutines/CoroSplit.cpp`, `CoroElide.cpp`):**
     Splits `llvm.coro.suspend` intrinsics into `(resume, destroy, cleanup)`
     ramp/switch clones and elides heap coroutine frames (`llvm.coro.alloc`) into
     caller stack frames when inlined into the awaiting caller.
- **Mapping onto Anneal's 4 `trusted/` Primitives (`CoroutineLoweringValidator`):**
  - **Cross-Language `BehaviorCodec`:**
    `Compiles L_CoroutineMIR L_MIR coroCodec s t` where `coroCodec.encodeQuery`
    maps a sequence of resumption inputs to repeated `Coroutine::resume` calls on
    the `CoroutineState` struct, and `decodeOut` projects `Poll::Pending(v)` and
    `Poll::Ready(ret)` back to `Yielded(v)` and `Completed(ret)`.
  - **`EventualBehaviorOf` Step Elasticity:** Absorbs entry discriminant
    `SwitchInt` dispatch steps and cross-yield state save/restore field writes
    while enforcing the normal-form obligation `HasYield t = false`.
- **Mechanized Stress Test (`coroutine_pinned_productive` and `coroutine_unpinned_move_violates_safety`):**
  In [MidLevelOptimizationAndLoweringProbes.lean](support/MidLevelOptimizationAndLoweringProbes.lean)
  (lines 407–441), when a coroutine creates an interior reference `let r = &x;`
  before an `.await` point and dereferences `*r` after resumption, moving the
  `CoroutineState` struct between `poll` calls (`resumeAddr ≠ entryAddr`)
  leaves `r` dangling (`coroutine_unpinned_move_violates_safety`). Encoding the
  `Pin<&mut Self>` address-stability invariant as `PinPre` (`resumeAddr = entryAddr`)
  yields `InhabitedPre PinPre ∧ L_Coro.ProductiveOn PinPre ()`
  (`coroutine_pinned_productive`).

#### 7.2 Use Case 3.21: Closure Conversion, Defunctionalization, Drop Elaboration, and Pattern-Matching Compilation (`HighLevelDesugarValidator`)

- **Real-World Tools Analyzed:**
  1. **`rustc ElaborateDrops` (`compiler/rustc_mir_transform/src/elaborate_drops.rs`):**
     Lowers pre-elaboration MIR `Drop` terminators into conditional drops guarded
     by synthesized stack boolean drop flags (`drop_flag_x : bool`) along both
     normal and `unwind` cleanup paths.
  2. **Maranget Pattern-Matching Decision Trees (`ML Workshop 2008`, DOI `10.1145/1411304.1411311`) & `CakeML` Verified Pattern Compiler (`pattern_matching/`):**
     Compiles declarative `match` clause matrices (with nested constructors,
     wildcards, or-patterns `P | Q`, and pattern guards `if g`) into a shared
     `SwitchInt` decision DAG using column heuristics (`q`, `ba`, `p`).
  3. **`CertiCoq` (`CertiCoq/certicoq`, Anand et al., CoqPL 2017; Paraskevopoulou, Li, Appel, ICFP 2021, DOI `10.1145/3473591`) & `CakeML` Closure Conversion (`closLang` / `bvl`):**
     Mechanized closure conversion and lambda lifting in Coq and HOL4, proving
     step-indexed / logical-relations equivalence between higher-order closures
     and flat environment structs paired with code pointers.
- **Mapping onto Anneal's 4 `trusted/` Primitives (`HighLevelDesugarValidator`):**
  - **Languages and `BehaviorCodec`:** `Compiles L_Declarative L_MIR desugarCodec s t`
    over `EventualBehaviorOf`, absorbing $1 \to d$ Maranget decision-DAG tests
    and runtime `drop_flag` updates while preserving the exact sequence of
    observable `Drop::drop` and match-guard calls in `trace : List Obs`.
  - **Match-Guard Move Hazards and Double-Panic Aborts:** `HighLevelDesugarValidator`
    checks in `VerificationResult` that no scrutinee sub-place is moved out
    *before* a match guard `if check(&x)` succeeds (preserving the intact
    scrutinee for fallback arms), and verifies that if a destructor panics while
    already unwinding on a cleanup path, `t` transitions to `.abort` rather than
    double-dropping or silently swallowing the first unwind.

#### 7.3 Use Case 3.22: Automatic Differentiation (`AD`) on MIR/SSA (`AutoDiffValidator`)

- **Real-World Tools Analyzed:**
  1. **`Enzyme` (`EnzymeAD/Enzyme`, Moses & Churavy, NeurIPS 2020; Moses et al., SC 2021) & `rustc #[autodiff]` (`compiler/rustc_codegen_llvm/src/autodiff.rs`, Drehwald & Moses):**
     Synthesizes forward-mode tangent and reverse-mode adjoint functions directly
     on optimized mid-level IR (after `SROA`, `Inlining`, and `LICM`, which
     dramatically reduces reverse-mode tape size compared to pre-optimization
     AD), using activity analysis, type analysis, and a shadow memory / tape cache.
  2. **`Tapenade` (`Hascoët & Pascual, ACM TOMS 2013`, DOI `10.1145/2450153.2450158`):**
     Source-to-source Fortran/C AD engine pioneering static dataflow activity,
     To-Be-Recorded (`TBR`) analysis, and binomial checkpointing schedules
     (Revolve) for bounded-memory reverse sweeps.
  3. **`CertiGrad` (`Selsam, Liang, Dill, ICML 2017`) and `SciLean` (`lecopivo/SciLean`, Skřivan):**
     `CertiGrad` proved end-to-end correctness of stochastic backpropagation
     graphs in Lean 3, while `SciLean` provides tactic-driven symbolic and
     programmatic forward/reverse automatic differentiation in Lean 4 via
     verified function transformations (`fwdFDeriv`, `revFDeriv`).
- **Mapping onto Anneal's 4 `trusted/` Primitives (`AutoDiffValidator`):**
  - **Languages and `BehaviorCodec`:**
    `Compiles (TangentialSpecLang s) L_MIR adCodec s t` where `adCodec.encodeQuery`
    pairs primal arguments with seed tangents $\dot{x}$ (forward mode) or seed
    cotangents $\bar{y}$ and an empty initial tape (reverse mode), and
    `decodeOut` strips the deallocated internal tape at return to project
    $(\text{out}, \nabla f)$.
  - **`EventualBehaviorOf` Step Elasticity:** Absorbs the $1 \to 2..4$
    instruction expansion of dual-number arithmetic and the $N \to 2N..4N$
    forward-plus-reverse sweep expansion.
  - **LIFO Tape Balance and Shadow `&mut` Aliasing:** In reverse mode, primal
    shared reads (`x₁: &f64, x₂: &f64`) turn into adjoint accumulates
    (`*dx₁ += adj; *dx₂ += adj`). If a caller passes aliased shared references
    `x₁ == x₂` with aliased shadow references `dx₁, dx₂ : &mut f64`, Rust's
    `&mut` uniqueness rule is violated! `AutoDiffValidator` checks both per-block
    LIFO tape push/pop balance across dynamic loops and disjointness (or raw
    pointer atomic/sequential accumulation) of shadow adjoint parameters in
    `VerificationResult`.

---

### 8. Category G: Relational Equivalence, Semantic Diff, and C-to-Rust Migration (Use Case 3.23)

```
Basis: source + execution + derived
```

#### 8.1 Use Case 3.23: Cross-Version PR Regression Equivalence (`AnnealDiff`), C-to-Rust Migration Validator (`C2RustCertifier`), and Equivalent-Mutant Filter (`MutEquiv`)

- **Real-World Tools Analyzed:**
  1. **`SymDiff` (`Lahiri, Hawblitzel, Kawaguchi, Rebêlo, CAV 2012`, DOI `10.1007/978-3-642-31424-7_54`):**
     Differential verifier over Boogie IR that constructs mutual product
     summaries to prove partial equivalence or extract differential regression
     counterexamples across program versions.
  2. **`LLReve` (`Felsing, Grebing, Klebanov, Rümmer, Ulbrich, ASE 2014`, DOI `10.1145/2642937.2642987`):**
     Relational equivalence verifier for LLVM IR that pairs off loops with
     different step counts at synchronization cut-points and discharges
     relational Horn clauses (`CHC`s) via `Z3`/`Eldarica`.
  3. **`UC-KLEE` (`Ramos & Engler, CAV 2011`, DOI `10.1007/978-3-642-22110-1_55`):**
     Under-constrained symbolic execution engine that cross-checks two C
     functions starting from lazy symbolic heap structures without requiring
     whole-program harnesses.
  4. **`C2Rust` (`immunant/c2rust`), `Laertes` (`Emre et al., OOPSLA 2021`, DOI `10.1145/3485495`), and `CROWN` (`Zhang, David, Yu, Wang, CAV 2023`, DOI `10.1007/978-3-031-37706-8_23`):**
     `C2Rust` translates C-1999 ASTs into syntax-level `unsafe` Rust with raw
     pointers (`*mut T`); `Laertes` and `CROWN` infer ownership, mutability, and
     fat-pointer array bounds via pointer/SMT constraints to lift raw C pointers
     into safe Rust `Box<T>`, `&T`, `&mut T`, and `&[T]` slices—without formal
     equivalence proofs.
  5. **Trivial Compiler Equivalence (`TCE`, Papadakis, Jia, Harman, Le Traon, ICSE 2015, DOI `10.1109/ICSE.2015.103`):**
     Uses optimizing compiler passes to detect and prune semantically equivalent
     mutants during mutation testing.
- **Mapping onto Anneal's 4 `trusted/` Primitives (`RelationalEquivSuite`):**
  - **Proof-Gated C-to-Rust Compilation (`C2RustCertifier`):**
    ```lean
    InhabitedPre cPre ∧
    L_Clight.ProductiveOn cPre f_c ∧
    Compiles L_Clight L_MIR cToRustCodec f_c f_rust
    ```
     paired with an anti-degeneracy obligation `UnsafeBlockCount f_rust == 0` (or
    `SafeRustRatio f_rust > SafeRustRatio f_c`) in `VerificationResult`.
  - **`EventualBehaviorOf` Step Elasticity:** Relates C pointer-increment loops
    (`p++`) to safe Rust `slice.iter()` loops with completely different per-step
    CFG structures by synchronizing at loop cut-points and comparing terminal/IO
    outcomes `EventualOut ExternIOObs Val`.
- **Mechanized Stress Tests (`c2rust_ub_source_vacuously_compiles_without_productiveOn`, `c2rust_productiveOn_blocks_ub_source`, and `c2rust_null_empty_slice_rejected_under_idCodec`):**
  In [MidLevelOptimizationAndLoweringProbes.lean](support/MidLevelOptimizationAndLoweringProbes.lean)
  (lines 443–509):
  1. **Signed-Overflow Directionality and Vacuity Guard:** In C (`L_Clight`),
     signed integer overflow is UB (`Partial.ub`), whereas in Rust release mode
     it wraps. Thus translating C signed addition to Rust wrapping addition
     satisfies `Compiles L_Clight L_MIR`. However, if a legacy C function has
     unconditional UB on all inputs, `Compiles` holds vacuously for *any* target
     (`c2rust_ub_source_vacuously_compiles_without_productiveOn`). Conjoining
     `InhabitedPre cPre ∧ L_Clight.ProductiveOn cPre f_c` immediately blocks
     vacuous C-to-Rust migration (`c2rust_productiveOn_blocks_ub_source`).
  2. **The `(NULL, 0)` C Buffer vs. Non-Null Rust `&[T]` Slice Trap:** In C,
     passing `(NULL, 0)` for a zero-length buffer is common and defined when no
     bytes are read (`len == 0`), whereas in Rust constructing a slice `&[u8]`
     from a null pointer (`ptr == 0`) via `slice::from_raw_parts(NULL, 0)` is
     **immediate Undefined Behavior** even when `len == 0` (Rust slices require
     `NonNull::dangling()`). Theorem
     `c2rust_null_empty_slice_rejected_under_idCodec` mechanizes this exact
     soundness bug, proving that `cToRustCodec` or `cPre` must either restrict
     `ptr ≠ 0` in `cPre` or canonicalize `(NULL, 0)` to `(NonNull::dangling(), 0)`
     at the FFI boundary.

---

### 9. Complete 23-Use-Case Mapping and Architectural Stress-Test Matrix

| ID | Use Case / Validator | Representative Real-World Tools | Primary `trusted/` Primitives | `EventualBehaviorOf` Step Elasticity | Key Semantic Stress Test / Anti-Degeneracy Invariant |
| :- | :--- | :--- | :--- | :--- | :--- |
| **3.1** | `mem2reg` (`MemToAnSSA`) | `Vellvm vmem2reg`, `CompCertSSA`, Braun et al., `LLVM PromoteMemToReg` | `Compiles L_MIR L_AnSSA mem2regCodec` | Absorbs `StorageLive`/`StorageDead` & stack load/store deletion ($k \to 1$) | Uninit stack read (`Partial.ub`) refines to frozen SSA reg (`mem2reg_uninit_refines`); `MemoryLoadStoreCount t P = 0` |
| **3.2** | `SROA` (`SROACertifier`) | `rustc sroa.rs`, `LLVM SROA`, `MLIR SROA`, `CompCert SimplLocals` | `Compiles L_MIR L_MIR sroaCodec` | Absorbs $1 \to m$ struct copy expansion & $1 \to 0$ dead-field pruning | Forbids raw-byte `*const u8` inspection of uninit struct padding & union overlap; `AggregateEliminated` |
| **3.3** | SSA Destruction & Parallel Moves | Rideau-Leroy Windmill, `CompCertSSA CSSA`, Boissinot et al. | `Compiles L_AnSSA L_MIR ssaDestructCodec` | Absorbs $1 \to k+1$ parallel-edge-to-sequential move expansion | Catches Briggs/Boissinot lost-copy & swap cycle bugs on backedges; `ZeroBlockParams t = true` |
| **3.4** | Critical-Edge Split & `LCSSA` | `LLVM BreakCriticalEdges`, `LoopSimplify`, `LCSSA` | `Compiles L_AnSSA L_AnSSA idCodec` | Absorbs $+1$ empty split-block `Goto` step (including in `.diverges` loops) | Preserves in-flight panic state & drop-flag invariants across split `unwind` landing-pad edges |
| **3.5** | Global Value Numbering (`GVN`) | Tristan-Leroy GVN, `Chamois CSE2`, `rustc gvn.rs`, `LLVM NewGVN` | `Compiles L_AnSSA L_AnSSA idCodec` | Absorbs $1 \to 0$ congruent instruction deletion | Rejects unsound IEEE-754 `x + 0.0 -> x` at `x = -0.0`; `externalCall` kills unprotected memory numbers |
| **3.6** | Partial Redundancy Elim (`PRE`) | Knoop-Rüthing-Steffen `LCM`, Tristan-Leroy LCM, `Chamois BTL_LCM` | `Compiles L_AnSSA L_AnSSA idCodec` | Absorbs path-sensitive $0 \to 1$ and $2 \to 1$ code motion | Enforces down-safety (anticipability) so trapping ops (`a / b`) never hoist above `externalCall` or loops |
| **3.7** | `SCCP` (`SCCPValidator`) | Wegman-Zadeck, `CompCertSSA SCCP`, `CompCert Constprop`, `LLVM IPSCCP` | `Compiles L_MIR L_MIR idCodec` | Absorbs multi-step constant folding & dead subgraph deletion | Commits concrete values at `StepResult.choice` to prevent the LLVM `undef` multi-use branching paradox |
| **3.8** | `DCE` & `DSE` (`DCEDSEValidator`) | Benton RHL, `CompCert Deadcode`/`NeedDomain`, `rustc DSE`, `LLVM BDCE` | `Compiles L_MIR L_MIR idCodec` | Absorbs $1 \to 0$ dead op/store deletion while keeping `Div ↔ Div` | Blocks deleting panicking ops (`let _ = x / d`) without `d ≠ 0` proof (`dce_panicking_div_unsound`) |
| **3.9** | `CVP` & Range-Check Elim | Bodík `ABCD`, GraalVM `ABCD`, `LLVM CVP` & `IRCE` | `Compiles L_MIR L_MIR idCodec` | Replaces `Assert` with `Goto`, pruning `.unwind` cleanup branches | Verifies bounds inequalities over modular `BitVec 64` to prevent `i + 1 < len` wrap-around bugs at `usize::MAX` |
| **3.10** | Borrow Load/Store Forwarding | `Stacked Borrows`, `Tree Borrows`, `Miri`, `SimulIris` | `Compiles L_MIR L_MIR idCodec` | Absorbs $1 \to 0$ redundant load elimination via UB refinement | Deleting a shared read only avoids disabling conflicting tags, monotonically refining `s` (`≤`) |
| **3.11** | Protector Call Motion | `SimulIris` `Protector`s, `Tree Borrows`, LLVM `ScopedNoAliasAA` | `Compiles` + `StepResult.externalCall` | Shifts memory loads/stores across `externalCall` ($\pm 1$ step) | `DSE` across diverging `externalCall` requires immediate foreign-read protector enforcement (`Probe 4`) |
| **3.12** | Escape Analysis (`Box` → Stack) | `LLVM AAHeapToStack`, GraalVM `PEA`, Go escape, Twin-Allocation | `Compiles L_MIR L_MIR heapToStackCodec` | Replaces multi-step `__rust_alloc` with `StorageLive` ($k \to 1$) | Models heap OOM as demonic choice & requires `¬AddressExposed` (`HeapAllocCount` drop) |
| **3.13** | `LICM` (`LICMValidator`) | Tristan-Leroy `LICM`, `Chamois BTL`, `Crellvm LICM`, `LLVM LICM` | `Compiles L_AnSSA L_AnSSA idCodec` | Compresses $N$ in-loop evaluations to $1$ preheader step ($N \to 1$) | Rejects hoisting trapping `100 / d` above 0-trip loops (`licm_trapping_zero_trip_unsound`) |
| **3.14** | Loop Unrolling & Unswitching | `LLVM SimpleLoopUnswitch` (`freeze`), `LoopUnroll`, `LoopPeel` | `Compiles L_AnSSA L_AnSSA idCodec` | Compresses $k$ latch branches into $1$ ($k \cdot m \to k \cdot m - (k-1)$) | Requires zero-trip guard or initialized/frozen proof before unswitching loop-invariant conditions |
| **3.15** | Loop Fusion / Polyhedral | `PolyVerify` (Courant-Leroy), `Pluto`, `ISL`, `Polly`, `Polygeist` | `Compiles L_MIR L_MIR idCodec` | Permutes iteration steps & fuses loop control overhead across SCoP | Requires proving all iterations in polyhedral domain $\mathcal{D}$ panic-free so bounds-check order cannot shift |
| **3.16** | `IVSR` & SIMD Vectorization | `Chamois BTL` LSR, `HELIX`, `Alive2`, `VeGen`, `Diospyros` (`egg`) | `Compiles L_MIR L_MIR idCodec` | Compresses $W$ scalar iterations into $1$ `Simd<T, W>` step ($W \to 1$) | Distinguishes wrapping vs. checked `IVSR` recurrence & blocks non-associative IEEE-754 SIMD reductions |
| **3.17** | Inlining & Devirtualization | `CompCert Inliningproof`, `CakeML bvl_inline`, `SimulIris`, `rustc` | `Compiles L_MIR L_MIR idCodec` | Eliminates call/return administrative frame steps ($2 \to 0$) | Inlining drops callee `Protector` (`inline_drops_protector_refines`), whereas outlining is non-reversible |
| **3.18** | Monomorphization / Polymorph | `rustc polymorphize.rs`, `rustc_monomorphize`, `.NET CLR` generics | `Compiles (L_PolyMIR σ) L_MIR layoutIsoCodec` | Lockstep or constant-offset projection transitions | Audits exact `(size, align, abi, isFreeze)` equality (blocking `[u8; 4]` vs. `u32` alignment mismatch) |
| **3.19** | `TCO`, Jump Threading, Switch | `CompCert Tailcallproof`/`Tunnelingproof`/`Switch`, `rustc` | `Compiles L_MIR L_MIR idCodec` | Compresses branch chains ($k \to 1$) or expands binary search ($1 \to \log n$) | Enforces `StorageDead` / zero escaping stack borrows before caller frame reuse in `TailCall` (`become`) |
| **3.20** | Async / Coroutine Lowering | `rustc coroutine.rs`, `RustBelt` `Pin`, `LLVM CoroSplit`/`CoroElide` | `Compiles L_CoroutineMIR L_MIR coroCodec` + `ProductiveOn` | Absorbs discriminant `SwitchInt` & cross-yield state save/restore steps | Enforces `Pin<&mut Self>` address stability (`coroutine_pinned_productive`) & disjoint union field live ranges |
| **3.21** | Closure, Drop Elab & Match | `rustc elaborate_drops.rs`, Maranget, `CakeML`, `CertiCoq` | `Compiles L_Declarative L_MIR desugarCodec` | Absorbs Maranget DAG tests & runtime boolean `drop_flag` updates | Prevents move-before-guard bugs in shared match DAGs & enforces double-panic `.abort` on unwind |
| **3.22** | Automatic Differentiation (`AD`) | `Enzyme`, `rustc #[autodiff]`, `Tapenade`, `CertiGrad`, `SciLean` | `Compiles (TangentialSpecLang s) L_MIR adCodec` | Expands $1$ primal step into $2..4$ forward or reverse-sweep steps | Audits LIFO tape push/pop balance across loops & prevents shadow `&mut` aliasing on shared primal inputs |
| **3.23** | PR Diff, `c2rust` & MutEquiv | `SymDiff`, `LLReve`, `UC-KLEE`, `C2Rust`, `CROWN`, `Laertes`, `TCE` | `InhabitedPre ∧ ProductiveOn ∧ Compiles L_Clight L_MIR` | Synchronizes C pointer loops with Rust iterator loops across cut-points | Blocks vacuous UB C compilation (`c2rust_productiveOn_blocks_ub_source`) & catches `(NULL, 0)` slice UB |

### Phase-2 Long-Tail Ecosystem Additions and Primitive Mappings

Basis: documentation, derived — incorporates the Stage-2 exhaustive long-tail
tool discovery sweep (`agent_a_shard_*_tools.md`) into the package's tool
taxonomy and four-primitive `trusted/` mapping.

- **Trivet (2025-2026), `mlir-tv` (`Ret2Me/mlir-tv`), and PEQC-MLIR (Pouchet et
  al. 2024-2025):** Lean 4 + LLM loop-invariant translation validation over
  `Lean-MLIR` and SMT/polyhedral equivalence validators for MLIR dialect
  lowerings.
- **CVT (TACAS 1998), TVOC (FMSD 2005), Necula GCC TV (PLDI 2000), PEC (PLDI
  2009), CMP (POPL 2020), and STOKE Semantic Alignment (PLDI 2019):**
  Foundational structure-preserving and product-program translation validators
  mapped onto `EventualBehaviorOf` and `Compiles`.
- **Isabelle/HOL `FormalSSA` (`afp/Formal_SSA`), MLIR `Mem2Reg`, and Cranelift
  `aegraph` (`bytecodealliance/wasmtime`):** Mechanized Braun et al. SSA
  construction, block-argument promotion (`AnSSA`), and scoped acyclic e-graphs
  in SSA dominator trees.
- **PolCert (`xmopx/polcert`, POPL 2021) and PolyCheck (POPL 2016):** Rocq-
  verified polyhedral scheduler validating Pluto schedules via the Verified
  Polyhedra Library (`VPL`) and Farkas certificates.
- **CHAD (Combinatory Homomorphic AD, TOPLAS) and Krawiec et al. (POPL 2022):**
  Mechanized logical-relations proofs of source-to-source forward and reverse-
  mode automatic differentiation.
- **VERT (2024), C2SaferRust, Syzygy, and `cargo-mutants` / `Mull`:** Verified
  C-to-Rust transpilation and symbolic-execution equivalent-mutant filters.

---

### Part II — Historical Verification Failures, Root-Cause Postmortems, and Architectural Defenses

### Finding 1: LLVM `undef` vs. `poison` Composition Paradoxes and Pointer-Integer Provenance Collapse

`Basis: source + execution + derived`

#### 1.1 The `LoopUnswitch` + `GVN` + `InstCombine` Composition Paradox (`PLDI 2017`)

Prior to the introduction of the `freeze` instruction, LLVM IR modeled
uninitialized memory and deferred arithmetic undefined behavior via two distinct
constructs:

- **`undef`**, which represented the set of all bit-patterns of a given type and
  permitted **different uses of the same SSA register** `v = undef` to observe
  independent bit-patterns (so `v ^ v` could refine to any integer, while `v + v`
  was neither guaranteed to be even nor fixed across uses); and
- **`poison`**, a tainting error token produced by arithmetic overflow (`add
  nsw`), out-of-bounds shifts (`shl`), or out-of-bounds `getelementptr inbounds`
  that triggered immediate Undefined Behavior (UB) when used as a branch
  condition (`br i1 %p`), memory address, divisor, or volatile/I/O operand.

As Lee et al. (*Taming Undefined Behavior in LLVM*, PLDI 2017, §§2–3, DOI
`10.1145/3062341.3062343`) demonstrated, this dual semantics made standard
mid-level optimizations **mutually inconsistent**:

1. **Why `LoopUnswitch` was unsound on `poison`:** Consider a well-defined loop
   whose invariant condition `c2` is computed from an expression `x +nsw 1` (or
   an uninitialized variable) that is only guarded inside `if (c1)`:
   ```llvm
   ; Source program (100% well-defined when c1 == false and x == INT_MAX):
   loop:
     %c2 = icmp slt i32 (%x +nsw 1), %y
     br i1 %c1, label %check_c2, label %safe_body
   check_c2:
     br i1 %c2, label %then, label %else
   ```
   When `c1` is `false` and `x == INT_MAX`, `%c2` evaluates to `poison`, but the
   source program never branches on `%c2` and is completely UB-free. If
   `LoopUnswitch` hoists `br i1 %c2` above the loop (duplicating the loop into a
   `%c2 == true` copy and a `%c2 == false` copy), the transformed program
   executes `br i1 poison` unconditionally on entry, turning a well-defined
   execution into immediate UB.
2. **Why `GVN` + `LoopUnswitch` was unsound on `undef`:** Conversely, if a
   variable `y` is uninitialized (`undef`) when a loop runs for `0` iterations or
   takes a non-reading branch, `SROA`/`mem2reg` promotes `y` to `undef`. If
   `LoopUnswitch` branches on `y` (`if (y) { L_true } else { L_false }`) and a
   subsequent `GVN` or `SCCP` pass propagates `y == true` inside `L_true` while
   another use of `y` earlier or later is independently refined as `false` (valid
   under multi-use `undef`), the combined pipeline executes both contradictory
   branches on a single path (LLVM PR21467 / PR31632).
3. **Why `select`-to-branch and `InstCombine` collided (`Alive2`, `PLDI 2021`):**
   Lopes et al. (*Alive2: Bounded Translation Validation for LLVM*, PLDI 2021,
   §§2, 5, DOI `10.1145/3453483.3454030`) further showed that rewriting
   `%r = select i1 %c, i32 %a, i32 %b` into an explicit diamond branch
   `br i1 %c` is unsound whenever `%c` can be `poison` and `%a == %b` (or `%r` is
   unused), because `select poison, %a, %b` merely returns `poison`, whereas
   `br i1 poison` triggers immediate UB. Similarly, `InstCombine` rewrites of
   `select i1 %c, i1 true, i1 %x` into `or i1 %c, %x` leaked `poison` from `%x`
   even when `%c == true`!

The only mathematically consistent resolution (Lee et al., PLDI 2017, §4) was to:
- Make `br i1 poison` immediate UB;
- Introduce a dedicated `freeze(v)` instruction that nondeterministically picks
  a **single, fixed** bit-pattern when `v` is `poison` so all downstream uses of
  `%f = freeze(v)` observe the exact same bitvector;
- Require `LoopUnswitch` and `PRE` to wrap speculated branch conditions in
  `freeze(%c2)` before hoisting `br i1`; and
- Deprecate per-use `undef` in favor of `freeze(poison)`.

#### 1.2 The `ptrtoint` / `inttoptr` + `GVN` Provenance Collapse (`OOPSLA 2018`)

Even with `freeze`, Lee et al. (*Reconciling High-Level Optimizations and
Low-Level Code in LLVM*, OOPSLA 2018, §2, DOI `10.1145/3276495`; LLVM PR34548 /
PR35229) proved that combining `GVN` with alias analysis causes end-to-end
miscompilations when two distinct allocations `p` and `q` happen to sit adjacent
in memory:

```c
char p[1], q[1];
uintptr_t ip = (uintptr_t)(p + 1); // One-past-the-end of p
uintptr_t iq = (uintptr_t)q;       // Base of q
if (ip == iq) {
    *(char *)iq = 10;              // Valid write to q[0] in source!
}
```

1. **Pass 1 (`GVN` equality propagation):** Inside the `if (ip == iq)` block,
   `GVN` observes `ip == iq` and replaces `iq` with `ip`, yielding
   `*(char *)ip = 10`, i.e., `*(char *)(uintptr_t)(p + 1) = 10`.
2. **Pass 2 (`InstCombine` cast folding):** `InstCombine` folds
   `(char *)(uintptr_t)(p + 1)` to `p + 1`, yielding `*(p + 1) = 10`.
3. **Pass 3 (`BasicAA` / `DSE`):** Alias analysis knows that a pointer derived
   from allocation `p` (`p + 1`) cannot alias allocation `q` (`noalias`), and
   furthermore dereferencing one-past-the-end of `p` (`*(p + 1)`) is immediate
   out-of-bounds UB! The optimizer therefore deletes the store `*(p + 1) = 10`
   or folds subsequent reads of `q[0]` to the old value.

The root cause is that `ip == iq` compares only the **numeric address**
(`Addr`), whereas `*(char *)iq` depends on the **allocation provenance**
(`AllocId`) carried by `iq` (or exposed via `ptrtoint`). Substituting `ip` for
`iq` under numeric equality is unsound whenever values carry hidden provenance
that `==` does not compare.

#### 1.3 Architectural Prevention in Anneal's `trusted/` Primitives

In Anneal (`Trusted/Refinement.lean` and `Trusted/MirSemantics.lean`), both
paradoxes are blocked at the root:

1. **Transitive Partial-Behavior Preorder (`Compiles`):** In
   `Trusted/Refinement.lean`, `Behavior Query Out := Query → Partial (Out → Prop)`
   defines refinement `B₂ ≤ B₁` by:
   $$\forall q,\; B_1(q).\text{defined} \implies \bigl(B_2(q).\text{defined} \;\wedge\; \forall o,\; B_2(q).\text{val}(o) \implies B_1(q).\text{val}(o)\bigr)$$
   Because `≤` is a verified reflexive, transitive preorder (`Preorder.le_trans`),
   it is **mathematically impossible** for a chain of verified passes $s = p_0
   \to p_1 \to \dots \to p_n = t$ satisfying `Compiles` at each step to miscompile
   a defined source input $q$. Any pass that attempts to hoist a branch on a
   potentially uninitialized or trapping value onto a path where the source was
   `.defined` fails `B₂(q).defined` at that step, as mechanized in
   `loopUnswitch_without_freeze_violates_compiles` in
   `support/MidLevelIrFailureCanaries.lean`.
2. **Typed Provenance Separation (`MirVal` vs. Numeric `BitVec`):** In
   `MirSemantics.lean`, pointers (`MirVal.ref` / `(AllocId, Offset, Tag)`) are
   distinct from integer bitvectors (`MirVal.int`). Therefore, an integer
   equality guard `ip == iq` proves equality of numeric addresses only, never
   equality of `(AllocId, Offset)` pairs; `GVNCertifier` cannot substitute a
   pointer of provenance `AllocId(p)` for `AllocId(q)` without falsifying the
   memory-step refinement obligation (`gvn_provenance_substitution_rejected` in
   `support/MidLevelIrFailureCanaries.lean`).

---

### Finding 2: `rustc` `-Zmir-opt-level=3/4` and `mutable-noalias` Miscompilations

`Basis: source + documentation + execution + derived`

#### 2.1 The Multi-Year `mutable-noalias` Saga on Self-Referential Generators and `Future`s (`#54878`, `#63818`, `#63934`)

Rust's borrow checker guarantees that safe mutable references `&mut T` are
unique, which in principle maps to LLVM's `noalias` parameter attribute. In
practice, `rustc` had to disable `-Zmutable-noalias` repeatedly for over five
years (`rust-lang/rust#54878`, tracking LLVM bugs and self-referential
miscompilations `#63818` and `#63934`):

- **Root Cause 1 (Self-Referential Coroutine State Machines):** When an `async
  fn` or generator creates a local variable `x` and a reference `r = &x` that
  both live across an `.await` (`Yield`) suspension point, `rustc`'s coroutine
  lowering pass packs both `x` and `r` into fields of the synthesized
  `CoroutineState` struct. When `Future::poll(self: Pin<&mut Self>, cx: &mut
  Context)` is invoked, `self` is passed as `&mut CoroutineState`. If `rustc`
  marks the `self` pointer argument as LLVM `noalias`, LLVM's `ScopedNoAliasAA`
  assumes that **every memory access through a pointer not syntactically derived
  from the `self` parameter argument during that `poll` call does not alias
  `*self`**. However, inside the resumed state block, the coroutine loads the
  stored field `r = (*self).field_r` from memory and then accesses `*r`! Because
  `r` was loaded from memory rather than computed via `getelementptr` from the
  incoming `self` pointer argument, LLVM's alias analysis concluded that `r` was
  not based on `self`, treated `*r` and `(*self).field_x` as non-aliasing, and
  reordered or deleted stores across them (`#63818`, `#63934`).
- **Root Cause 2 (Fix via `!Unpin` and Tree Borrows):** `rustc` had to suppress
  `noalias` on `&mut T` whenever `T` did not implement `Unpin` (i.e., could be a
  pinned self-referential generator/Future) and later align its aliasing model
  with Stacked Borrows (`UnsafePinned` / `Pin<&mut T>`) and Tree Borrows.

#### 2.2 `rustc_mir_transform` Pass Miscompilations (`GVN`, `ConstProp`, `DestinationPropagation`, `DSE`, and Coroutine `StorageLive` Overlap)

As `rustc` expanded its native MIR optimization pipeline (`-Zmir-opt-level=2/3/4`
in `compiler/rustc_mir_transform`), several soundness bugs (`I-unsound`,
`A-mir-opt`) escaped into nightly and stable compilers because passes reasoned
about syntactic MIR places without a mechanized operational semantics:

1. **`GVN` Reusing Partially Moved Function Arguments (`rust-lang/rust#120613`)
   and Overlapping Aliasing Assignments (`#141038`):** In `#120613`, `rustc`'s
   MIR `GVN` pass recorded that `_2 = move (_1.0)` had the same value number as
   `_1.0`. After `_1.0` was moved and dropped/mutated, a subsequent read of `_2`
   was rewritten by `GVN` back into a read of `_1.0`, causing a use-after-move /
   double-drop miscompilation. In `#141038`, `GVN` substituted an aliased place
   into the right-hand side of an assignment `*_1 = *_2` when `_1` and `_2`
   pointed to overlapping memory, violating MIR's requirement that `Assign(dst,
   Use(Operand::Copy(src)))` has non-overlapping `dst` and `src`.
2. **`ConstProp` Propagating Across Mutating Borrows (`rust-lang/rust#110947`)
   and Corrupting Pointer-Typed Enum Fields (`#118328`):** In `#110947`, MIR
   `ConstProp` tracked constant values stored into a local `_1`, failed to
   invalidate that constant knowledge when an interior raw pointer or mutable
   reborrow mutated `_1`, and folded a post-mutation read of `_1` to the stale
   pre-mutation constant. In `#118328`, `ConstProp` misread niche-encoded enum
   layouts containing pointers (`Option<NonNull<T>>`), folding a valid non-null
   pointer field to a zero scalar constant.
3. **`DestinationPropagation` and `DeadStoreElimination` Desynchronizing
   `StorageLive`/`StorageDead` Across Coroutine Yields (`rust-lang/rust#63616`,
   `#146383`):** In MIR, `StorageLive(l)` and `StorageDead(l)` control both
   LLVM's `llvm.lifetime.start`/`end` stack-slot coloring and `rustc`'s
   coroutine state-machine layout packing (`compiler/rustc_mir_transform/src/coroutine.rs`).
   When `DestinationPropagation` (`#146383`) merged destination places `_dst`
   and `_tmp` without taking the union of their `StorageLive`..`StorageDead`
   live ranges, or when coroutine lowering (`#63616`) computed storage conflicts
   for partially initialized aggregates across `Yield`, two locals that were
   simultaneously live across a suspension point were assigned **overlapping
   byte offsets** inside the `CoroutineState` union, silently overwriting each
   other across `.await`.

#### 2.3 Architectural Prevention in Anneal's `trusted/` Primitives

Anneal's architecture prevents every class of `rustc` MIR optimizer and
coroutine-layout miscompilation in two complementary ways:

1. **Extraction of Post-Optimization `Runtime(PostCleanup)` MIR:** For crates
   compiled by `rustc`, `anneal-rustc-capture` extracts `Runtime(PostCleanup)`
   MIR *after* all MIR transformations (`ElaborateDrops`, `Coroutine` lowering,
   `GVN`, `DestinationPropagation`) have already executed. Thus, any bug in an
   upstream `rustc` MIR pass that introduces an overlapping assignment, a stale
   `StorageDead` access, or an overlapping coroutine variant offset is exposed
   directly in the captured `MirBody` and **fails verification** against
   `MirMachine`'s operational semantics (where accessing a `StorageDead` local
   or overlapping `Assign` transitions to `.failed .ub`).
2. **Certifying MIR-to-MIR Validators (`Compiles L_MIR L_MIR`):** When MIR
   optimizations (`GVNCertifier`, `BorrowMemoryOpt`, `CoroutineLoweringValidator`)
   are run inside Anneal's verified pipeline, `MirMachine` tracks per-local
   liveness (`StorageLive`/`StorageDead`), initialization masks, and borrow tags
   explicitly in `State`. A `GVN` rewrite that substitutes a moved/deallocated
   place (`#120613`), a `ConstProp` fold that ignores an aliasing write
   (`#110947`), or a coroutine layout packing that overlaps two co-live fields
   (`#63616`) fails the `Compiles` refinement theorem inside the Lean 4 kernel
   (`coroutine_overlapping_live_fields_rejected` in
   `support/MidLevelIrFailureCanaries.lean`).

---

### Finding 3: Stacked Borrows and Tree Borrows Protector Bugs on Diverging External Calls

`Basis: source + execution + derived`

#### 3.1 The Dead-Store Elimination Paradox Across Diverging External Calls (`POPL 2020`, `PLDI 2025`, `Simuliris`)

One of the primary goals of Rust's aliasing models—Stacked Borrows (Jung et al.,
POPL 2020, DOI `10.1145/3371109`) and Tree Borrows (Villani et al., PLDI 2025,
DOI `10.1145/3735592`)—is to validate intra-function memory optimizations on
unique mutable references `x : &mut i32` across calls to unknown external
functions `ext()`. To keep `x` unaliased for the entire duration of a function
 call `fn foo(x: &mut i32)` even when `foo` does not access `x` after calling
`ext()`, both models attach a **Function-Entry Protector** to `x`'s borrow tag
$\tau_x$ upon entering `foo`, which remains active until `foo` returns.

During the Rocq mechanization of Stacked Borrows and Tree Borrows in
`Simuliris` (`e3abfcdc301f92250d4227fc03c00463bf57b982`), researchers discovered
that **sinking a store or eliminating a dead store across an unknown call
`ext()` is unsound under naive protector semantics if `ext()` diverges or
aborts**:

```rust
// Suppose a raw pointer `RAW_ALIAS` pointing to `*x` was legally created
// before `foo` was called (under Tree Borrows `Reserved` lazy initialization)
// or exposed via a parent tag, and stored in a global/thread-local variable.
pub fn foo(x: &mut i32) {
    *x = 1;      // Store 1 (appears overwritten by Store 2 below!)
    ext();       // Opaque external call: what if `ext()` reads `RAW_ALIAS`,
                 // prints its value, and then enters `loop {}` or `exit(0)`?
    *x = 2;      // Store 2
}
```

Consider what happens if a Dead Store Elimination (`DSE`) pass transforms `foo`
into `foo_opt` by deleting `*x = 1` (reasoning that `ext()` cannot legally read
or write `*x` without violating `x`'s protector, and `*x = 2` overwrites `*x = 1`
immediately after `ext()` returns):

1. **Case A (`ext()` returns normally):** If `ext()` read `RAW_ALIAS` during its
   execution, then in Stacked Borrows (or Tree Borrows once `*x = 1` activated
   $\tau_x$), reading `RAW_ALIAS` either immediately triggered protector UB or
   disabled $\tau_x$ so that either the protector check at `foo`'s exit or the
   subsequent write `*x = 2` triggered UB. Thus on all returning executions,
   `foo` had UB whenever `ext()` observed `*x`, making `DSE` sound.
2. **Case B (`ext()` diverges `loop {}` or terminates the process `exit(0)`):**
   Suppose `ext()` reads `*RAW_ALIAS`, prints the value it observes to standard
   output (`Obs`), and then enters an infinite loop `loop {}`!
   - Because `ext()` **never returns** to `foo`, the statement `*x = 2` in `foo`
     and `foo`'s function-exit protector check **never execute**!
   - Under a **Weak Protector** (or in Tree Borrows if `*x = 1` is deleted so
     $\tau_x$ remains in the `Reserved` state at function entry!), deleting
     `*x = 1` means that when `ext()` reads `*RAW_ALIAS` in `foo_opt`, $\tau_x$
     was never activated by a write! In Tree Borrows without an entry write, a
     foreign read of a `Reserved` mutable reference transitions $\tau_x$ to
     `Frozen`—which is **not UB** unless $\tau_x$ is later written or checked by
     a strong exit rule! Since `ext()` diverges and never returns, `foo_opt`
     never writes to $\tau_x$, whereas in the unoptimized `foo`, `*x = 1` wrote
     `1` and activated $\tau_x$ before `ext()` ran.
   - Even if $\tau_x$ is already `Active`, if protector violation is only
     checked when popping the call frame on return (`Weak` exit-only check), a
     diverging `ext()` never pops `foo`'s frame, so `foo` is UB-free and prints
     `1` before diverging, whereas `foo_opt` prints the old pre-`foo` value of
     `*x` before diverging—a **complete end-to-end miscompilation of a UB-free
     program**!

To restore soundness for `DSE` and store sinking across potentially diverging
external calls, Villani et al. (*Tree Borrows*, PLDI 2025, §4; `Simuliris`
`theories/tree_borrows/`) proved that:
- Protected references must distinguish **`Strong` vs. `Weak` protectors**: a
  `Strong` protector makes any foreign read of an `Active` protected `&mut T`
  **immediate UB at the moment of the foreign read** (even if the function later
  diverges), and
- Deleting or sinking the first write `*x = 1` across `ext()` is sound **only**
  if function entry already performs an implicit/virtual write initialization
  (or `x` enters as `Active` rather than `Reserved`), because otherwise deleting
  `*x = 1` removes the state transition from `Reserved` to `Active` that made
  `ext()`'s foreign read UB in the source program!

#### 3.2 Architectural Prevention in Anneal's `trusted/` Primitives

Anneal's `trusted/` architecture (`StepResult.externalCall` + `EventualBehaviorOf`
in `Trusted/StepResult.lean`, validated by the re-entrancy canaries in
`anneal-structural-external-calls-and-tcb-mutation-testing-2026`) directly
enforces both halves of this invariant:

1. **Immediate Call-Site Boundary Enforcement (`StepResult.externalCall`):**
   ```lean
   StepResult.externalCall (boundaryInv : Bool) (branches : State → Prop) :=
     if boundaryInv then .choice .demonic branches else .failed .ub
   ```
   In `MirMachine`, `boundaryInv` checks caller-side invariants *before* the
   external call begins, and `branches` constrains all reachable states (both on
   return and along internal callback/diverging prefixes) to preserve memory
   locations guarded by active `Strong` caller protectors. Any foreign access to
   an `Active` strongly protected caller location transitions immediately to
   `.failed .ub` at the access step, not lazily at function return.
2. **Distinguishing `Reserved` vs. `Active` in `Compiles`:** In
   `support/MidLevelIrFailureCanaries.lean`
   (`dse_across_diverging_call_unsound_under_weak_or_unactivated_protector` and
   `dse_across_diverging_call_sound_under_strong_active_protector`), Lean's
   kernel machine-checks both directions: when a protector is `Weak` (checked
   only at return) or `Reserved` (not yet activated on entry), eliminating
   `*x = 1` before a diverging `externalCall` violates `Compiles`; when the
   entry state marks `x` as `Active` under a `Strong` protector, any foreign
   observation inside `externalCall` triggers immediate `.failed .ub` in the
   source, so `Compiles` holds across both returning and `.diverges` outcomes.

---

### Finding 4: C++/Rust Forward-Progress (`mustprogress` / `willreturn`) Infinite-Loop Miscompilations

`Basis: normative + source + execution + derived`

#### 4.1 `rust-lang/rust#28728`: How LLVM Deleted Safe Rust `loop {}` Blocks and Executed Unreachable Code

For nearly six years (2015–2021), `rust-lang/rust#28728` (*"LLVM loop
optimization can make safe programs crash"*) stood as one of the most severe
soundness bugs in safe Rust. Under C++11 `[intro.progress]`, the C++ standard
allows an implementation to assume that any thread will eventually either
terminate, make a call to a library I/O function, perform a `volatile` access,
or perform an atomic synchronization operation. Consequently, in C++, a
side-effect-free infinite loop `while (true) {}` is Undefined Behavior.

Because LLVM was originally architected around C/C++ assumptions, multiple LLVM
middle-end passes (`SimplifyCFG`, `LoopDeletion`, `ADCE` — Aggressive Dead Code
Elimination, and `PostDominatorTree` construction) assumed that **every
side-effect-free loop terminates**:

```rust
pub fn hang_forever() -> ! {
    loop {} // 100% safe, well-defined diverging loop in Rust!
}

pub fn safe_caller(cond: bool) -> i32 {
    if cond {
        hang_forever();
    }
    // In Rust, this point is only reachable when `cond == false`!
    42
}
```

When LLVM optimized Rust programs containing side-effect-free infinite loops:
1. **`LoopDeletion` / `ADCE` deleted the loop:** Because `loop {}` has no memory
   writes, `volatile` operations, or calls, `ADCE` marked the loop's branch
   backedge as dead control flow and removed the loop entirely.
2. **Fallthrough into unreachable code (`!`) and missing `ret` instructions:**
   Because `hang_forever() -> !` returns the uninhabited never type `!`, `rustc`
   emitted LLVM's `unreachable` terminator immediately after the `loop {}` body.
   Once LLVM deleted the `loop {}`, execution fell straight into `unreachable`!
   In optimized builds, LLVM stripped everything ending in `unreachable`—meaning
   `hang_forever()` compiled to an **empty `0`-byte function body with no `ret`
   instruction**, falling straight through into whatever function happened to be
   placed next in the `.text` section of the ELF binary!
3. **Backward UB propagation (`cond` forced to `false`):** In `safe_caller`,
   because the `cond == true` branch ended in `unreachable` after loop deletion,
   `SimplifyCFG` deduced that `cond` could *never* be `true` on any valid
   execution, deleted the `if cond` check altogether, and unconditionally
   returned `42` (or corrupted memory when a bounds check was guarded by a
   diverging loop).

Fixing `rust-lang/rust#28728` required a fundamental redesign of LLVM's loop and
function attributes in LLVM 12 (`rust-lang/rust#81255`, `#83359`):
- LLVM introduced the **`mustprogress`** function and loop metadata attribute
  (which Clang emits for C++ functions, but `rustc` omits because Rust permits
  silent infinite loops) and the **`willreturn`** function attribute (asserting
  that a function call is guaranteed to return in finite time without
  diverging).
- `LoopDeletion`, `ADCE`, and `DeadStoreElimination` were restricted to eliminate
  loops or dead operations across calls only when `mustprogress` / `willreturn`
  is proven.

#### 4.2 Related Loop-Speculation Failure: Hoisting Trapping Operations Above Zero-Trip or Diverging Loops (`LICM` and `PRE`)

A closely related failure mode occurs in Loop-Invariant Code Motion (`LICM`) and
Partial Redundancy Elimination (`PRE`, Knoop-Rüthing-Steffen lazy code motion):
- Suppose a loop body contains a loop-invariant division `q = a / d` (which in
  Rust MIR emits an `Assert(d != 0)` panic check, and in x86-64 emits `idiv` /
  `udiv` which raises hardware `#DE` on `d == 0` or `INT64_MIN / -1`), preceded
  inside the loop by an early exit `if exit_now { break; }` or an infinite loop
  `if hang { loop {} }` or an external call `ext()`.
- If `LICM` hoists `q = a / d` into the loop preheader without proving either
  that `q = a / d` is **non-trapping (`d != 0`)** or that the loop executes
  $\ge 1$ iteration (`TripCount ≥ 1`) and `q = a / d` dominates all loop exits,
  external calls, and internal loops, then on an input where `d == 0` and
  `TripCount == 0` (or `hang == true`), the source program returns normally (or
  diverges silently in `loop {}`), whereas the target program panics or traps in
  the preheader!

#### 4.3 Architectural Prevention in Anneal's `trusted/` Primitives

Anneal's `EventualBehaviorOf` primitive (`Trusted/StepResult.lean`) makes silent
divergence a first-class, non-deletable semantic outcome:

1. **Bidirectional Divergence Preservation (`EventualOut.diverges`):**
   In `EventualBehaviorOf`, `EventualOut Obs Val` is the disjoint sum:
   ```lean
   inductive EventualOut (Obs Val : Type) where
     | terminated (trace : List Obs) (term : Terminal Val)
     | diverges
   ```
   A machine state $s$ has outcome `.diverges` iff $\forall n : \mathbb{N},\;
   \exists s',\; \text{StepsN } M\; n\; s\; (.running\; s')$. Under `Compiles`,
   every outcome produced by the target `t` on a defined source query `q` must
   decode (`codec.decodeOut o₂ = some o₁` with `idCodec`) to a valid outcome of
   the source `s`.
   - If the source program `s` diverges (`s` only produces `.diverges` on query
     `q`), any target `t` that deletes the infinite loop and terminates with
     `.terminated trace term` produces an outcome `.terminated ... ∉ {.diverges}`,
     **immediately falsifying `Compiles`** (`infinite_loop_deletion_violates_compiles`
     in `support/MidLevelIrFailureCanaries.lean`)!
   - Conversely, if `s` terminates (`s` only produces `.terminated trace term`),
     any target `t` that introduces a new infinite loop produces `.diverges ∉
     {.terminated trace term}`, also falsifying `Compiles`.
   - Furthermore, under `ProductiveOn`, a diverging loop cannot be replaced by
     an empty (`unreachable`) behavior `fun _ => False` because `ProductiveOn`
     enforces Dijkstra's Law of the Excluded Miracle ($\exists o,\; B(q)(o)$).
2. **Preventing Premature Panics / Traps When Hoisting Across Loops (`LICM` /
   `PRE`):** In `MirSemantics.lean` and `EventualBehaviorOf`, a Rust panic
   (`.terminated trace (.panic msg)`) has a distinct `SemObs` from normal return
   (`.terminated trace (.normal ())`) and from `.diverges`, while hardware
   division-by-zero traps (`.failed .ub`) make `defined = False`. Consequently,
   hoisting `a / d` into a preheader when `s` would have taken 0 iterations or
   diverged in `loop {}` on `d = 0` is provably rejected by `Compiles`
   (`licm_hoisting_trapping_div_above_zero_trip_or_diverging_loop_rejected` in
   `support/MidLevelIrFailureCanaries.lean`).

---

### Finding 5: SSA Destruction (`Lost-Copy` and `Swap` Bugs), Tail-Call Stack-Escape Corruption, and Drop-Elaboration / Unwind Safety Failures

`Basis: source + execution + derived`

#### 5.1 The Briggs/Boissinot `Lost-Copy` and `Swap` Bugs in Naive SSA Destruction (`SPE 1998`, `JAR 2008`, `CGO 2009`)

When lowering a program out of Static Single Assignment (`SSA`) or
block-argument `AnSSA` form (`Goto(bb, [e₁, ..., e_k])`) into mutable registers
or stack slots, all $\phi$-functions (or block parameters) at a basic-block entry
must execute **simultaneously as a parallel assignment** $(x_1, \dots, x_k) :=
(v_1, \dots, v_k)$, reading every right-hand side $v_i$ before any left-hand
side $x_j$ is overwritten.

Cytron et al.'s original out-of-SSA algorithm (TOPLAS 1991) placed sequential
copy instructions `x_i = v_i` at the end of each predecessor block. As Briggs,
Cooper, Harvey, and Simpson (*Practical Improvements to the Construction and
Destruction of Static Single Assignment Form*, SPE 1998, DOI
`10.1002/(SICI)1097-024X(199807)28:8<859::AID-SPE175>3.0.CO;2-Z`) and
Boissinot, Darte, Dupont de Dinechin, Guillon, and Rastello (*Revisiting
Out-of-SSA Translation for Correctness, Code Quality, and Efficiency*, CGO 2009,
DOI `10.1109/CGO.2009.19`) proved, naive predecessor copy placement fails on two
classic control-flow patterns:

1. **The `Swap` Bug (Cyclic Parallel Moves on Loop Backedges):**
   Suppose a loop header block `bb_hdr(a, b)` receives a backedge transfer
   `Goto(bb_hdr, [b, a])` (or two $\phi$-nodes `a₂ = φ(a₁, b₂); b₂ = φ(b₁, a₂)`
   after live-range coalescing maps `a₁, a₂` to register `a` and `b₁, b₂` to
   register `b`). Lowering the parallel edge transfer `(a, b) := (b, a)`
   naively into the sequential assignments:
   ```text
   a := b;
   b := a;   // BUG: reads the newly overwritten `a` (which is now `b`)!
   ```
   clobbers `a` on the first move, leaving both `a` and `b` holding the initial
   value of `b`! More generally, any directed permutation cycle of length $c \ge 2$
   in the parallel-move dependency graph requires either a scratch register
   (`tmp := a; a := b; b := tmp`) or a hardware swap instruction (`xchg`), as
   mechanized in Coq by Rideau, Serpette, and Leroy (*Tilting at Windmills with
   Coq: Formal Verification of a Compilation Algorithm for Parallel Moves*, JAR
   2008, DOI `10.1007/s10817-008-9097-3`).
2. **The `Lost-Copy` Bug (Critical Edges + Copy Folding):**
   Suppose a loop body computes `x₂ = x₁ + 1` and ends with a conditional branch
   `if (p) goto bb_hdr else goto bb_exit`, where `bb_hdr` has $\phi$-node
   `x₁ = φ(x₀, x₂)` and `bb_exit` uses the pre-increment value `x₁`! Because
   the edge from the loop latch to `bb_hdr` shares a predecessor with `bb_exit`
   (a critical edge when `bb_exit` also has other predecessors), inserting the
   backedge copy `x₁ := x₂` at the end of the loop latch *before* the conditional
   branch overwrites `x₁` on the path to `bb_exit`! When the loop exits,
   `bb_exit` observes `x₂` instead of `x₁` (the old copy of `x₁` was lost).

#### 5.2 Tail-Call Stack-Escape Corruption (`LLVM tailcallelim` / `AllocaDerivedValueTracker`)

Tail-Call Optimization (`TCO` / sibling-call elimination / `tailcallelim` in
LLVM and `become` in Rust MIR) replaces a call-followed-by-return sequence
`dest = Call(f, args); Return(dest)` with a direct frame-reusing jump (`TailCall`
or a loop backedge to the entry block for tail recursion), deallocating or
overwriting the caller's stack frame *before* `f` executes.

In LLVM's `TailRecursionElimination.cpp` (`tailcallelim`), historical
miscompilations occurred whenever `AllocaDerivedValueTracker` failed to detect
that a pointer derived from a stack local (`alloca` or an incoming `byval`
stack copy) escaped into the tail-called function's arguments or a global:

```rust
fn caller(n: usize) -> u64 {
    let local_buf: u64 = 99;
    // If `callee(&local_buf)` is lowered to a frame-reusing TailCall,
    // `caller`'s stack frame is popped/reused BEFORE `callee` reads `*ptr`!
    callee(&local_buf, n)
}
```

When `caller`'s stack frame is reused by `callee`'s prologue (or overwritten by
the next loop iteration in tail-recursion elimination), `callee` dereferences a
dangling stack pointer (`&local_buf`), reading its own spilled registers or
return address instead of `99`.

#### 5.3 Drop Elaboration, Unwind Double-Drops, and the `Drop` Leakpocalypse (`rust-lang/rust#24292`, `ElaborateDrops`)

High-level Rust lowering must also desugar scope-based destructors (`Drop::drop`)
and collection iterators across both normal control flow and stack unwinding:

1. **Unwind Double-Drop and Missing Drop-Flag Updates (`ElaborateDrops`):**
   In pre-elaboration MIR, a variable `x` may be conditionally moved out on one
   branch (`if cond { consume(x); }`) and dropped at scope exit. `rustc`'s
   `ElaborateDrops` pass lowers conditional drops by introducing runtime boolean
   stack drop flags (`drop_flag_x : bool`), setting `drop_flag_x = true` on
   initialization, `drop_flag_x = false` before moving or dropping `x`, and
   guarding the cleanup landing pad with `if drop_flag_x { drop_in_place(&mut x) }`.
   If a pass clears `drop_flag_x = false` *after* calling `drop_in_place(&mut x)`
   instead of *before*, or omits updating the flag on an unwind edge when
   dropping field `s.a` of a struct panics during unwinding, the unwind landing
   pad drops `s.a` a **second time** (double-free UB)! Furthermore, if `s.b`'s
   destructor *also* panics while the thread is already unwinding from `s.a`'s
   panic, failing to transition to immediate process `.abort` (Rust's
   double-panic rule) corrupts the unwinder state.
2. **The "Leakpocalypse" (`rust-lang/rust#24292`) and `Vec::drain` Exception
   Safety:** In 2015 (`#24292`), the Rust project discovered that `std::thread::scoped`
   (`JoinGuard`) and `Vec::drain` assumed their `Drop` implementation was
   guaranteed to run before the enclosing function returned. Because safe Rust
   can construct an `Rc<RefCell<...>>` reference cycle (or call `mem::forget`)
   to leak any value without running `Drop`, leaking a pre-fix `Vec::drain`
   iterator left the parent `Vec`'s `len` unchanged after elements had already
   been moved out of its backing buffer—causing safe code after `drain` to read
   uninitialized/already-dropped memory (use-after-free)! Fixing `#24292`
   required `Vec::drain` to set `self.set_len(start)` **before** handing out the
   `Drain` iterator (the "pre-pooping your pants" invariant) so that even if
   `Drain::drop` never runs (or a user callback panics mid-iteration), the
   `Vec`'s `AdtInv` (`initialized_prefix >= len`) remains valid at every external
   observation point.

#### 5.4 Architectural Prevention in Anneal's `trusted/` Primitives

Each of these lowering and cleanup hazards is caught directly by Anneal's four
primitives:

1. **Catching `Swap` and `Lost-Copy` via `Compiles L_AnSSA L_MIR` and
   `EventualBehaviorOf`:** In `SSADestructCertifier`, the source `AnSSA` machine
   executes parallel block-argument assignment atomically in $1$ step, while the
   target `MirMachine` executes the lowered sequential move list in $k + 1$
   steps (`EventualBehaviorOf` absorbs the $1 \to k + 1$ step dilation). When a
   parallel swap `(a, b) := (b, a)` is lowered without a scratch temporary into
   `a := b; b := a`, executing those 2 steps in `MirMachine` produces final
   state `(b, b) ≠ (b, a)`, refuting `Compiles`
   (`naive_ssa_swap_lowering_violates_compiles` and
   `temp_ssa_swap_lowering_satisfies_compiles` in
   `support/MidLevelIrFailureCanaries.lean`).
2. **Blocking Tail-Call Stack Escape via `StorageDead` Frame Deallocation:**
   In `MirMachine`, deallocating the caller's stack frame before a `TailCall`
   marks every caller stack `AllocId` as deallocated (`StorageDead`). If a
   pointer to any caller local was passed in `args` to the tail callee, the
   callee's first dereference of that pointer hits a deallocated `AllocId` and
   transitions to `.failed .ub`, falsifying `Compiles`
   (`tail_call_with_escaping_stack_ref_violates_compiles` in
   `support/MidLevelIrFailureCanaries.lean`).
3. **Catching `ElaborateDrops` Double-Drops and `Vec::drain` Leak/Unwind Bugs:**
   In `MirMachine`, dropping an already-dropped place transitions to
   `.failed .ub`, while `StepResult.externalCall` checks `AdtInv` at every open
   call boundary (`#24292`). If `Vec::drain` fails to set `vec.len = start`
   before yielding to a caller loop body or panicking callback (or if
   `ElaborateDrops` fails to clear `drop_flag` before invoking `Drop::drop`),
   the resulting state violates `AdtInv` or double-drops on unwind, refuting
   `Compiles` (`drop_elaboration_clear_after_drop_double_frees_on_unwind` in
   `support/MidLevelIrFailureCanaries.lean`).

---

### Finding 6: Translation Validator, Credible Compilation, and C-to-Rust Lifting Limitations

`Basis: source + documentation + execution + derived`

#### 6.1 `Alive2`: Bounded Loop Unrolling (`-tv-unroll=k`) and SMT Bitvector Timeouts (`PLDI 2021`)

Lopes et al. (*Alive2: Bounded Translation Validation for LLVM*, PLDI 2021,
§§1, 7, DOI `10.1145/3453483.3454030`) demonstrated that SMT-backed translation
validation is extraordinarily effective at finding LLVM bugs, but faces two
fundamental architectural boundaries when used as a verification gate:

1. **Bounded Loop Unrolling Misses Loop-Carried Miscompilations Past Bound $k$:**
   Because Alive2 lowers CFG validation directly to loop-free SMT queries
   without synthesizing or checking inductive loop invariants, it unrolls loops
   to a fixed small bound $k$ (by default $k = 1$ or $k = 2$ in routine runs).
   Any optimization bug that only manifests when a loop executes $> k$
   iterations—such as an Induction-Variable Strength Reduction (`IVSR`) wrap
   bug, a loop-vectorization (`Simd<T, W>`) tail-lane overwrite on iteration
   $W + 1$, or a wrong trip-count mask—falls outside the unrolled formula and
   is silently accepted as "no counterexample found within bound $k$."
2. **SMT Solver `timeout` / `unknown` on Nonlinear Arithmetic, Floating-Point,
   and Wide Vectors:** Encoding 64-bit integer multiplication/division, IEEE-754
   floating-point associative reductions, or 256/512-bit SIMD shuffle networks
   into monolithic `QF_ABV` / `QF_FPBV` SMT queries frequently causes Z3 to
   return `timeout` or `unknown`. Furthermore, trusting an external C++ SMT
   solver's unverified `unsat` answer places the entire 500k-LoC solver inside
   the Trusted Computing Base (TCB).

#### 6.2 `Crellvm` Proof-Hint Maintenance Collapse (`PLDI 2018`) and `Vellvm` Pass-Coverage Limits (`ICFP 2021`)

To avoid both bounded unrolling and SMT timeouts, Kang et al. (*Crellvm:
Verified Credible Compilation for LLVM*, PLDI 2018, DOI
`10.1145/3192366.3192398`) built a Coq-verified Relational Hoare Logic (`RHL`)
proof checker for LLVM IR and modified C++ LLVM passes (`GVN`, `LICM`, `SROA`,
`InstCombine`) to emit step-by-step **proof hints** (`Hint`) as they mutated
the IR. While Crellvm successfully verified pass runs with a small Coq TCB, the
architecture suffered from a fatal software-engineering failure mode:

- **Intrusive C++ Pass Instrumentation vs. Upstream LLVM Churn:** Every minor
  refactoring inside LLVM's C++ pass implementations (such as changing helper
  traversal order in `GVN.cpp` or `SROA.cpp` across LLVM point releases) broke
  the tightly coupled C++ hint-generation hooks. Maintaining invasive instrumentation
  inside millions of lines of fast-moving C++ LLVM code proved unsustainable,
  leading to the abandonment of the instrumented LLVM fork after LLVM 3.9/7.0.
- **Vellvm's Full-Pass Verification Gap (`ICFP 2021`):** Conversely, Zakowski
  et al. (*Modular, Compositional, and Executable Formal Semantics for LLVM IR*,
  ICFP 2021, DOI `10.1145/3473572`) mechanized a modular Interaction Trees
  (`ITree`) semantics for sequential LLVM IR (`Vellvm`), enabling foundational
  proofs of small reference passes (`helix`, simple constant folding). However,
  proving full production optimization passes directly over monadic `ITree`
  denotations requires re-implementing the entire compiler pass inside Rocq/Coq
  and proving manual simulation lemmas for every case—which cannot validate
  external Rust/C++ compiler passes (`rustc`, `regalloc2`, `isl`, `egg`)
  without a certificate-checking bridge.

#### 6.3 `C2Rust` and `CROWN` Ownership-Lifting Failures and Cross-Language Refinement Vacuity (`CAV 2023`)

In C-to-Rust migration, syntactic transpilers (`C2Rust`) translate C pointer
code into `unsafe extern "C"` Rust using raw pointers (`*mut T`). Ownership-guided
refactoring tools such as `CROWN` (Zhang et al., *Ownership Guided C to Rust
Translation*, CAV 2023, DOI `10.1007/978-3-031-37709-9_22`) solve global
ownership and mutability constraints to rewrite `*mut T` into safe `Box<T>`,
`Option<&mut T>`, and slices `&mut [T]`. Historical experience with `C2Rust` and
`CROWN` exposes three critical verification failures when certifying C-to-Rust
translations:

1. **Inability to Lift C `union`s, Non-Tree Aliasing (Cyclic/Doubly-Linked
   Lists), Pointer Arithmetic, and Variadics:** Whenever a C struct uses an
   untagged `union`, performs sub-object pointer arithmetic (`container_of`), or
   shares mutable aliases across non-tree graphs, `CROWN`'s ownership solver
   cannot assign unique Rust `&mut` ownership and either aborts lifting or falls
   back to unverified `unsafe` raw-pointer blocks.
2. **The Vacuous C-Source UB Trap (`signed` Overflow / Uninitialized Read):**
   Suppose a verifier checks only `Compiles L_Clight L_MIR cToRustCodec f_c f_rust`
   (`L_MIR.sem f_rust ≤ codec (L_Clight.sem f_c)`). If `f_c` contains an
   unintended C Undefined Behavior bug on its input domain (for example, signed
   integer overflow `x + 1` at `x = INT_MAX`, or a missing null precondition),
   then `L_Clight.sem f_c q` is `.undefined` (`defined = False`). Because
   refinement `≤` has `L_Clight.sem f_c q).defined` as its antecedent, **`Compiles`
   holds vacuously even if `f_rust` immediately triggers Rust UB or formats the
   hard drive**!
3. **The `(NULL, 0)` C Buffer vs. Non-Null Rust Slice `&[T]` UB Mismatch:**
   In C, passing `(ptr = NULL, len = 0)` to a function that loops `for (size_t
   i = 0; i < len; i++)` is **100% well-defined** as long as `ptr` is never
   dereferenced (and C-2023 `N3322` even legalizes `ptr + 0` on `NULL`). When an
   automated C-to-Rust lifter translates `(const uint8_t *ptr, size_t len)` into
   a safe Rust slice parameter `&[u8]` constructed at the FFI boundary via
   `unsafe { core::slice::from_raw_parts(ptr, len) }`, passing `(NULL, 0)`
   triggers **immediate Rust Undefined Behavior** because Rust slice references
   `&[T]` are required to be non-null and aligned (`NonNull::dangling()`) even
   when `len == 0`!

#### 6.4 Architectural Prevention in Anneal's `trusted/` Primitives

Anneal's architecture resolves all three classes of validator and lifter
failures:

1. **Unbounded Inductive Certificates + Kernel-Checked `LRAT`/`Farkas` Instead
   of Bounded SMT (`Alive2`) or Invasive C++ Hooks (`Crellvm`):**
   - Unlike `Alive2`, Anneal never bounds loop iterations in `trusted/`:
     `EventualBehaviorOf` quantifies over **all** step counts $n \in \mathbb{N}$
     (`∃ n` for `.terminated`, `∀ n` for `.diverges`). Loop optimizations
     (`LICM`, `LoopUnroll`, `PolyhedralScheduleValidator`, `IVSR`) supply
     unbounded inductive loop invariants or Farkas affine schedule certificates
     checked in `theory/`.
   - Unlike `Crellvm`, Anneal does not instrument C++ passes with fragile step
     hooks: external solvers and optimizers emit compact, pass-agnostic boundary
     certificates (`Mem2RegCert`, `GVNCert`, `PolyhedralCert`, `LRAT`, `Alethe`)
     checked by total, `native_decide`-free Lean 4 validators in `theory/`. Any
     instruction or loop where an external tool times out or cannot produce a
     certificate is either left unoptimized (backed by `NaiveCodegen`) or
     surfaced as a positive per-obligation entry in `VerificationResult`.
2. **Blocking C-to-Rust Vacuity and `(NULL, 0)` Slice UB via Proof-Gated
   Compilation (`InhabitedPre ∧ ProductiveOn ∧ Compiles`):**
   - Requiring `InhabitedPre cPre ∧ L_Clight.ProductiveOn cPre f_c ∧ Compiles
     L_Clight L_MIR cToRustCodec f_c f_rust` mandates a proof that `cPre` is
     non-empty and that the C source `f_c` is **genuinely UB-free and
     productive** on every query satisfying `cPre` (`c2rust_vacuous_c_ub_blocked_by_productiveOn`
     in `support/MidLevelIrFailureCanaries.lean`).
   - Furthermore, `cToRustCodec.encodeQuery` maps C `(ptr, len)` inputs into
     `MirState`, where constructing `&[T]` with `ptr == 0` and `len == 0` fails
     `MirMachine`'s slice non-null validity guard (`.failed .ub`), immediately
     refuting `Compiles` unless `cPre` excludes `ptr == NULL` or the wrapper
     substitutes `NonNull::dangling()` when `len == 0`
     (`c2rust_null_zero_len_slice_violates_compiles` in
     `support/MidLevelIrFailureCanaries.lean`).

---

### Finding 7: Cross-Cutting Architectural Synthesis: How Anneal's Four `trusted/` Primitives Prevent All Fifteen Historical Failure Classes

`Basis: source + execution + derived`

#### 7.1 Master Failure Postmortem and Prevention Matrix

Across all fifteen historical failure classes examined in Findings 1–6, every
miscompilation or verification failure traces back to violating one or more of
four semantic invariants that Anneal enforces directly in `trusted/lean/`:

1. **`Language SemObs` + `BehaviorCodec` + `Compiles` / `Abstracts`
   (`Trusted/Refinement.lean`):** Enforces a reflexive, transitive partial-behavior
   refinement preorder `L₂.sem t ≤ codec.toMorphism (L₁.sem s)` with partial
   bijective outcome decoding (`decodeOut_encodeOut`, `encodeOut_decodeOut`,
   `obs_decodeOut`).
2. **`ProductiveOn` + `InhabitedPre` (`Trusted/Refinement.lean`):** Enforces
   non-empty input domains (`∃ q, pre q`) and Dijkstra's Law of the Excluded
   Miracle (`∀ q, pre q → ∃ h : defined, ∃ o, val h o`), blocking vacuous
   source-UB refinement and empty-behavior miracles.
3. **`SmallStepMachine` + `EventualBehaviorOf` + `StepResult.externalCall`
   (`Trusted/StepResult.lean`):** Separates finite-trace termination
   (`.terminated trace term`, existential step count `∃ n`) from silent
   divergence (`.diverges`, universal step count `∀ n`) and enforces immediate
   call-site boundary invariants (`boundaryInv : Bool`) and frame/protector
   preservation across opaque calls (`branches : State → Prop`).
4. **Positive Per-Obligation `VerificationResult` (`Trusted/Refinement.lean`):**
   Tracks every pass side-condition, non-trapping guard, layout disjointness
   check, and anti-degeneracy cost/normal-form predicate as an isolated positive
   consequent obligation without antecedent `False.elim` explosion.

| # | Historical Failure Class | Primary Source / Issue | Technical Root Cause | Governing Anneal `trusted/` Primitive(s) | Mechanized Canary in `support/MidLevelIrFailureCanaries.lean` |
| :- | :--- | :--- | :--- | :--- | :--- |
| **1** | `LoopUnswitch` + `GVN` on `undef` / `poison` | Lee et al., PLDI 2017 (`10.1145/3062341.3062343`); LLVM PR21467, PR31632 | Per-use `undef` + branching on unguarded `poison` makes `GVN ∘ LoopUnswitch` non-transitive and introduces UB on 0-trip loops | `Compiles` (`≤ᵇ` transitive preorder) + `Partial.defined` preservation | `loopUnswitch_without_freeze_violates_compiles` (`L165-173`), `loopUnswitch_with_freeze_satisfies_compiles` (`L176-188`) |
| **2** | `select`-to-branch & `InstCombine` poison leaks | Lopes et al., PLDI 2021 (`10.1145/3453483.3454030`) | Lowering `select c, a, b` to `br c` turns value-level `poison` into immediate control-flow UB | `Compiles` (`(L₁.sem s q).defined → (L₂.sem t q).defined`) | `loopUnswitch_without_freeze_violates_compiles` (`L165-173`) |
| **3** | `ptrtoint` / `inttoptr` + `GVN` provenance collapse | Lee et al., OOPSLA 2018 (`10.1145/3276495`); LLVM PR34548, PR35229 | Substituting `p + 1` for `q` under numeric `ip == iq` replaces valid `AllocId(q)` provenance with out-of-bounds `AllocId(p)` | `MirVal.ref (allocId, offset)` provenance separation + `Compiles` | `gvn_provenance_substitution_rejected` (`L213-219`) |
| **4** | `rustc` `mutable-noalias` on `!Unpin` generators / `Future`s | `rust-lang/rust#54878`, `#63818`, `#63934` | Emitting LLVM `noalias` on `Pin<&mut Self>` treats self-referential interior pointers loaded from `*self` as non-aliasing | Post-cleanup MIR capture + `ProductiveOn` pinning precondition + Tree Borrows tags | `coroutine_overlapping_live_fields_rejected` (`L256-265`) |
| **5** | `rustc` MIR `GVN` & `ConstProp` aliasing / partial-move bugs | `rust-lang/rust#110947`, `#118328`, `#120613`, `#141038` | Syntactic place value-numbering reuses moved fields (`#120613`), ignores mutating borrows (`#110947`), or creates overlapping copies (`#141038`) | Operational `MirMachine` state + `Compiles L_MIR L_MIR` | `gvn_provenance_substitution_rejected` (`L213-219`) |
| **6** | Coroutine `StorageLive` / `StorageDead` yield overlap | `rust-lang/rust#63616`, `#146383` (`DestinationPropagation`) | Desynchronized `StorageLive` ranges pack co-live locals into identical union offsets across `Yield` | `Compiles L_CoroutineMIR L_MIR` + cross-yield liveness disjointness check | `coroutine_overlapping_live_fields_rejected` (`L256-265`) |
| **7** | Stacked / Tree Borrows DSE across diverging `externalCall` | Jung et al., POPL 2020; Villani et al., PLDI 2025; `Simuliris` (`e3abfcdc`) | Deleting `*x = 1` before `ext(); *x = 2` is unsound if `ext()` reads an alias and diverges (`loop {}`) under a `Weak` or `Reserved` protector | `StepResult.externalCall` + `EventualOut.diverges` + `Strong` active protector framing | `dse_across_diverging_call_unsound_under_weak_or_unactivated_protector` (`L314-325`), `dse_across_diverging_call_sound_under_strong_active_protector` (`L329-338`) |
| **8** | Forward-progress infinite-loop deletion (`loop {}`) | `rust-lang/rust#28728`, `#81255`, `#83359` (LLVM `mustprogress`) | C++ `[intro.progress]` assumption deletes side-effect-free `loop {}` and falls through into `unreachable` | `EventualBehaviorOf` (`EventualOut.diverges` bidirectional preservation) + `ProductiveOn` | `infinite_loop_deletion_violates_compiles` (`L359-368`) |
| **9** | `LICM` / `PRE` hoisting trapping ops above 0-trip or diverging loops | Knoop et al. (`PRE`); `Chamois-CompCert` (`BTL`); Sub-Domain 3.6 & 3.13 | Hoisting `a / d` into a preheader introduces a panic/trap when the loop takes 0 iterations or diverges before `a / d` | `EventualOut` (`Terminal.panic` vs. `.normal` vs. `.diverges`) + `Compiles` | `licm_hoisting_trapping_div_above_zero_trip_or_diverging_loop_rejected` (`L390-399`) |
| **10** | Briggs/Boissinot `Swap` and `Lost-Copy` out-of-SSA bugs | Briggs et al., SPE 1998; Rideau et al., JAR 2008; Boissinot et al., CGO 2009 | Naive sequentialization of $\phi$-cycles (`a := b; b := a`) or unsplit critical edges overwrites live registers | `Compiles L_AnSSA L_MIR` + `EventualBehaviorOf` ($1 \to k+1$ step dilation) | `naive_ssa_swap_lowering_violates_compiles` (`L429-438`), `temp_ssa_swap_lowering_satisfies_compiles` (`L441-446`) |
| **11** | Tail-call elimination (`TCO`) stack-local address escape | LLVM `TailRecursionElimination.cpp` (`AllocaDerivedValueTracker`) | Reusing caller stack frame when `&local` or `byval` escapes to tail callee causes dangling stack dereference | `MirMachine` frame deallocation (`StorageDead`) before `TailCall` + `Compiles` | `tail_call_with_escaping_stack_ref_violates_compiles` (`L463-469`) |
| **12** | `ElaborateDrops` unwind double-drop & `#24292` Leakpocalypse | `rust-lang/rust#24292` (`Vec::drain`, `JoinGuard`); MIR `ElaborateDrops` | Clearing `drop_flag` after `Drop::drop` double-frees on panic unwind; leaking `Drain` leaves stale `Vec::len` | `MirMachine` drop-flag state + `StepResult.externalCall` `AdtInv` check | `drop_elaboration_clear_after_drop_double_frees_on_unwind` (`L489-495`) |
| **13** | `Alive2` bounded unrolling (`-tv-unroll=k`) & SMT timeouts | Lopes et al., PLDI 2021 (`10.1145/3453483.3454030`) | Bounded loop unrolling misses bugs at iteration $k+1$; monolithic `QF_ABV`/`QF_FPBV` queries time out | Unbounded `EventualBehaviorOf` (`∀ n` / `∃ n`) + kernel-checked `Farkas`/`LRAT` certificates | `Behavior.Refines.trans` (lines 49-56) |
| **14** | `Crellvm` proof-hint fragility & `Vellvm` pass-coverage gap | Kang et al., PLDI 2018 (`10.1145/3192366.3192398`); Zakowski et al., ICFP 2021 (`10.1145/3473572`) | Invasive C++ pass instrumentation breaks on LLVM upgrades; monadic `ITree` proofs require rewriting passes in Rocq | Pass-agnostic boundary certificates checked in `theory/` + `VerificationResult` | `BehaviorCodec.toMorphism` (lines 84-92) |
| **15** | `C2Rust` / `CROWN` C-UB vacuity & `(NULL, 0)` slice UB | Zhang et al., CAV 2023 (`10.1007/978-3-031-37709-9_22`) | Source C UB makes `Compiles` hold vacuously; translating valid C `(NULL, 0)` to `slice::from_raw_parts(null(), 0)` introduces Rust UB | `InhabitedPre ∧ ProductiveOn ∧ Compiles` + `cToRustCodec` non-null slice guard | `c2rust_vacuous_c_ub_blocked_by_productiveOn` (`L515-520`), `c2rust_null_zero_len_slice_violates_compiles` (`L551-559`) |

## Boundaries

### Part I Boundaries — Real-World Verification Tools

The following scope boundaries and negative-space qualifications govern this
report:

- **Not examined (`not examined`):**
  - Low-level machine-instruction selection, physical register allocation
    (`regalloc2`), hardware instruction scheduling, object-file linking (`ELF`),
    and binary lifting (`McSema`/`FoxDec`). Those backend and binary passes are
    covered in Sub-Domain 4 rather than this mid-level IR report.
  - Pre-macro AST expansion (`rustc_expand`), trait solver coherence
    (`Chalk` / `next-solver`), and borrow-checker region inference (`Polonius`),
    which operate prior to `Runtime(PostCleanup)` MIR capture or in Sub-Domain 1.
- **Known not to apply (`known not to apply`):**
  - **Symmetric behavioral equivalence (`L₂.sem t = L₁.sem s`) as a general
    compiler pass correctness criterion:** As proven in
    `mem2reg_uninit_not_symmetric` and `inline_protector_not_reversible` in
    [MidLevelOptimizationAndLoweringProbes.lean](support/MidLevelOptimizationAndLoweringProbes.lean),
    standard mid-level passes (`mem2reg`, Tree Borrows read elimination, function
    inlining, heap-to-stack OOM refinement, and C-to-Rust signed-overflow
    lowering) strictly reduce Undefined Behavior or demonic nondeterminism and
    therefore satisfy directional refinement (`Compiles`, `≤`) while violating
    reverse refinement (`≥`).
  - **Unconditional deletion of unused Rust arithmetic or indexing operations in
    `DCE`:** Unlike LLVM `nsw`/`nuw` poison (which is side-effect free until
    observed by a branching/memory sink), Rust MIR integer division (`Div`/`Rem`),
    checked arithmetic (`CheckedBinOp`), and slice bounds assertions (`Assert`)
    produce defined `.unwind` panics with observable unwinding side effects.
    Treating them as pure dead-code-eliminable expressions without a
    dominating non-zero / in-bounds proof is unsound (`dce_panicking_div_unsound`).
  - **Identity query mapping for C `(NULL, 0)` buffers to Rust `&[T]` slices:**
    Mapping a C `(ptr, len)` pair directly to a Rust slice `&[T]` without a
    non-null precondition or `(NULL, 0) ↦ (NonNull::dangling(), 0)` canonicalizer
    is unsound (`c2rust_null_empty_slice_rejected_under_idCodec`).
- **Unsupported (`unsupported`):**
  - **Strict bitwise IEEE-754 floating-point equality under unguarded SIMD
    horizontal reduction reassociation or reverse-mode AD adjoint summation:**
    Because IEEE-754 floating-point addition is non-associative, passes that
    reassociate floating-point reductions (`SLP`/`LoopVectorize` horizontal
    sums or out-of-order adjoint accumulations) cannot satisfy bitwise identity
    `Compiles` unless the source specification explicitly relaxes `Out` to an
    $\varepsilon$-ball or `reassoc` nondeterministic choice set.

### Part II Boundaries — Historical Verification Failures

To prevent future agents from over-generalizing these findings, the following
scope boundaries apply:

- **Not examined — Hardware relaxed-memory concurrency interactions with
  mid-level scalar passes:** While Finding 3 analyzes sequential and re-entrant
  call-boundary protectors (`Stacked Borrows` / `Tree Borrows`), the interaction
  between mid-level load/store motion and weak hardware memory models (`C-2011`
  `Relaxed`/`Release`/`Acquire`, `x86-TSO` store buffers, and `AArch64`/`RVWMO`
  out-of-order execution) is **not examined** in this package; it is covered in
  `anneal-memory-bridge-weak-memory-atomics-constant-time-and-bare-metal-2026`.
- **Not examined — Low-level target-ISA peephole, instruction-selection, and
  ELF linker failures:** Failures specific to `x86-64`/`AArch64`/`RISC-V`
  condition-code fusion (`OF`/`CF`), register-allocator spill slot packing, and
  ELF relocation relaxation belong to Sub-Domain 4 and are **not examined** here.
- **Known not to apply — Symmetric equivalence (`=`) for borrow-aware and
  undef/poison-refining optimizations:** As established in Findings 1, 2, and 3
  (and Sub-Domain 3.10 and 3.17), optimizations such as `mem2reg` uninitialized-read
  refinement, Tree Borrows redundant-read elimination, and function inlining
  (which drops Function-Entry Protectors) make the target program strictly
  **more defined** than the source program (`L₂.sem t ≤ L₁.sem s` with strict
  inequality). Symmetric behavioral equivalence (`L₂.sem t = L₁.sem s`) is
  **known not to apply** to these passes; `Compiles` must remain an asymmetric
  refinement preorder (`≤`).
- **Unsupported — Uninstrumented translation validation of arbitrary C++ LLVM
  `-O3` loop passes without inductive invariants:** Neither `Alive2` (which is
  bounded at `-tv-unroll=k`) nor Anneal's certifying validators can validate an
  arbitrary loop-transforming pass without an inductive loop/schedule witness
  (`LICMCert`, `PolyhedralCert`, or `IVSR` recurrence invariant). When an
  external optimizer does not supply a valid certificate, unverified pass output
  is **unsupported** as a silent TCB step and must be either rejected (falling
  back to `NaiveCodegen`) or surfaced explicitly in `VerificationResult`.

## Evidence

### Part I Evidence — Real-World Verification Tools

### Preserved Mechanized Lean 4 Support Artifact

- **[MidLevelOptimizationAndLoweringProbes.lean](support/MidLevelOptimizationAndLoweringProbes.lean)**
  - **Lines:** `513`
  - **SHA-256:**
    `18181cc1058d2d7af77159f1c231789bb48024d089e6bd403e4a5390b9ee98e1`
  - **Verification Environment:** Verified on `2026-10-31` with
    `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) via
    `lean -DElab.async=false -Ddebug.skipKernelTC=false` (exit code `0`, zero
    warnings, zero `sorryAx`, zero `Lean.ofReduceBool`, zero `Classical.choice`).
  - **Mechanized Theorems (all 13 `#print axioms` checks report `does not depend on any axioms`):**
    1. `mem2reg_uninit_refines` (L201) and `mem2reg_uninit_not_symmetric` (L213)
    2. `dce_panicking_div_unsound` (L245) and `dce_guarded_div_compiles` (L272)
    3. `inline_drops_protector_refines` (L310) and `inline_protector_not_reversible` (L321)
    4. `dse_across_diverging_external_call_unsound_if_late_protector` (L355)
    5. `licm_trapping_zero_trip_unsound` (L395)
    6. `coroutine_pinned_productive` (L427) and `coroutine_unpinned_move_violates_safety` (L433)
    7. `c2rust_ub_source_vacuously_compiles_without_productiveOn` (L454),
       `c2rust_productiveOn_blocks_ub_source` (L461), and
       `c2rust_null_empty_slice_rejected_under_idCodec` (L492).

### Primary Source Coordinates and Literature Citations

- **Anneal Core & MIR-to-x86-64 Repositories (`joshlf/anneal`):**
  - `24367bd1a8c784f2578535954f9915e24894a56f`:
    `trusted/lean/Trusted/Refinement.lean` (lines 203–473),
    `trusted/lean/Trusted/StepResult.lean` (lines 55–200),
    `trusted/lean/Trusted/MirSemantics.lean` (lines 590–867).
  - `5fc1139f2208b3c9cfb513573c4a731cc32bb457`:
    `theory/Anneal/Compiler/NaiveCodegen.lean` (lines 38–299),
    `theory/Anneal/Compiler/Peephole.lean` (lines 45–205).
- **Rust Compiler (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`, `1.99.1`):**
  - `compiler/rustc_mir_transform/src/sroa.rs`,
    `compiler/rustc_mir_transform/src/gvn.rs`,
    `compiler/rustc_mir_transform/src/dataflow_const_prop.rs`,
    `compiler/rustc_mir_transform/src/dead_store_elimination.rs`,
    `compiler/rustc_mir_transform/src/jump_threading.rs`,
    `compiler/rustc_mir_transform/src/inline.rs`,
    `compiler/rustc_mir_transform/src/polymorphize.rs`,
    `compiler/rustc_mir_transform/src/coroutine.rs`,
    `compiler/rustc_mir_transform/src/elaborate_drops.rs`,
    `compiler/rustc_monomorphize/src/collector.rs`,
    `compiler/rustc_codegen_llvm/src/autodiff.rs`.
- **External Mechanized and Production Compiler Sources:**
  - `Alive2`: Lopes et al., PLDI 2021 (`10.1145/3453483.3454030`), `AliveToolkit/alive2`.
  - `Crellvm`: Kang et al., PLDI 2018 (`10.1145/3192366.3192377`), `snu-sf/crellvm`.
  - `Vellvm` / `VIR`: Zhao et al., POPL 2012 (`10.1145/2103656.2103709`) & PLDI 2013 (`10.1145/2491956.2462164`); Zakowski et al., ICFP 2021 (`10.1145/3473572`), `vellvm/vellvm`.
  - `CompCert`, `CompCertSSA`, & `Chamois-CompCert`: Leroy, CACM 2009 (`10.1145/1538788.1538814`); Tristan & Leroy, POPL 2008 (`10.1145/1328438.1328485`) & PLDI 2009 (`10.1145/1542476.1542512`); Rideau, Serpette, Leroy, JAR 2008 (`10.1007/s10817-007-9096-8`); Barthe, Demange, Pichardie, TOPLAS 2014 (`10.1145/2579080`); Demange, Pichardie, Stefanesco, CC 2015 (`10.1007/978-3-662-46663-6_5`); Gourdin et al., OOPSLA 2023 (`10.1145/3622840`).
  - `Peggy`, `egg`, `egglog`, & Cranelift `aegraphs`: Tate et al., POPL 2009 (`10.1145/1480881.1480915`); Willsey et al., POPL 2021 (`10.1145/3434304`); Zhang et al., PLDI 2023 (`10.1145/3591239`).
  - `Lean-MLIR`: Bhat, Keizer, Hughes, Goens, Grosser, ITP 2024, `opencompl/lean-mlir@ae0dd933` (`ITP24`).
  - `CakeML`: Tan et al., JFP 2019 (`10.1017/S0956796818000229`), `CakeML/cakeml`.
  - `Stacked Borrows`, `Tree Borrows`, `Miri`, & `SimulIris`: Jung et al., POPL 2020 (`10.1145/3371109`); Gäher et al., POPL 2022 (`10.1145/3498687`); Villani, Hostert, Dreyer, Jung, PLDI 2025 (`10.1145/3729269`), `rust-lang/miri`.
  - `PolyVerify`, `Pluto`, `VeGen`, & `Diospyros`: Bondhugula et al., PLDI 2008 (`10.1145/1375581.1375595`); Courant & Leroy, POPL 2021 (`10.1145/3434321`); Chen, Mendis, Amarasinghe, ASPLOS 2021 (`10.1145/3445814.3446692`); VanHattum et al., ASPLOS 2021 (`10.1145/3445814.3446707`).
  - `CertiCoq`, Maranget, `Enzyme`, `Tapenade`, & `SciLean`: Maranget, ML 2008 (`10.1145/1411304.1411311`); Hascoët & Pascual, TOMS 2013 (`10.1145/2450153.2450158`); Moses & Churavy, NeurIPS 2020 (`EnzymeAD/Enzyme`); Paraskevopoulou, Li, Appel, ICFP 2021 (`10.1145/3473591`); Skřivan, `lecopivo/SciLean`.
  - `SymDiff`, `LLReve`, `UC-KLEE`, `C2Rust`, `Laertes`, `CROWN`, & `TCE`: Ramos & Engler, CAV 2011 (`10.1007/978-3-642-22110-1_55`); Lahiri et al., CAV 2012 (`10.1007/978-3-642-31424-7_54`); Felsing et al., ASE 2014 (`10.1145/2642937.2642987`); Papadakis et al., ICSE 2015 (`10.1109/ICSE.2015.103`); Emre et al., OOPSLA 2021 (`10.1145/3485495`); Zhang, David, Yu, Wang, CAV 2023 (`10.1007/978-3-031-37706-8_23`).

### Part II Evidence — Historical Verification Failures

### Primary Anneal Repository Sources

- **`joshlf/anneal` (`trusted/lean` at `24367bd1a8c784f2578535954f9915e24894a56f`):**
  - `trusted/lean/Trusted/Refinement.lean`: Defines `Partial`, `Behavior`,
    `Language`, `BehaviorCodec`, `Compiles`, `ProductiveOn`, and
    `VerificationResultOn`.
  - `trusted/lean/Trusted/StepResult.lean`: Defines `StepResult`, `Terminal`,
    and prefix reachability (`ReachesPrefix`).
  - `trusted/lean/Trusted/MirSemantics.lean`: Defines `MirVal`, `MirState`,
    `MirSem`, and `EnsuresRetLibInv`.
- **`joshlf/anneal` (`MIR-to-x86-64` at `5fc1139f2208b3c9cfb513573c4a731cc32bb457`):**
  - `trusted/lean/Trusted/X86Semantics.lean`, `trusted/audit/TrustedBoundary.lean`,
    and `trusted/rustc-capture/src/lib.rs`.

### Primary Academic and Technical Sources

1. **Lee, Kim, Song, Hur, Das, Majnemer, Regehr, and Lopes (PLDI 2017):**
   *Taming Undefined Behavior in LLVM*, ACM SIGPLAN Notices 52(6), pp. 633–647,
   DOI `10.1145/3062341.3062343`. Establishes the mutual inconsistency of
   `GVN`, `LoopUnswitch`, and `SROA` under LLVM's pre-`freeze` `undef`/`poison`
   semantics (§§2–3) and formalizes the `freeze` instruction (§4).
2. **Lee, Hur, Jung, Liu, Regehr, and Lopes (OOPSLA 2018):** *Reconciling
   High-Level Optimizations and Low-Level Code in LLVM*, Proc. ACM Program.
   Lang. 2(OOPSLA), Article 125, DOI `10.1145/3276495`. Documents the
   `ptrtoint`/`inttoptr` + `GVN` + `InstCombine` adjacent-allocation provenance
   miscompilation (§2, LLVM PR34548 / PR35229) and formalizes twin-allocation
   memory semantics.
3. **Lopes, Lee, Hur, Liu, and Regehr (PLDI 2021):** *Alive2: Bounded
   Translation Validation for LLVM*, Proc. 42nd ACM SIGPLAN Conf. on
   Programming Language Design and Implementation, pp. 65–79, DOI
   `10.1145/3453483.3454030`. Documents `select`-to-branch poison UB bugs (§2),
   refinement semantics (§5), and bounded loop unrolling limitations (§7).
4. **Jung, Dang, Kang, and Dreyer (POPL 2020):** *Stacked Borrows: An Aliasing
   Model for Rust*, Proc. ACM Program. Lang. 4(POPL), Article 41, DOI
   `10.1145/3371109`. Introduces function-entry protectors for `&mut T` / `&T`
   across unknown calls (§4).
5. **Villani, Hostert, Jung, and Dreyer (PLDI 2025):** *Tree Borrows*, Proc. ACM
   Program. Lang. 9(PLDI), DOI `10.1145/3735592`, paired with the `Simuliris`
   mechanization (`https://gitlab.mpi-sws.org/iris/simuliris` at
   `e3abfcdc301f92250d4227fc03c00463bf57b982`). Establishes the distinction
   between `Strong` and `Weak` function-entry protectors and the soundness
   requirements for Dead Store Elimination across diverging external calls.
6. **Briggs, Cooper, Harvey, and Simpson (SPE 1998):** *Practical Improvements
   to the Construction and Destruction of Static Single Assignment Form*,
   Software: Practice and Experience 28(8), pp. 859–881, DOI
   `10.1002/(SICI)1097-024X(199807)28:8<859::AID-SPE175>3.0.CO;2-Z`. Identifies
   and names the `Lost-Copy` and `Swap` bugs in Cytron et al.'s out-of-SSA
   translation.
7. **Rideau, Serpette, and Leroy (JAR 2008):** *Tilting at Windmills with Coq:
   Formal Verification of a Compilation Algorithm for Parallel Moves*, Journal
   of Automated Reasoning 40(4), pp. 307–326, DOI `10.1007/s10817-008-9097-3`.
   Mechanizes the cycle-breaking parallel-move sequentialization algorithm used
   in CompCert.
8. **Boissinot, Darte, Dupont de Dinechin, Guillon, and Rastello (CGO 2009):**
   *Revisiting Out-of-SSA Translation for Correctness, Code Quality, and
   Efficiency*, Proc. 7th IEEE/ACM Int. Symp. on Code Generation and
   Optimization, pp. 114–125, DOI `10.1109/CGO.2009.19`. Proves that general
   coalescing during SSA destruction requires splitting critical edges and
   sequentializing parallel copies via dependency graphs.
9. **Kang et al. (PLDI 2018):** *Crellvm: Verified Credible Compilation for
   LLVM*, Proc. 39th ACM SIGPLAN Conf. on Programming Language Design and
   Implementation, pp. 631–645, DOI `10.1145/3192366.3192398`.
10. **Zakowski et al. (ICFP 2021):** *Modular, Compositional, and Executable
    Formal Semantics for LLVM IR* (`Vellvm`), Proc. ACM Program. Lang. 5(ICFP),
    Article 67, DOI `10.1145/3473572`.
11. **Zhang, David, Yu, and Wang (CAV 2023):** *Ownership Guided C to Rust
    Translation* (`CROWN`), LNCS 13965, pp. 459–482, DOI
    `10.1007/978-3-031-37709-9_22`.
12. **Upstream `rust-lang/rust` Issue Archive:**
    - `#24292` (*std::thread::scoped / JoinGuard and Vec::drain unsoundness when
      Drop is bypassed*);
    - `#28728`, `#81255`, `#83359` (*LLVM forward-progress infinite loop
      miscompilation and `mustprogress` / `willreturn` mitigation*);
    - `#54878`, `#63818`, `#63934` (*`noalias` miscompilations on `&mut` and
      self-referential generators / `Future`s*);
    - `#63616` (*partial initialization and storage-conflict overlap in
      generators*);
    - `#110947`, `#118328` (*MIR `ConstProp` miscompilations across mutating
      borrows and pointer-typed enum fields*);
    - `#120613`, `#141038` (*MIR `GVN` reuse of moved arguments and overlapping
      aliased assignments*); and
    - `#146383` (*MIR `DestinationPropagation` copy/lifetime miscompilation*).

### Preserved Package Artifacts

- [`support/MidLevelIrFailureCanaries.lean`](support/MidLevelIrFailureCanaries.lean):
  561-line standalone Lean 4.34.1 file mechanizing 13 zero-axiom failure-refutation
  and repair-conformance theorems across Findings 1–6 (observed and verified on
  2026-10-31).

## Revalidation

### Part I Revalidation — Real-World Verification Tools

Re-run the preserved Lean 4 probe and review this report's mappings whenever:

1. `trusted/lean/Trusted/Refinement.lean` or `trusted/lean/Trusted/StepResult.lean`
   changes `Partial`, `Language`, `BehaviorCodec`, `Compiles`, `Abstracts`,
   `ProductiveOn`, `VerificationResult`, `EventualBehaviorOf`, or
   `StepResult.externalCall`.
2. `trusted/lean/Trusted/MirSemantics.lean` adds Tree Borrows tag transitions,
   Function-Entry `Protector` state, or `Yield` coroutine resumption semantics.
3. A new mid-level optimization pass or validator in `theory/` (`MemToAnSSA`,
   `SROACertifier`, `GVNCertifier`, `LICMValidator`, `CoroutineLoweringValidator`,
   or `C2RustCertifier`) is wired into `trusted/rustc-capture`.

Deterministic kernel revalidation command from the package root:

```bash
lean \
  -DElab.async=false -Ddebug.skipKernelTC=false \
  support/MidLevelOptimizationAndLoweringProbes.lean
```

### Part II Revalidation — Historical Verification Failures

1. **Executable Lean 4.34.1 Kernel Revalidation (< 2 seconds):**
   Run the Lean 4 kernel checker with asynchronous elaboration and kernel-skip
   flags disabled on the preserved canary development:
   ```console
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     reports/anneal-mid-level-ir-optimizations-and-lowering-survey/support/MidLevelIrFailureCanaries.lean
   ```
   A zero exit code confirms that all 13 refutation and conformance theorems
   (`loopUnswitch_without_freeze_violates_compiles` through
   `c2rust_null_zero_len_slice_violates_compiles`) typecheck in the Lean 4
   kernel with zero axioms.
2. **Revalidating Against Future Changes to Anneal's `trusted/lean/` Primitives:**
   When `Trusted/Refinement.lean`, `Trusted/StepResult.lean`, or
   `Trusted/MirSemantics.lean` is modified, verify that:
   - `Compiles` still enforces `(L₁.sem s q₁).defined → (L₂.sem t (codec.encodeQuery q₁)).defined`
     and `decodeOut` outcome inclusion (Canaries 1a, 2, 3, 6a, 7a, 7b, 8b);
   - `EventualOut` still distinguishes `.diverges`, `.terminated trace (.normal v)`,
     `.terminated trace (.panic msg)`, and `.terminated trace .abort` in `SemObs`
     (Canaries 4a, 5a, 5b); and
   - `ProductiveOn` still requires `∃ h : (L.sem prog q).defined, ∃ o, (L.sem prog q).val h o`
     (Canary 8a).
