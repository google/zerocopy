# Historical Failures in Deductive Verification, Program Logics, Type Systems, and Abstract Interpretation: Root-Cause Postmortems and Architectural Defenses for Anneal

## Summary

Across three decades of deductive program verifiers (`Dafny`, `Verus`,
`Creusot`, `Prusti`, `Kani`, `Frama-C WP`, `Why3`, `Boogie`, `Viper`, `F*`,
`KeY`, `ESC/Java2`), separation logics and aliasing models (`RustBelt`,
`Stacked Borrows`, `Tree Borrows`, `Polonius`, LLVM/C pointer provenance), and
static abstract interpreters (the Linux kernel eBPF verifier, `Astrée`,
`Frama-C Eva`, `IKOS`, `MIRAI`), verification failures cluster into six
recurring structural root causes rather than isolated coding mistakes:

1. **Vacuous refinement via over-constrained prophecies, false assumptions, or
   demonic miracles:** A translation pass or intermediate verification language
   (IVL) emits an unsatisfiable assumption (`assume false`, an inconsistent
   prophecy resolution equation in `RustHorn`/`Creusot`, or an broken inhale
   encoding in `Viper`/`Boogie`), collapsing the post-state set to $\emptyset$
   and allowing any postcondition—including `ensures false`—to pass.
2. **Inconsistent prelude axioms and uninhabited refinement domains:** Background
   SMT preludes (`Dafny` `#6534`, `#6537`), VC simplifiers (`F*` `#4485`), or
   liquid refinement signatures (`x > 10 && x < 5`) make the entry precondition
   unsatisfiable, discharging universal safety claims over an empty domain.
3. **Antecedent waiver and trusted-boundary contamination:** Unverified helper
   specifications (`#[trusted]`, `admit()`, `external_body`, or waived
   obligations) injected as logical hypotheses in an implication antecedent
   ($H_{\text{waived}} \to G_{\text{verified}}$) silently discharge unrelated
   safety obligations whenever a waived hypothesis is inconsistent.
4. **Open-world callback re-entrancy and exceptional/unwind control-flow
   omissions:** Verifiers check representation invariants (`AdtInv`) only at
   normal function return while ignoring mid-method state during external
   closure callbacks (`Vec::dedup_by`, `RefCell`, `MutexGuard::map` in
   `rust-lang/rust#25760`) or along stack-unwinding edges (`Charon`
   `reconstruct_fallible_operations`, `KeY`/`ESC/Java2` abrupt termination).
5. **Operational aliasing and pointer-provenance mismatches:** Overly rigid
   aliasing models (`Stacked Borrows` rejecting valid two-phase borrows,
   `addr_of!`, and `Pin` patterns) cause false-positive UB rejections that force
   users into `#[trusted]` bypasses, while overly permissive flat-memory or
   round-trip cast folds (`llvm#34548`, `llvm#35229`, `PNVI` GVN+AA
   interactions) miscompile valid low-level pointer arithmetic.
6. **Unsound abstract transformers, state pruning, and SMT quantifier
   instability:** Hand-written abstract transfer functions (`Linux eBPF` `tnum`
   and 32/64-bit subregister bounds in `CVE-2020-8835`, `CVE-2021-3490`,
   `CVE-2021-31440`, `CVE-2022-23222`, and state-pruning taint omissions in
   `CVE-2023-2163`) violate concretization soundness, while heuristic E-matching
   in SMT-backed verifiers (`IronFleet`, `Dafny`, `Verus`, `Viper`) causes
   non-deterministic proof collapse ("the butterfly effect") under minor code
   edits.

Anneal's four orthogonal `trusted/lean/` primitives are specifically shaped to
block these six failure modes at the Lean 4 kernel boundary without expanding
the trusted computing base (TCB):

- **`Language SemObs` + `BehaviorCodec` (`Compiles` / `Abstracts`):** Separates
  downward compilation from upward abstraction via a partial-bijection codec
  whose left-inverse query law (`decodeQuery (encodeQuery q₁) = q₁`) and
  observable spine alignment (`obs_decodeOut`) prevent unverified frontend
  rewrites or ghost-state erasure from silently dropping failure behaviors.
- **`ProductiveOn` + `InhabitedPre`:** Enforces Dijkstra's Law of the Excluded
  Miracle ($\forall q,\, \text{pre}(q) \to \exists h\,o,\, (L.\text{sem}\,p\,q).\text{val}\,h\,o$)
  together with domain non-emptiness ($\exists q,\, \text{pre}(q)$), ruling out
  both empty-outcome prophecy miracles and contradictory refinement domains.
- **Positive per-obligation `VerificationResult`:** Formulates obligation
  tracking as a positive conjunction of disjunctions
  `AllHold (waived.map policy.isAllowed) ∧ AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))`,
  eliminating antecedent Principle-of-Explosion contamination across obligations.
- **`SmallStepMachine` with `EventualBehaviorOf` + `StepResult.externalCall`:**
  Separates finite-prefix undefinedness (`.failed .ub` / `.stuck`, mapped to
  `defined = False` in `Partial`) from non-termination (`.diverges`, mapped to a
  defined `EventualOut` outcome), preserves explicit normal vs. unwind termination
  in `Terminal Val`, and checks `boundaryInv : Bool` at every `externalCall`
  step so broken `AdtInv` or active Tree Borrows protectors fail immediately
  upon callback invocation.

## Applicability

This report synthesizes primary historical failure records, CVE root-cause
commits, upstream issue trackers, and published postmortems across four families
of formal verification systems, and evaluates their architectural implications
for the Anneal verification platform at
`joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`:

- **Deductive verifiers and IVL pipelines:** `Dafny` (`dafny-lang/dafny` issues
  `#4053`, `#6534`, `#6537`), `Verus`
  (`verus-lang/verus@0141ebc6f14410dfc87fef1da57408578002eb7c` and arXiv
  `2303.05491v2`), `Creusot` and `RustHornBelt` (`creusot-rs/creusot`, DOI
  `10.1145/3519939.3523704`), `Prusti` and `Viper`/`Boogie`
  (`viperproject/prusti-dev`, DOI `10.1007/978-3-030-81688-9_33`, DOI
  `10.1145/3656438`), `Kani` (`model-checking/kani` `[F] Soundness` corpus),
  `F*` (`FStarLang/FStar` issues `#4478`, `#4485`, `#4487`), `Frama-C WP` /
  `Why3`, and `KeY` / `ESC/Java2`.
- **Separation logics, borrow checkers, and aliasing/provenance models:**
  `RustBelt` (DOI `10.1145/3158154`, `rust-lang/rust#25760`), `RustBelt Meets
  Relaxed Memory` (DOI `10.1145/3371102`, `rust-lang/rust#51780`), `Stacked
  Borrows` (DOI `10.1145/3371109`), `Tree Borrows` (DOI `10.1145/3729338`),
  `rustc` NLL/Polonius and trait-solver soundness issues (`rust-lang/rust#25860`,
  `#84591`, `#100013`), and LLVM/C/Rust pointer-integer provenance bugs
  (`llvm#34548`, `llvm#35229`, DOI `10.1145/3062341.3062343`, DOI
  `10.1145/3276495`).
- **Abstract interpreters and static analyzers:** Linux kernel eBPF verifier
  (`torvalds/linux` commits `581738a681b6`, `049c4e13714e`, `10bf4e83167c`,
  `64620e0a1e71`, `71b547f56124` for `CVE-2020-8835`, `CVE-2021-3490`,
  `CVE-2021-31440`, `CVE-2022-23222`, `CVE-2023-2163`), `Agni` range-analysis
  verification (DOI `10.1109/CGO53902.2022.9741267`, DOI
  `10.1007/978-3-031-37709-9_12`), `Astrée`, `Frama-C Eva`, `IKOS`, and `MIRAI`.
- **Functional translators and SMT proof-stability studies:** `Electrolysis`
  (Ullrich 2016), `Aeneas` and `Charon`
  (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`, DOI
  `10.1145/3547647`), `IronFleet` (DOI `10.1145/2815400.2815428`), Dafny trigger
  selection (DOI `10.1007/978-3-319-41528-4_20`), and `Mariposa` (DOI
  `10.1145/3622852`).

"Failure" is construed broadly to encompass (a) confirmed soundness bugs and
CVEs where a verifier or static analyzer accepted unsafe code or allowed proving
`false`, (b) vacuity bugs where inconsistent axioms or preconditions rendered a
theorem empty, (c) expressiveness and semantic-model mismatches where valid
idiomatic systems code was rejected, and (d) proof-maintenance collapses where
verification became intractable or brittle at scale.

## Findings

### 1. Cross-Cutting Failure Taxonomy and Mapping to Anneal's Four Primitives

Basis: **derived** synthesis from the primary source, bug-tracker, CVE, and
execution evidence in §§2–6.

Every historical failure mode examined in §§2–5 exploits a specific gap between
the artifact a user believes they verified and the semantic proposition actually
checked by the tool. The table below indexes all 28 historical failure
postmortems in this report against the exact Anneal `trusted/lean/` primitive
that closes the corresponding vulnerability class:

| Failure ID | System(s) & Primary Coordinates | Failure Category | Root-Cause Mechanism | Anneal `trusted/` Defense Primitive & Architectural Mechanism |
| :--- | :--- | :--- | :--- | :--- |
| **F-1.1** | `Dafny` (`#6534`, `#6537`) | Prelude Axiom Soundness | Unguarded `$Box($Unbox(x): T) == x` and `Map#Items` prelude axioms admit ill-typed terms and derive `false` via E-matching | Zero background SMT prelude in `trusted/`; all domain lemmas live in `theory/` and must be proved constructively in Lean 4's kernel |
| **F-1.2** | `Dafny` (`#4053`), `Verus` (`air/smt_verify.rs`), `Why3` | Unchecked Solver Backend | Z3 `/proverOpt:O:smt.arith.solver=6` bug or solver bug returns `unsat` without proof certificate reconstruction | `trusted/audit/` inspects `.olean` kernel environment directly; external solvers must emit `LRAT`/`Alethe`/Farkas certificates checked in `theory/` |
| **F-1.3** | `Verus` (`verus@0141ebc`, `erasure.md`, `Tracked::assume_new`) | Ghost Erasure & Mode-Boundary Mismatch | Conditional compilation (`cfg(verus_only)`) or unverified callers forging zero-sized `Tracked<T>` wrappers break erased guarantees | Anneal captures post-macro `Runtime(PostCleanup)` MIR directly from `rustc`; `BehaviorCodec` binds pure ghost state to concrete `MirState` bytes |
| **F-1.4** | `Creusot`, `RustHorn`, `RustHornBelt` (PLDI 2022) | Prophetic Borrow Resolution Vacuity | Over-constrained prophecy variables $(v_{\text{cur}}, v_{\text{final}})$ yield empty outcome set ($\text{wp}(p, \text{False}) = \text{True}$) | `L.ProductiveOn pre prog` enforces Dijkstra's Law of the Excluded Miracle ($\exists h\,o,\, (L.\text{sem}\,p\,q).\text{val}\,h\,o$) |
| **F-1.5** | `Prusti` / `Viper` / `Boogie` (CAV 2021, PLDI 2024) | Frontend-to-IVL Inhale/Exhale Desugaring Bug | Flawed permission-mask exhale or shared-borrow encoding silently turns source failure into IVL `assume false` (magic) | `Abstracts L_v L_mir codec v s` (`L_mir.sem s ≤ codec.toMorphism (L_v.sem v)`) reflects `L_v` safety back to source `L_mir` failure freedom |
| **F-1.6** | `Kani` (`[F] Soundness` label) | Uninit Padding, Provenance & Stub Vacuity | CBMC translation omits byte-level `Uninit` padding checks, pointer provenance tags, or replaces functions with under-approximating stubs | `L_mir` models byte-accurate `AbstractByte` (`Uninit \| Init`) and provenance; `ProductiveOn` blocks under-approximating empty stubs |
| **F-1.7** | `F*` (`#4478`, `#4485`, `#4487`), `Liquid Haskell` / `Flux` | Empty-Domain / Contradictory Refinement Vacuity | VC simplifier assumes uninhabited function/refinement type is inhabited, or contradictory entry refinement proves `False` | `InhabitedPre pre` ($\exists q,\, \text{pre}(q)$) is mandatory alongside `SpecOn` and `ProductiveOn`, rejecting empty precondition domains |
| **F-1.8** | `Frama-C WP` (Vanadium `goto`), `KeY`, `ESC/Java2` | Abrupt Termination, Unstructured CFG & Loop Unrolling | `goto` across statement contracts breaks WP domination assumptions; `ESC/Java2` 1-step loop unrolling misses $k > 1$ bugs | `SmallStepMachine` operates directly on unstructured `Runtime(PostCleanup)` MIR CFGs with `EventualBehaviorOf` unbounded step closure |
| **F-2.1** | `RustBelt` (`MutexGuard::map`, `rust-lang/rust#25760`) | Lifetime Variance / Covariant Guard Soundness | `MutexGuard::map` inherited covariance where `'a: 'b` was not properly bounded for `&mut T` projection, allowing use-after-unlock | `StepResult.externalCall` and `AdtInv` proofs operate over post-monomorphization/post-cleanup MIR memory lifetimes and active protectors |
| **F-2.2** | `RustBelt Meets Relaxed Memory` (`Arc::get_mut`, `rust-lang/rust#51780`) | Sequential-Consistency Adequacy Gap | Original POPL 2018 RustBelt assumed SC memory; under C11 weak memory, `Arc::get_mut`'s `Relaxed` weak-count read raced with `Arc::clone`/`drop` | `Language SemObs` allows instantiating weak-memory `SmallStepMachine` models in `theory/` without baking an SC assumption into `trusted/` |
| **F-2.3** | Rust `std` (`Vec::dedup_by`, `BinaryHeap`, `RefCell`) | Callback Re-Entrancy & Panic Unwind Safety | Methods temporarily break `AdtInv` (`len > init`), call user closure `f` that panics or re-enters, and read uninitialized memory on drop | `StepResult.externalCall boundaryInv branches` checks `boundaryInv` (`AdtInv`) at the exact call step; `EventualOut` checks `Terminal.panic` unwind paths |
| **F-2.4** | `Stacked Borrows` (POPL 2020) vs. `Tree Borrows` (PLDI 2025) | Eager Borrow-Stack Pop on Idiomatic Unsafe Rust | Stacked Borrows eagerly pops `Unique` tags on parent reads (breaking two-phase borrows, `addr_of!`, `container_of`) and over-constrains `&mut` | `Tree Borrows` replaces stack pops with lazy `Reserved → Active → Frozen → Disabled` tree transitions; `Compiles L_sb L_tb` relates both in `theory/` |
| **F-2.5** | `Tree Borrows` Function-Entry `Protector` Semantics | Cross-Call Noalias & Interior Mutability Subtlety | `llvm.noalias` requires protected references to stay valid until function exit, even across unknown external callbacks, unless `UnsafeCell` is present | `StepResult.externalCall` checks active call-frame `Protector` invariants via `boundaryInv` and constrains `branches` across opaque calls |
| **F-2.6** | `rustc` Borrow Checker (`#25860`, `#84591`, `#100013`) | Implied Bounds + Variance + HRTB Soundness Hole | `rustc` omits `ImpliedBounds` (`'b: 'a` from `&'a &'b T`) inside higher-ranked trait binders (`for<'a>`), transmuting short lifetimes to `'static` in safe Rust | Anneal does not take `rustc`'s borrow checker as an axiom for memory safety; `L_mir` checks actual dynamic memory and borrow-tag safety on MIR |
| **F-2.7** | LLVM / C / Rust Provenance (`llvm#34548`, `llvm#35229`, `PNVI`) | Pointer-Integer Cast Folding & GVN Miscompilation | Combining `inttoptr(ptrtoint(p)) -> p` with integer equality GVN substitutes pointers of different provenance; angelic `with_exposed_provenance` clashes with demonic choice | `L_mir` tracks deterministic Strict Provenance (`AllocId`) natively and resolves exposed provenance deterministically by disjoint live address range |
| **F-3.1** | Linux eBPF Verifier (`CVE-2020-8835`, `581738a681b6`) | `JMP32` 32-Bit Branch Bounds Refinement Bug | `__reg_bound_offset32` improperly derived 64-bit/tnum bounds after 32-bit conditional jumps (`BPF_JMP32`), yielding OOB kernel R/W | Certifying abstract interpreters in `theory/` must prove 1-step concretization soundness ($\forall s \in \gamma(a),\, \text{step}(s) \subseteq \gamma(F^{\#}(a))$) via `bv_decide` |
| **F-3.2** | Linux eBPF Verifier (`CVE-2021-3490`, `049c4e13714e`) | `tnum` vs. `u32`/`s32` Bitwise `AND`/`OR`/`XOR` Bug | `scalar32_min_max_and`/`or`/`xor` skipped updating 32-bit bounds when `subreg_def` was known constant, leaving `u32_min > u32_max` | In `theory/`, reduced product reductions between `tnum` (`KnownBits`) and intervals are machine-checked on 64-bit bitvectors (`bv_decide`) |
| **F-3.3** | Linux eBPF Verifier (`CVE-2021-31440`, `10bf4e83167c`) | `__reg_combine_64_into_32` Endpoint Truncation Bug | Projecting 64-bit `[0x0_ffffffff, 0x1_00000000]` to 32-bit truncated endpoints without checking `(umin >> 32) == (umax >> 32)` | `bv_decide` immediately refutes the unguarded 64-to-32 interval projection theorem with the exact boundary counterexample |
| **F-3.4** | Linux eBPF Verifier (`CVE-2022-23222`, `64620e0a1e71`) | Nullable Pointer (`*_OR_NULL`) Arithmetic Bypass | `adjust_ptr_min_max_vals` permitted pointer arithmetic on `PTR_TO_MEM_OR_NULL` before null check, retaining false bounds when pointer was `NULL` | `L_mir` separates `Option/Nullable` discriminant tags from valid `AllocId` pointers; pointer arithmetic on `AllocId = none` fails (`defined = False`) |
| **F-3.5** | Linux eBPF Verifier (`CVE-2023-2163`, `71b547f56124`) | Incorrect CFG State-Pruning Precision Backpropagation | `propagate_precision` failed to walk all predecessor frames/branches when marking a register precise, pruning an unsafe path as equivalent to a safe one | Anneal's certifying fixpoint checker (`checkNumFixpoint`) checks inclusion $F^{\#}(\text{inv}[bb]) \sqsubseteq^{\#} \text{inv}[bb']$ at *every* CFG edge independently |
| **F-3.6** | Linux eBPF Abstract Domains (`Agni`, CGO 2022 / CAV 2023) | Unsound Abstract Bitwise & Multiplication Operators | `Agni` discovered latent unsoundness and precision inversions in kernel `tnum` multiplication and bitwise reduction routines | Separating domain transfer soundness (proved once in `theory/`) from per-program post-fixpoint checking eliminates analyzer-engine TCB bugs |
| **F-3.7** | `Frama-C Eva`, `Astrée`, `IKOS`, `MIRAI` | Threshold Widening Collapse & Unmodeled Library Stubs | Aggressive widening ($\nabla$) loses relational loop invariants ($i \le len$); `MIRAI` / `IKOS` missing stdlib stubs silently under-approximate side effects | External analyzers emit Farkas/Octagon fixpoint certificates checked in `theory/`; unverified callees must use `VerificationResult` waivers or `externalCall` |
| **F-4.1** | `Electrolysis` (Ullrich 2016) | Pure Lens Explosion & Interior Mutability Wall | Pure functional lenses (`get`/`set` laws) could not express `UnsafeCell`, `RefCell`, raw pointer aliasing, or borrows stored inside structs | Anneal places `L_mir` (`SmallStepMachine`) at the base of `trusted/` and uses `Abstracts L_pure L_mir` only for functions where functional lenses apply |
| **F-4.2** | `Prusti` (Legacy Encoder vs. Rewrite) | Monolithic Method-Granularity Viper Encoding | Encoding full Rust MIR + borrow lifetimes into one giant Viper method caused nonlinear Z3 timeouts and opaque fold/unfold errors | Fine-grained per-obligation decomposition in `VerificationResult` + modular `Abstracts` bridges allow mixing decidable checkers with interactive Lean proofs |
| **F-4.3** | `Aeneas` & `Charon` (`#583`, `#534`, `OfJson.ml`) | UB-Introducing Frontend Pass & Silent Partial Output | `Charon` `--preset=aeneas` rewrites raw-pointer indexing into reference creation (`#583`), loses quantified lifetimes (`#534`), and `OfJson.ml` drops `has_errors` | `anneal-rustc-capture` extracts unmodified `Runtime(PostCleanup)` MIR directly without reference-synthesizing rewrites and fails closed on errors |
| **F-4.4** | `Aeneas` & `RustHorn` | Functionalization Boundary on Cyclic/Aliased State | Backward functions and prophecies require strict tree-shaped non-aliasing; raw pointers, intrusive lists, and `Arc`/`Mutex` cannot be translated directly | Anneal supports heterogeneous verification in one crate: `Aeneas`-style `Abstracts` for safe callers composed with Iris/SymHeap proofs for `unsafe` leaves |
| **F-4.5** | `IronFleet` (SOSP 2015), `Dafny` (CAV 2016), `Verus`, `Viper` | SMT E-Matching "Butterfly Effect" & Trigger Loops | Unrelated variable renames or assertion additions alter Z3 quantifier instantiation order, turning 1s proofs into timeouts (`Mariposa` OOPSLA 2023) | Anneal freezes deterministic proof artifacts (Lean kernel terms, `LRAT`, `Alethe`, Farkas witnesses) in `theory/` rather than re-running heuristic SMT search in CI |
| **F-4.6** | `F*`, `Why3`, `Verus`, `Creusot` | Cross-Version Proof Session & Toolchain Drift | Upgrading the SMT solver or compiler nightly invalidates thousands of implicit VC obligations with no localized diagnostic | `VerificationResult` binds individual obligations to explicit source spans and deterministic kernel-checked certificates |

---

### 2. Deductive Verifier Soundness Bugs and Vacuity Postmortems

#### F-1.1: Background Prelude Axiom Inconsistencies (`Dafny` `#6534`, `#6537`)

Basis: **documentation** — `dafny-lang/dafny` issues `#6534` and `#6537`.

- **Historical failure:** Deductive verifiers that compile a high-level language
  to Boogie or SMT-LIB prepend a large, hand-authored axiomatic prelude (often
  2,000–5,000 lines of quantified SMT axioms defining boxing/unboxing, type
  tags, heap allocation maps, sequences, sets, and finite maps). In `Dafny`
  issue `#6534` (*"Soundness: unguarded `$Box($Unbox(x): T) == x` axiom"*), the
  Boogie prelude asserted the round-trip identity
  $\forall x : \text{Box}.\, \text{\$Box}(\text{\$Unbox}(x) : T) = x$ without
  guarding on whether $x$'s dynamic type tag actually matched $T$. When $T$ had
  a restricted cardinality or subset constraint (such as `bool` or a finite
  newtype), instantiating the unguarded axiom on boxes of two distinct types
  forced their unboxed values to collide, allowing Z3 to derive `false` and
  verify `ensures false`. Similarly, in `Dafny` issue `#6537` (*"Soundness:
  `Map#Items` membership axiom admits non-pairs"*), the axiomatization of
  `Map#Items` omitted a structural sort guard requiring elements of `m.Items` to
  be 2-tuples, creating a model contradiction with tuple projection axioms.
- **Technical root cause:** Unchecked universal axioms in an SMT prelude bypass
  definitional conservativity. Even a single missing sort/type-tag guard or an
  over-triggered quantifier in a 4,000-line `.bpl` prelude makes the background
  theory $\mathcal{T}_{\text{prelude}}$ unsatisfiable ($\mathcal{T}_{\text{prelude}} \vdash \bot$).
  Because an SMT solver checks validity of $G$ by testing unsatisfiability of
  $\mathcal{T}_{\text{prelude}} \wedge \neg G$, any inconsistency in
  $\mathcal{T}_{\text{prelude}}$ silently makes *every* verification condition
  return `unsat` ("Verified").
- **Architectural lesson for Anneal (`trusted/lean/`):** Anneal's `trusted/lean/`
  contains **zero background SMT prelude axioms** and zero uninterpreted
  function axiomatizations. All data structures (`BitVec`, `Array`, `List`,
  finite maps, and `L_mir` operational semantics) are defined constructively in
  Lean 4 (`trusted/lean/` and `theory/`), where Lean's kernel enforces
  definitional conservativity and `trusted/audit/` (`TrustedBoundary.lean`)
  audits `.olean` files to reject unauthorized `axiom` declarations.

#### F-1.2: SMT Solver Backend Bugs and Flag-Dependent Unsoundness (`Dafny` `#4053`, `Verus`, `Why3`)

Basis: **documentation** + **source** — `dafny-lang/dafny#4053`;
`verus-lang/verus@0141ebc6f14410dfc87fef1da57408578002eb7c`,
`source/air/src/smt_verify.rs:249–364`.

- **Historical failure:** In `Dafny` issue `#4053` (*"Unsound verification with
  `/proverOpt:O:smt.arith.solver=6`"*), passing a non-default Z3 arithmetic
  solver configuration interacted with Dafny's prelude axioms and nonlinear
  arithmetic encoding to return `unsat` on an invalid assertion. More broadly,
  as established in our corpus report `verus-tracked-memory-trust-0141ebc`,
  `Verus`'s AIR backend (`smt_verify.rs:249–275`) sends an SMT-LIB query to Z3
  and treats the textual response `"unsat"` as `ValidityResult::Valid` without
  reconstructing a proof object; `Creusot`/`Why3`, `Prusti`/`Viper`, and
  `Dafny` do the same by default.
- **Technical root cause:** Mainstream SMT solvers (`Z3`, `cvc5`) are complex
  500,000+ line C++ codebases with intricate combinations of Nelson-Oppen theory
  propagation, E-matching, bit-blasting, and linear/nonlinear arithmetic. Trusting
  an uncertified `"unsat"` string places the entire C++ SMT solver and the
  verifier's VC-to-SMT-LIB pretty-printer inside the TCB.
- **Architectural lesson for Anneal (`trusted/lean/` & `trusted/audit/`):**
  Anneal never accepts an external solver's `"unsat"` status as a trusted
  verdict. `trusted/audit/` checks that `Trusted.CrateTheorem` has a complete,
  axiom-free proof term inside the Lean 4 kernel environment. When external SAT
  or SMT solvers are used in Anneal, they act strictly as untrusted certificate
  oracles that emit `LRAT`, `Alethe`, or Farkas linear-combination witnesses
  verified by total reflective checkers in `theory/`.

#### F-1.3: Ghost Erasure, Conditional-Compilation Skew, and Forged Tracked Tokens (`Verus`)

Basis: **source** + **documentation** —
`verus-lang/verus@0141ebc6f14410dfc87fef1da57408578002eb7c`,
`source/builtin/src/lib.rs:546–570`, `source/vir/src/modes.rs`,
`source/docs/guide/src/erasure.md`.

- **Historical failure:** Deductive verifiers that extend Rust syntax with
  inline `spec` and `proof` blocks (`Verus`, `Creusot`, `Prusti`) must erase
  ghost code before invoking `rustc` to produce executable machine code. Three
  distinct failure modes have surfaced in `Verus`'s issue tracker and
  documentation:
  1. **Verification vs. compilation body skew (`erasure.md`):** Conditional
     compilation attributes (`#[cfg(verus_keep_ghost)]` / `verus_only`) can cause
     the VIR verifier to verify one function body while `rustc` compiles a
     different executable body.
  2. **Unhygienic spec/closure and integer-discriminant mismatches
     (`verus-lang/verus` `label:soundness`):** Soundness bugs in `Verus`'s internal
     VIR translator—such as mis-scoped variables in closure capture environments,
     const-generic substitution errors, or enum discriminant integer-width
     mismatches—allowed proving `ensures false` because the VIR encoding
     diverged from `rustc`'s type/layout rules.
  3. **Public API boundary bypass on erased `Tracked<T>` tokens
     (`builtin/src/lib.rs:546–570`):** At runtime, `Tracked<PointsTo<T>>` is a
     zero-sized wrapper (`PhantomData`). If a verified Verus function is called
     by ordinary unverified Rust code (or if macro visibility leaks allow
     calling `Tracked::assume_new`), the caller can pass a forged ZST token
     without owning the underlying memory permission.
- **Technical root cause:** Whenever verification operates on a custom
  pre-erasure AST (`VIR`) rather than the exact artifact compiled to machine
  code, any discrepancy between `VIR` lowering and `rustc` lowering—or any
  assumption carried only by erased ghost parameters at public crate
  boundaries—creates an unverified gap.
- **Architectural lesson for Anneal (`trusted/rustc-capture/` & `BehaviorCodec`):**
  1. `anneal-rustc-capture` extracts `Runtime(PostCleanup)` MIR directly from
     the active `rustc` compilation pass *after* macro expansion, type checking,
     borrow checking, and drop elaboration, ensuring verification and codegen
     see the exact same MIR control-flow graph and monomorphic type layouts.
  2. In `Abstracts L_v L_mir codec v s`, `codec : BehaviorCodec L_v L_mir`
     requires `decodeQuery (encodeQuery q₁) = q₁`. As proved in Sub-Domain 1
     Executive Finding #1, ghost permissions (like fractional maps or
     `GhostToken` arenas) cannot be left as unconstrained phantom arguments in
     `L_mir.Query`; they must be grounded as concrete heap-layout predicates in
     `MirState` (`encodeQuery`) or initialized deterministically from `MirState`.

#### F-1.4: Prophetic Borrow Resolution Vacuity and `#[trusted]` Invariant Gaps (`Creusot` & `RustHornBelt`)

Basis: **documentation** — Matsushita, Denis, Jourdan, and Dreyer, *"RustHornBelt:
A Semantic Foundation for Functional Verification of Rust Programs with Unsafe
Code,"* PLDI 2022, DOI `10.1145/3519939.3523704`; `creusot-rs/creusot`
`label:soundness` tracker.

- **Historical failure:** `RustHorn` and `Creusot` translate a mutable borrow
  `b: &'a mut T` into a pair of pure first-order values $(v_{\text{cur}},
  v_{\text{final}})$, where $v_{\text{final}}$ is a **prophecy variable**
  predicting the value `*b` will hold at the future point when lifetime `'a`
  ends (`Resolve::resolve`). When `'a` ends, the translator emits an assumption
  identifying the current value of `*b` with $v_{\text{final}}$:
  `assume (v_at_end == v_final)`. In `Creusot`'s development, soundness issues
  arose when:
  1. Custom or unsoundly specified `Resolve` implementations, type invariants
     (`creusot_contracts::Invariant`), or cyclic borrow resolutions introduced
     contradictory constraints on $v_{\text{final}}$, turning `assume (v_at_end == v_final)`
     into `assume false`; and
  2. Functions marked `#[trusted]` or external standard-library specifications
     (`Vec`, `HashMap`) omitted implicit type invariants or precondition guards,
     allowing callers to obtain values violating type invariants.
- **Technical root cause:** In predicate-transformer terms, a prophecy assumption
  `assume (P(v_final))` is demonic assumption: $\text{wp}(\texttt{assume } P, Q) = (P \to Q)$.
  If the constraints accumulated on $v_{\text{final}}$ along an execution path
  are unsatisfiable ($\neg \exists v_{\text{final}},\, P(v_{\text{final}})$),
  then $\forall v_{\text{final}},\, P(v_{\text{final}}) \to Q$ holds vacuously
  for *every* postcondition $Q$, including $Q = \text{False}$! That is why
  `RustHornBelt` (PLDI 2022) had to construct a delicate step-indexed semantic
  model of *parametric prophecies* in Iris to prove that well-typed safe Rust
  borrow resolutions always have a realizable prophecy assignment.
- **Architectural lesson for Anneal (`ProductiveOn` & `VerificationResult`):**
  1. Anneal's `L.ProductiveOn pre prog` (`∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o, (L.sem prog q).val h o`)
     directly enforces **non-empty outcome sets** (Dijkstra's Law of the Excluded
     Miracle). As verified in `support/failure_mechanisms_probe.py` (`witness_1`),
     any prophetic or backward-function translation in `theory/` (`L_pure`)
     whose prophecy resolution constraint is unsatisfiable produces an empty
     outcome set `(L_pure.sem f q).val h = ∅`, which is immediately rejected by
     `L_pure.ProductiveOn pre f`!
  2. Any unverified `#[trusted]` specification or waived obligation must be
     explicitly listed in `waived` inside `VerificationResult policy waived obligations`,
     where `policy.isAllowed` gates whether waivers are permitted and positive
     disjunction (`ob.id ∈ waived ∨ ob.prop`) prevents a flawed helper spec from
     contaminating unwaived obligations (`witness_3`).

#### F-1.5: Separation-Logic-to-IVL Inhale/Exhale Desugaring Bugs (`Prusti`, `Viper`, `Boogie`)

Basis: **documentation** — Parthasarathy et al., CAV 2021 (DOI
`10.1007/978-3-030-81688-9_33`) and PLDI 2024 (DOI `10.1145/3656438`);
`viperproject/prusti-dev` `label:unsoundness` tracker.

- **Historical failure:** `Prusti` compiles Rust MIR with specifications into
  `Viper` (an intermediate verification language with implicit dynamic frames),
  and `Viper`'s `Carbon` backend compiles `Viper` `inhale`/`exhale` statements
  into `Boogie` `assume`/`assert` statements over heap and permission-mask maps.
  Both `Prusti` and `Viper` experienced historical soundness bugs in this
  two-stage desugaring:
  1. In `Prusti`, early encodings of shared references (`&T`), specification
     refinements on trait implementations, and loop framing omitted permission
     read-framing checks or inhaled over-strong post-borrow state assumptions,
     allowing `assert!(false)` to verify.
  2. In `Viper` and `Boogie` (analyzed in Parthasarathy et al., CAV 2021 and
     PLDI 2024, and in our corpus report
     `boogie-viper-failure-reflection-certificates-2021-2024`), bugs in map
     encoding, background axiom generation, passification, or well-formedness
     ordering meant that a source program with a reachable failure reduced to a
     target `Boogie` program whose execution reached `assume false` (magic),
     causing `Boogie` to report the buggy program as verified.
- **Technical root cause:** A verifier frontend that lowers source code through
  unverified IVL transformations (`Rust → Viper → Boogie → SMT`) implicitly
  assumes **failure reflection**: every failing execution of the source program
  must correspond to a failing execution of the generated IVL program. If any
  lowering step accidentally turns a bad source state into an empty/magic target
  transition (`assume false`) or drops a branch, target verification succeeds
  while source safety fails.
- **Architectural lesson for Anneal (`Abstracts` in `Trusted/Refinement.lean`):**
  Anneal eliminates unverified IVL lowering from the TCB. In
  `Abstracts L_v L_mir codec v s` (`L_mir.sem s ≤ codec.toMorphism (L_v.sem v)`),
  the behavioral refinement order `b₂ ≤ b₁` on `Partial (Out → Prop)` is defined
  as:
  $$\forall q,\, (b_1\,q).\text{defined} \to \exists h_2 : (b_2\,q).\text{defined},\, \forall o,\, (b_2\,q).\text{val}\,h_2\,o \to (b_1\,q).\text{val}\,h_1\,o$$
  Consequently, proving `(L_v.sem v q₁).defined` (the abstract model `v` has no
  failure) immediately implies `(L_mir.sem s (encodeQuery q₁)).defined` (the
  concrete MIR program `s` has no `.failed .ub` or `.stuck` prefix!). No
  translation into `L_v` is trusted unless accompanied by a kernel-checked proof
  of `Abstracts L_v L_mir codec v s`.

#### F-1.6: Bounded Model Checking Soundness Gaps on Padding, Provenance, and Stubs (`Kani`)

Basis: **documentation** — `model-checking/kani` issues under label
`[F] Soundness`.

- **Historical failure:** `Kani` translates Rust MIR to `Goto-C` programs checked
  by `CBMC`. In `model-checking/kani`'s `[F] Soundness` tracker (which tracks
  false negatives where Kani reports `VERIFICATION:- SUCCESSFUL` on code with UB
  or panics), recurring soundness gaps have included:
  1. **Uninitialized padding bytes:** Copying or transmuting structs with
     uninitialized padding bytes into types requiring initialized bytes (e.g.,
     `zerocopy`-style casts or `transmute`) was not flagged when CBMC's byte
     model initialized local padding to zero or omitted per-byte `Uninit` shadow
     tracking.
  2. **Pointer provenance and aliasing UB:** Because CBMC models pointers as
     `(object_id, offset)` pairs without Stacked/Tree Borrows tags or Rust
     Strict Provenance rules, `unsafe` code that violates mutable aliasing rules
     or casts integers to pointers passes Kani while failing Miri or
     miscompiling under `rustc -O3`.
  3. **Function contract and stub replacement vacuity:** When verifying a caller
     against a stubbed or contracted callee (`#[kani::stub]` /
     `#[kani::requires]`), over-constrained `assume` clauses or incomplete
     havocing of reachable mutable memory allowed callers to pass verification
     while exhibiting UB on real callee behaviors.
- **Technical root cause:** Lowering Rust MIR into a C-level model checker
  (`CBMC`) inherits C's memory abstractions, losing Rust-specific UB conditions
  (uninitialized byte poison, borrow tags, unwind landing pads) and relying on
  unchecked stub instrumentation.
- **Architectural lesson for Anneal (`L_mir` & `StepResult.externalCall`):**
  Anneal's `L_mir` (`SmallStepMachine`) models Rust's byte-level initialization
  (`Uninit` vs. `Init`), pointer provenance (`AllocId`), and borrow tags directly
  in Lean 4, and models stubbed/contracted calls via
  `StepResult.externalCall boundaryInv branches` where `branches : MirState → Prop`
  demonically quantifies over *all* post-states permitted by the callee contract.

#### F-1.7: Dependent Type-Checker and VC Simplifier Empty-Domain Bugs (`F*` `#4478`, `#4485`, `#4487`, `Liquid Haskell` / `Flux`)

Basis: **documentation** — `FStarLang/FStar` issues `#4478`, `#4485`, `#4487`.

- **Historical failure:** Even dependently typed languages and refinement type
  checkers have suffered soundness bugs that prove `False`:
  1. **`F*` VC simplifier uninhabited-type bugs (`FStarLang/FStar#4485`, `#4487`):**
     `F*`'s internal verification-condition simplifier simplified away unused
     quantified variables or function bindings under the implicit assumption that
     every type in the context was inhabited, allowing a user to bind a variable
     of an uninhabited refinement/function type (`squash False` or `unit -> Dv False`)
     and derive `Lemma False`.
  2. **`F*` reflection API round-trip unsoundness (`FStarLang/FStar#4478`):**
     The metaprogramming reflection axiom `inspect_pack_inv` asserted that
     packing and inspecting syntax views was a strict identity even for invalid
     or unsupported universe instantiations (`Tv_UInst` / `Tv_Unsupp`), allowing
     tactics to construct an ill-typed term proving `False`.
  3. **Contradictory refinement preconditions (`Liquid Haskell` / `Flux`):**
     In liquid refinement type systems, if a function's input refinement types
     or assumed measure axioms are mutually contradictory (e.g., `x: usize{x > 10 && x < 5}`),
     every Horn subtyping obligation $\Gamma \wedge \text{pre} \Rightarrow \text{goal}$
     has a false premise and is discharged trivially by the SMT solver.
- **Technical root cause:** Classical first-order logic and SMT solvers assume
  non-empty sorts, whereas dependent and refinement types easily construct empty
  types ($\{x : T \mid \text{False}\}$). Any simplification rule or function
  contract that fails to prove **inhabitation** of its domain risks deriving
  `False` from an empty set.
- **Architectural lesson for Anneal (`InhabitedPre` in `Trusted/Refinement.lean`):**
  Anneal elevates `InhabitedPre pre := ∃ q, pre q` to a first-class primitive in
  `trusted/lean/`. As demonstrated in `support/failure_mechanisms_probe.py`
  (`witness_2`), `L.SpecOn pre post` and `L.ProductiveOn pre prog` both quantify
  universally over `{q | pre q}` and therefore hold vacuously when `pre` is
  contradictory; pairing them with `InhabitedPre pre` forces every verified
  specification to exhibit a concrete input witness $q_0$ satisfying `pre q₀`.

#### F-1.8: Unstructured Control Flow, Abrupt Termination, and Loop Unrolling Gaps (`Frama-C WP`, `KeY`, `ESC/Java2`)

Basis: **documentation** — Frama-C WP Vanadium release notes (`goto` / statement
contract restrictions); Flanagan et al., *ESC/Java2* design documentation.

- **Historical failure:**
  1. **`Frama-C WP` non-natural `goto` loops and statement contracts:** Prior to
     Frama-C 23 (Vanadium), `Frama-C WP`'s weakest-precondition passify/CFG
     reduction assumed natural reducible loops dominated by a single loop header.
     When C programs used `goto` to jump into the middle of a loop or across a
     statement contract, the dominator-tree WP calculation dropped state edges,
     producing unsound verification conditions (forcing Frama-C 23+ to restrict
     non-natural `goto` loops and statement contracts).
  2. **`KeY` and `ESC/Java2` abrupt termination and bounded loop unrolling:**
     `ESC/Java2` intentionally unrolled loops only once ($k = 1.5$ iterations)
     by default, missing any bug that required $\ge 2$ loop iterations, and
     approximated object invariants across exception paths. In `KeY` and early
     JML tools, abrupt termination (`throw`, `break`, `continue`, `return` inside
     `try`/`finally`) repeatedly caused soundness bugs when normal-execution
     postconditions or framing rules were applied to exceptional exit edges.
- **Technical root cause:** Syntax-directed VCGens struggle with unstructured
  control-flow graphs (`goto`, multi-entry loops) and exceptional control flow
  (panics, stack unwinding, `finally` / drop glue) because syntactic substitution
  rules assume structured single-entry/single-exit blocks.
- **Architectural lesson for Anneal (`SmallStepMachine` & `EventualOut`):**
  Anneal's `trusted/lean/` defines program semantics operationally via
  `SmallStepMachine` over `Runtime(PostCleanup)` MIR's unstructured basic-block
  CFG, where `rustc` has already lowered all loops, `break`/`continue`, `?`
  operators, and panic stack unwinding (`UnwindAction` cleanup edges) into
  explicit basic-block transitions, and `EventualOut` distinguishes normal return
  (`Terminal.return`) from panic unwinding (`Terminal.panic`) in its terminal
  outcome type.

---

### 3. Separation Logic, Adequacy, and Aliasing Model Failures

#### F-2.1: Standard-Library Lifetime Variance and Guard Projection Bug (`RustBelt` & `MutexGuard::map`, `rust-lang/rust#25760`)

Basis: **documentation** — Jung, Jourdan, Krebbers, and Dreyer, *"RustBelt:
Securing the Foundations of the Rust Programming Language,"* POPL 2018, DOI
`10.1145/3158154`; `rust-lang/rust#25760`.

- **Historical failure:** While formalizing the semantic type soundness of
  Rust's standard library synchronization primitives in Iris (`RustBelt`, POPL
  2018), Jung et al. discovered a soundness bug in `std::sync::MutexGuard::map`
  (`rust-lang/rust#25760`). `MutexGuard<'a, T>` held a lock on a `Mutex<T>` for
  lifetime `'a`, and `MutexGuard::map` took a closure `F: FnOnce(&mut T) -> &mut U`
  to project the guard to a subfield `MutexGuard<'a, U>`. Because `MutexGuard<'a, T>`
  contained a raw pointer `*mut T` (or `&'a Mutex<T>`) without a phantom
  invariant marker on `T`, `rustc` inferred `MutexGuard<'a, T>` to be
  **covariant** in `T`! A safe caller could therefore obtain a
  `MutexGuard<'a, &'static str>`, coerce it via covariance to
  `MutexGuard<'a, &'short str>`, overwrite the protected reference with a
  short-lived `'short` reference while holding the lock, and unlock the mutex—leaving
  a dangling `'short` reference inside the `'static` `Mutex`!
- **Technical root cause:** Syntactic variance inference in `rustc` inspects
  only the structural field types of an ADT (`*const T` is covariant, `*mut T` /
  `&mut T` is invariant). When an `unsafe` abstraction wraps a shared reference
  `&'a Mutex<T>` or raw pointer to provide mutable access (`DerefMut`), omitting
  `PhantomData<&'a mut T>` silently makes the wrapper covariant in `T`, breaking
  the semantic invariant of exclusive mutable ownership.
- **Architectural lesson for Anneal (`AdtInv` & `VerificationResult`):**
  In Anneal (UC-6.4), a module's representation invariant `AdtInv(ty, val, state)`
  is defined semantically over `L_mir` heap states rather than trusting
  syntactic variance annotations. If a safe public function accepts or returns a
  projected guard after lifetime coercion, the proof of `L_mir.sem m ≤ L_mir.SpecOn pre_AdtInv post_AdtInv`
  must show that `post_AdtInv` holds for all values permitted by the coerced
  type signature, immediately exposing any variance-enabled invariant violation.

#### F-2.2: Sequential-Consistency Adequacy Blind Spot (`RustBelt Meets Relaxed Memory` & `Arc::get_mut`, `rust-lang/rust#51780`)

Basis: **documentation** — Dang, Jourdan, Kaiser, and Dreyer, *"RustBelt Meets
Relaxed Memory,"* POPL 2020, DOI `10.1145/3371102`; `rust-lang/rust#51780`.

- **Historical failure:** The original POPL 2018 `RustBelt` mechanized proof
  verified `std::sync::Arc<T>` under a **sequentially consistent (SC)**
  operational semantics and pronounced `Arc` sound. When Dang et al. (POPL 2020)
  ported the `Arc` proof to `iRC11` (an Iris separation logic over the C++11 /
  Rust relaxed-memory model), the proof of `Arc::get_mut` **failed**, uncovering
  a real data-race soundness bug in the Rust standard library
  (`rust-lang/rust#51780`). Specifically:
  - `Arc::get_mut(&mut self) -> Option<&mut T>` checks that both the strong
    reference count is 1 and the weak reference count is 1 before granting
    exclusive `&mut T` access to the payload.
  - To prevent a concurrent `Weak::upgrade` from racing, `Arc::get_mut` used
    `compare_exchange(..., Acquire, Relaxed)` to lock the strong count, and then
    read the weak count using `Ordering::Relaxed`!
  - Under C11 relaxed memory, when another thread dropped the last `Weak<T>`
    pointer, its prior read-only inspections of the `Arc` inner structure were
    only synchronized with `Release` on the weak count decrement. Because
    `Arc::get_mut` read the weak count with `Relaxed` instead of `Acquire`, no
    happens-before edge was established between operations before `Weak::drop`
    and the subsequent mutable write through `Arc::get_mut`—causing a C11 data
    race (immediate UB)!
- **Technical root cause:** A formal verification proof is only as strong as the
  operational machine semantics underneath its adequacy theorem. Assuming
  sequential consistency in the operational semantics hid a weak-memory
  synchronization bug (`Relaxed` vs. `Acquire`) in code whose entire purpose is
  concurrent reference counting.
- **Architectural lesson for Anneal (`Language SemObs` & `SmallStepMachine`):**
  Anneal does not hardcode a single sequentially consistent memory model into
  `trusted/lean/`'s core `Language` primitive. Instead, `Language SemObs` and
  `SmallStepMachine` are parameterized over `State`, allowing `theory/` to
  instantiate weak-memory operational models (`C11PromisingAxiomatic` in UC-5.5,
  `X86TSOBufferSim` in UC-5.6, `ArmRiscvPopModel` in UC-5.7) and verify
  concurrent primitives like `Arc` against weak-memory transitions without
  altering `trusted/lean/`.

#### F-2.3: Mid-Method Broken `AdtInv`, Callback Re-Entrancy, and Unwind Safety (`Vec::dedup_by`, `BinaryHeap`, `RefCell`)

Basis: **documentation** + **execution** — Rust standard-library panic-safety
and unwind-safety advisories (`Vec::dedup_by`, `BinaryHeap` hole-filling
patterns, `RustSec` container unwind bugs); `support/failure_mechanisms_probe.py`
(`witness_4`).

- **Historical failure:** A pervasive bug class in unsafe Rust collections
  (`std::vec::Vec::dedup_by`, `Vec::retain`, `BinaryHeap::sift_up` / `rebuild`,
  and third-party arena/vector crates) occurs when a method:
  1. Temporarily moves an element out of an array slot `ptr.add(i).read()`
     (leaving an uninitialized hole inside `0..self.len` and temporarily
     breaking `AdtInv`),
  2. Invokes a user-supplied closure `same_bucket(&mut a, &mut b)` or `Ord::cmp`
     while `self.len` still covers the uninitialized slot, and
  3. Plans to shift the remaining elements and update `self.len` *after* the
     closure returns.
  If the user closure **panics** (triggering stack unwinding), `Vec::drop` runs
  during unwinding while `self.len` still includes the uninitialized hole,
  causing `Drop::drop` to dereference uninitialized/moved memory (double-free /
  UB)! Even without panicking, if the user closure **re-enters** the data
  structure through a shared reference (`RefCell` / global / thread-local), it
  observes the broken `AdtInv` in the middle of the operation.
- **Technical root cause:** Deductive verifiers that check type invariants
  (`AdtInv`) only at function entry and normal function return (`return`
  postconditions) miss two critical intermediate observation points:
  1. **Open-world external call boundaries** where control leaves the current
     module while `AdtInv` is suspended, and
  2. **Exceptional unwind edges** (`UnwindAction::Cleanup`) where destructors
     run on partially mutated state.
- **Architectural lesson for Anneal (`StepResult.externalCall` & `Terminal.panic`):**
  Anneal catches both failure paths structurally (verified in `witness_4` of
  `support/failure_mechanisms_probe.py`):
  1. `StepResult.externalCall (boundaryInv : Bool) (branches : State → Prop)`
     evaluates `boundaryInv` **at the exact step the closure/trait call is
     invoked** and transitions immediately to `.failed .ub` (`defined = False`)
     if `boundaryInv = false`. Encoding `AdtInv` into `boundaryInv` forces the
     collection method (e.g., via a `Drop` guard struct that tracks the hole gap
     and sets `self.len = 0` or repairs the gap before calling out) to maintain
     a valid invariant at every callback!
  2. `EventualOut.terminated trace (term : Terminal Val)` explicitly includes
     both normal return (`Terminal.return`) and unwinding panic
     (`Terminal.panic`), so `SpecOn pre post_AdtInv` checks that `AdtInv` holds
     along `Runtime(PostCleanup)` MIR unwind edges as well.

#### F-2.4: Stacked Borrows Incompatibilities with Idiomatic Unsafe Rust vs. Tree Borrows (`POPL 2020` → `PLDI 2025`)

Basis: **documentation** + **execution** — Jung, Dang, Kang, and Dreyer,
*"Stacked Borrows: An Aliasing Model for Rust,"* POPL 2020, DOI
`10.1145/3371109`; Villani, Hostert, Dreyer, and Jung, *"Tree Borrows,"* PLDI
2025, DOI `10.1145/3729338`; `support/failure_mechanisms_probe.py` (`witness_5`).

- **Historical failure:** `Stacked Borrows` (POPL 2020) was the first formal
  operational aliasing model for Rust implemented in Miri. It modeled per-byte
  aliasing permissions as a linear stack of borrow tags (`Unique`,
  `SharedReadWrite`, `SharedReadOnly`), where any read through a parent tag
  `t_parent` popped all `Unique` tags above `t_parent` off the stack, and any
  write popped all tags above `t_parent`. When tested at scale against the
  Crates.io ecosystem and the Rust standard library, Stacked Borrows exhibited
  four severe **model-adequacy failures** (rejecting idiomatic, compiler-intended
  Rust patterns as UB):
  1. **Two-phase borrows and read-before-write on `&mut T`:** In safe Rust,
     `v.push(v.len())` desugars in MIR to creating a two-phase mutable borrow
     `tmp = &two_phase mut v` first, then evaluating `v.len()` via a shared
     reborrow of `v`, and finally activating `tmp` inside `Vec::push`. Under
     pure Stacked Borrows (`Unique` on `Retag`), reading `v` for `v.len()`
     popped `tmp`'s `Unique` tag before `push` could use it (`witness_5`)!
     Stacked Borrows had to fall back to a lossy `SharedReadWrite` hack for
     two-phase borrows that forfeited optimizations.
  2. **Over-eager array/struct subobject over-invalidation (`addr_of!` /
     `container_of`):** In Stacked Borrows, creating a reference `&mut s.field_a`
     and casting it to a raw pointer restricted the tag's spatial range strictly
     to `field_a` (unless `-Zmiri-tag-raw-pointers` compromises were used),
     breaking intrusive linked-list `container_of!` offset patterns where a raw
     pointer derived from a field reference accesses the enclosing struct.
  3. **Eager non-aliasing on untouched `&mut T`:** Passing an unused `&mut T`
     reference alongside a raw pointer that is only *read* invalidated the
     `&mut T` even if the `&mut T` was never written to during the call.
  4. **`Pin<&mut T>` and self-referential futures:** Polling a self-referential
     `async` state machine through `Pin::new_unchecked(&mut fut)` invalidated
     internal self-pointers stored inside `fut` under Stacked Borrows' strict
     stack pop rule.
- **Technical root cause:** A linear stack per byte confuses *temporal creation
  order* with *logical derivation hierarchy*, and treats the mere creation of a
  `&mut T` (`Retag`) as an immediate write rather than a **lazy reservation**
  that becomes exclusive only when first written. That forced Villani et al.
  (PLDI 2025) to replace Stacked Borrows with **Tree Borrows**, which:
  - Organizes tags into a **tree** (where sibling branches can be disabled
    without popping parent/ancestor branches), and
  - Replaces `Unique` with a lazy state machine `Reserved → Active → Frozen → Disabled`
    where a newly created `&mut T` starts in `Reserved` (tolerating foreign
    reads!) and transitions to `Active` only on its first child write (cutting
    ecosystem test rejections by ~54%).
- **Architectural lesson for Anneal (`L_mir` & `Compiles L_sb L_tb`):**
  1. Anneal's `L_mir` aliasing semantics in `trusted/` (or in `theory/` modular
     refinements per UC-3.1) should use `Tree Borrows`'s lazy
     `Reserved → Active → Frozen → Disabled` state machine (or support
     parameterizing the borrow-tag state machine) rather than hardcoding
     Stacked Borrows' eager stack pop into the TCB.
  2. Because `Compiles L_sb L_tb codec f f` is expressible directly in Anneal's
     `Language` refinement calculus, proofs conducted under a stricter aliasing
     discipline (or untagged memory `L_untagged` via `Abstracts L_untagged L_mir_tb`)
     compose cleanly without redoing the TCB.

#### F-2.5: Tree Borrows Function-Entry `Protector` Subtleties Across External Calls and `UnsafeCell`

Basis: **documentation** — Villani et al., *"Tree Borrows,"* PLDI 2025, DOI
`10.1145/3729338`; `simuliris-tree-borrows-selected-kernel-replay-e3abfcdc`
corpus report.

- **Historical failure:** During the design of `Tree Borrows`, making `&mut T`
  start in `Reserved` (tolerating foreign reads before the first write) created
  a subtle **compiler optimization soundness trap**: LLVM's `noalias` attribute
  on a function parameter `x: &mut T` allows the compiler to reorder or delete
  reads and writes through `x` across an opaque function call `opaque_cb()` inside
  the function body, *even if `x` was only `Reserved` (never written) in the
  source program*! If `opaque_cb()` were allowed to write to the memory of `x`
  via a parent pointer and merely transition `x` from `Reserved` to `Disabled`
  (without triggering UB because `x` is never used again), LLVM's upward motion
  of a write or load to `x` across `opaque_cb()` would be unsound! Furthermore,
  if `T` contains an `UnsafeCell`, `Reserved` behaves differently (`ReservedIM`)
  because interior mutability permits shared writes when not protected.
- **Technical root cause:** Function-argument references carry a stronger
  aliasing contract than local reborrows: a function-entry tag must remain valid
  (not `Disabled`) **for the entire duration of the function call**, even if the
  reference is never dereferenced again after an intermediate callback. Tree
  Borrows models this via a call-frame **`Protector`** attached on
  `RetagKind::FnEntry`: transitioning a *protected* tag to `Disabled` is
  **immediate UB** at the moment of the conflicting access!
- **Architectural lesson for Anneal (`StepResult.externalCall` & Call-Frame Protectors):**
  As identified in UC-3.1, when `SmallStepMachine` steps across an external or
  indirect call via `StepResult.externalCall boundaryInv branches`, active
  `Protector` tags from enclosing call frames must be enforced by `boundaryInv`
  and preserved by `branches : State → Prop`. Any external callback branch that
  would transition an active protected tag to `Disabled` must step to `.failed .ub`.

#### F-2.6: `rustc` Borrow Checker Soundness Holes (`#25860` Implied Bounds + Variance + HRTB, `#84591`, `#100013`)

Basis: **documentation** — `rust-lang/rust` issues `#25860`, `#84591`, `#100013`;
Rust Compiler Development Guide (*Implied Bounds* and *Higher-Ranked Trait
Bounds*).

- **Historical failure:** Opened in May 2015 and remaining open for over a
  decade, **`rust-lang/rust#25860`** (*"Implied bounds on nested references +
  variance = soundness hole"*) allows 100% safe Rust code (`#![forbid(unsafe_code)]`)
  to transmute a short-lived reference `&'a T` into `&'static T`, causing a
  use-after-free segfault:
  - In Rust, writing a function signature `fn helper<'a, 'b>(x: &'a &'b (), y: &'b str) -> &'a str { y }`
    requires no explicit `where 'b: 'a` clause because `rustc` assumes the
    **implied bound** `'b: 'a` from the well-formedness of the argument type
    `&'a &'b ()`.
  - Consequently, the function pointer type `for<'a> fn(&'a &'b (), &'b str) -> &'a str`
    is accepted as well-formed without checking `'b: 'a` at the call site until
    the function is called.
  - Using contravariance of function arguments (`fn(T)`) combined with
    higher-ranked lifetime binders (`for<'a>`), safe code can coerce that
    function pointer into a type where the nested reference `&'a &'b ()` is
    abstracted behind a trait projection or contravariant parameter, and then
    call it with `'a = 'static` and a short-lived `'b` **without ever
    constructing a value of type `&'static &'b ()`**!
  - Sibling soundness holes (`rust-lang/rust#84591` on supertrait upcasting with
    HRTBs and `#100013` / Polonius loan-invalidation interactions with HRTBs)
    exploit the same structural flaw: `rustc`'s trait and borrow checkers assume
    implied bounds from binder parameters without proving those bounds at binder
    instantiation sites.
- **Technical root cause:** `rustc`'s static type and borrow checker is **not
  currently sound** in the presence of higher-ranked trait bounds, implied
  bounds, and variance. Any verification tool (`Electrolysis`, `Aeneas`,
  `RustHorn`, `Creusot`, `Verus`) that treats `rustc`'s borrow checker as an
  unquestioned oracle guaranteeing memory disjointness and lifetime validity on
  safe Rust inherits `#25860` and `#84591` as soundness holes!
- **Architectural lesson for Anneal (`L_mir` & Certifying Polonius Checker UC-3.2):**
  Anneal's `trusted/lean/` **does not axiomatize `rustc` type/borrow checking as
  a proof of UB freedom**. Instead, `Trusted.CrateTheorem` is defined over
  `L_mir`'s concrete operational semantics (`SmallStepMachine`), where
  dereferencing a dangling allocation (`StorageDead` / freed `AllocId`) is
  dynamic `.failed .ub`. When a functional translator (UC-1.1) or borrow-erasure
  pass (UC-3.1/UC-3.2) relies on lifetime disjointness, that disjointness must
  be discharged in `theory/` via a kernel-checked Polonius/borrow certificate or
  dynamic region check, which fails closed if an implied bound `'b: 'a` is
  missing!

#### F-2.7: Pointer-Integer Cast Provenance Paradoxes (`llvm#34548`, `llvm#35229`, `PNVI` vs. Strict/Exposed Provenance)

Basis: **documentation** — Lee et al., *"Taming Undefined Behavior in LLVM,"*
PLDI 2017, DOI `10.1145/3062341.3062343`; Kang et al., *"Reconciling High-Level
Optimizations and Low-Level Code in LLVM,"* OOPSLA 2018, DOI `10.1145/3276495`;
LLVM bugs `#34548` and `#35229`.

- **Historical failure:** In C, C++, and Rust (`llvm#34548`, `llvm#35229`), a
  classic three-step optimization sequence in LLVM miscompiled valid programs
  that cast pointers to integers and back:
  1. Suppose allocation $p$ ends at address `0x1000` (one-past-the-end pointer
     `p_end = p + n` has numeric address `0x1000` and provenance `Alloc(p)`) and
     allocation $q$ begins immediately at address `0x1000` (`q` has numeric
     address `0x1000` and provenance `Alloc(q)`).
  2. The program casts both to integers (`ip = (uintptr_t)p_end`,
     `iq = (uintptr_t)q`), branches on `if (ip == iq)`, and inside the branch
     computes `q2 = (int*)iq` and writes `*q2 = 42`.
  3. **Pass 1 (GVN on integers):** Inside `if (ip == iq)`, Global Value
     Numbering replaces `iq` with `ip`, turning `q2 = (int*)iq` into
     `q2 = (int*)((uintptr_t)p_end)`.
  4. **Pass 2 (`InstCombine` round-trip fold `inttoptr(ptrtoint(x)) -> x`):**
     `InstCombine` folds `(int*)((uintptr_t)p_end)` to `p_end`!
  5. **Pass 3 (Alias Analysis + Dead Store Elimination):** Because `p_end` has
     provenance `Alloc(p)` (and is out-of-bounds for writing to $q$), LLVM
     concludes `*p_end = 42` is UB / cannot alias reads from `q`, and deletes
     the store `*q2 = 42`!
- **Technical root cause:** Three seemingly natural rules—(a) integer GVN
  (`ip == iq` allows substituting `ip` for `iq`), (b) round-trip pointer-integer
  cast elimination (`inttoptr(ptrtoint(x)) -> x`), and (c) provenance-based
  alias analysis (`p + n` cannot access `q`)—are **mutually inconsistent**!
  Furthermore, in C/Rust's `PNVI-ae-udi` (Exposed Provenance) model,
  `with_exposed_provenance(addr)` is often specified via *angelic
  nondeterminism* (guessing whether `0x1000` has provenance `Alloc(p)` or
  `Alloc(q)`), which breaks demonic refinement calculi (`Behavior Query Out`).
- **Architectural lesson for Anneal (`L_mir` & Sub-Domain 1 UC-3.3):**
  1. Anneal's `L_mir` keeps pointer provenance (`AllocId`) distinct from pure
     `BitVec` integers (`ptrtoint` strips `AllocId`, so `inttoptr(ptrtoint(x))`
     is *not* definitionally equal to `x`; Strict Provenance `ptr.with_addr` /
     `ptr.map_addr` preserves `AllocId` explicitly).
  2. Because `Behavior Query Out` uses **demonic** nondeterminism (`≤` requires
     all branches to be UB-free), modeling `with_exposed_provenance(addr)` as a
     demonic choice over all exposed `AllocId`s would falsely trigger UB whenever
     $\ge 2$ allocations are exposed! Instead, `L_mir` resolves exposed
     provenance deterministically to the unique live allocation whose interior
     byte range $[base, base + size)$ contains `addr` (or prevents adjacent
     allocations from sharing interior addresses).

---

### 4. Abstract Interpretation and Static Analyzer Soundness Bugs

#### F-3.1: Linux Kernel eBPF Verifier `BPF_JMP32` 32-Bit Branch Bounds Refinement Bug (`CVE-2020-8835`, `torvalds/linux@581738a681b6`)

Basis: **source** + **documentation** — `torvalds/linux` commit
`581738a681b6faae5725c2555439189ca81c0f1f` (and fix commit `3f50f132d840`); NVD
`CVE-2020-8835`.

- **Historical failure:** The Linux kernel eBPF verifier (`kernel/bpf/verifier.c`)
  is an in-kernel abstract interpreter that tracks each 64-bit register `R0..R10`
  using a reduced product of five abstract domains: 64-bit unsigned intervals
  `[umin_value, umax_value]`, 64-bit signed intervals `[smin_value, smax_value]`,
  32-bit unsigned intervals `[u32_min_value, u32_max_value]`, 32-bit signed
  intervals `[s32_min_value, s32_max_value]`, and a 64-bit tristate known-bits
  domain `var_off : tnum` (`(value, mask)` where `value & mask == 0`). In
  `CVE-2020-8835` (exploited at Pwn2Own 2020 for root local privilege
  escalation), commit `581738a681b6` added `__reg_bound_offset32` to synchronize
  32-bit bounds into `var_off` (`tnum`) after 32-bit conditional branches
  (`BPF_JMP32`), but used 64-bit `umin_value`/`umax_value` instead of
  `u32_min_value`/`u32_max_value` when intersecting `tnum` subregister masks. By
  crafting a register whose 64-bit bounds and 32-bit bounds diverged across a
  32-bit branch, an attacker forced the verifier to infer that a register equal
  to `1` at runtime was statically equal to `0`, bypassing array bounds checks
  and achieving arbitrary kernel read/write.
- **Technical root cause:** Hand-written cross-domain reduction routines
  (`__reg_bound_offset32`, `__reg_combine_64_into_32`, `reg_bounds_sync`) that
  mutually refine 5 coupled abstract domains without a mechanized proof of the
  concretization invariant $\gamma_{\text{64}} \cap \gamma_{\text{32}} \cap
  \gamma_{\text{tnum}}$ are extraordinarily error-prone: a single typo mixing a
  64-bit field with a 32-bit field collapses the abstract state to a wrong
  singleton constant.
- **Architectural lesson for Anneal (Certifying Abstract Domains UC-5.1 & UC-5.2):**
  In Anneal, abstract interpretation never runs inside `trusted/`. Instead, the
  concretization function $\gamma : \text{AbstractReg} \to (\text{BitVec 64} \to \text{Prop})$
  and every cross-domain reduction operator `syncBounds# : AbstractReg → AbstractReg`
  reside in `theory/` and must carry a Lean kernel proof (discharged via
  `bv_decide`) that $\forall x : \text{BitVec 64},\, \gamma(a)(x) \to \gamma(\text{syncBounds}^{\#}(a))(x)$.

#### F-3.2: Linux Kernel eBPF Verifier `tnum` Bitwise ALU32 Subregister Bounds Bug (`CVE-2021-3490`, `torvalds/linux@049c4e13714e`)

Basis: **source** + **documentation** — `torvalds/linux` commit
`049c4e13714ea026ddfb62fc726fb0e3f22c2861`; NVD `CVE-2021-3490`.

- **Historical failure:** In `CVE-2021-3490`, the eBPF verifier's 32-bit bitwise
  abstract transfer functions `scalar32_min_max_and`, `scalar32_min_max_or`, and
  `scalar32_min_max_xor` in `kernel/bpf/verifier.c` contained an early return:
  when both operands had known 32-bit constants according to `tnum_subreg_is_const(src_reg->var_off)`
  and `dst_reg->subreg_def`, the functions returned early without updating
  `s32_min_value`, `s32_max_value`, `u32_min_value`, and `u32_max_value` (relying
  on a later `reg_bounds_sync` call to infer the 32-bit bounds from `var_off`).
  However, because the prior `u32_min_value` and `u32_max_value` were left stale
  before `reg_bounds_sync` intersected them with the new `var_off` bounds, the
  intersection of the stale interval with the new bitwise result produced an
  inverted interval `u32_min_value > u32_max_value` (e.g., `u32_min_value = 1,
  u32_max_value = 0`), which subsequent pointer arithmetic trusted to perform
  out-of-bounds kernel memory writes.
- **Technical root cause:** Confusing **domain refinement (intersection)** with
  **state update (destructive assignment)** during a mutable transfer step:
  `reg_bounds_sync` assumes the existing `[u32_min, u32_max]` interval is already
  a sound over-approximation of the *new* register value and narrows it against
  `var_off`. Leaving the *pre-operation* interval in `[u32_min, u32_max]` and
  intersecting it with the *post-operation* `var_off` computed $I_{\text{pre}}
  \cap \gamma_{\text{tnum}}(v_{\text{post}}) = \emptyset$!
- **Architectural lesson for Anneal (`ProductiveOn` & Functional Transfer Proof in `theory/`):**
  1. In pure functional Lean (`theory/`), abstract transfer functions return a
     fresh `AbstractVal` rather than mutating fields in place and intersecting
     stale pre-state bounds with post-state `tnum` masks.
  2. Furthermore, an inverted interval (`u32_min > u32_max`) has an empty
     concretization $\gamma(a) = \emptyset$, which is the abstract-interpretation
     analog of a demonic miracle (`witness_1` / `witness_6`) and is immediately
     caught when proving transfer soundness on inhabited concrete states.

#### F-3.3: Linux Kernel eBPF Verifier 64-to-32-Bit Endpoint Truncation Bug (`CVE-2021-31440`, `torvalds/linux@10bf4e83167c`)

Basis: **source** + **execution** — `torvalds/linux` commit
`10bf4e83167cc68595b85fd73bb91e8f2c086e36`; NVD `CVE-2021-31440`;
`support/failure_mechanisms_probe.py` (`witness_6`).

- **Historical failure:** In `CVE-2021-31440`, the helper
  `__reg_combine_64_into_32(struct bpf_reg_state *reg)` attempted to tighten
  32-bit bounds `[u32_min_value, u32_max_value]` from 64-bit bounds
  `[umin_value, umax_value]`. It checked whether the lower 32 bits of
  `umin_value` and `umax_value` satisfied boundary conditions independently,
  rather than checking whether `umin_value` and `umax_value` shared the **same
  upper 32 bits** (`(umin_value >> 32) == (umax_value >> 32)`). As reproduced in
  `witness_6` (`support/failure_mechanisms_probe.py`), when a 64-bit register
  had bounds `[0x0_ffffffff, 0x1_00000000]` (straddling the $2^{32}$ boundary),
  the concrete low-32-bit values are $\{0\text{xffffffff}, 0\text{x00000000}\}$,
  which wrap around $2^{32}$! Projecting without the upper-32-bit equality check
  caused the verifier to miscalculate 32-bit bounds as a tight constant `0` or
  inverted range after a 32-bit ALU operation.
- **Technical root cause:** Modular wrap-around on subregister projection: the
  map $x \mapsto x \bmod 2^{32}$ is monotonic on an interval $[a, b] \subseteq
  [0, 2^{64}-1]$ **if and only if** $\lfloor a / 2^{32} \rfloor = \lfloor b /
  2^{32} \rfloor$.
- **Architectural lesson for Anneal (`bv_decide` Domain Verification in `theory/`):**
  When verifying the 32-bit projection operator in `theory/` via Lean 4's
  `bv_decide`, omitting the guard `(umin >>> 32) == (umax >>> 32)` immediately
  fails kernel checking and produces the exact counterexample `umin = 0xffffffff,
  umax = 0x100000000`.

#### F-3.4: Linux Kernel eBPF Verifier Nullable Pointer (`*_OR_NULL`) Arithmetic Bypass (`CVE-2022-23222`, `torvalds/linux@64620e0a1e71`)

Basis: **source** + **documentation** — `torvalds/linux` commit
`64620e0a1e712a778095bd35cbb277dc2259281f`; NVD `CVE-2022-23222`.

- **Historical failure:** In `CVE-2022-23222`, `adjust_ptr_min_max_vals` in
  `kernel/bpf/verifier.c` permitted pointer arithmetic (`BPF_ADD` / `BPF_SUB`)
  on registers carrying nullable pointer types (`PTR_TO_MEM_OR_NULL`,
  `PTR_TO_BTF_ID_OR_NULL`, `PTR_TO_SOCKET_OR_NULL`) *before* the pointer was
  checked for `NULL`. When the user program added a known offset `0` (or
  non-zero offset) to a `*_OR_NULL` pointer and then branched on `if (ptr == 0)`
  to convert the register into a known scalar `0`, the verifier's pointer-offset
  tracking corrupted the scalar range bounds, allowing arbitrary out-of-bounds
  pointer arithmetic.
- **Technical root cause:** Conflating a sum type $\text{Option}(\text{Ptr}) =
  \text{None} \mid \text{Some}(\text{AllocId}, \text{Offset})$ with a single
  pointer record whose base might be zero, and allowing offset arithmetic before
  case-splitting on the `Option` tag.
- **Architectural lesson for Anneal (`L_mir` Memory & Provenance Model):**
  In Anneal's `L_mir`, a valid pointer carries ` some allocId : Option AllocId`,
  whereas a null pointer has `allocId = none`. In `SmallStepMachine`, performing
  in-bounds pointer offset arithmetic (`PtrOffset` / `GEP`) on a pointer with
  `allocId = none` (for non-zero offset) steps immediately to `.failed .ub`.

#### F-3.5: Linux Kernel eBPF Verifier CFG State-Pruning Precision Backpropagation Bug (`CVE-2023-2163`, `torvalds/linux@71b547f56124`)

Basis: **source** + **documentation** — `torvalds/linux` commit
`71b547f561247897a0a14f3082730156c0533fed`; NVD `CVE-2023-2163`.

- **Historical failure:** To avoid exponential path explosion on large eBPF
  programs, the eBPF verifier performs **state pruning** (`is_state_visited` /
  `states_equal`): if the current abstract state $S_{\text{cur}}$ at a CFG join
  point is subsumed by a previously verified state $S_{\text{old}}$ on all
  registers marked `precise = true`, the verifier prunes the path. To know which
  registers must be tracked precisely, `mark_chain_precision` /
  `propagate_precision` walks backward along the explored execution history
  whenever a register is used in a sensitive sink (like packet/map pointer
  indexing). In `CVE-2023-2163`, `propagate_precision` failed to walk backward
  correctly across certain conditional branch / subprog jump histories, leaving
  a critical scalar register marked `precise = false` in $S_{\text{old}}$. When
  a later path arrived with an out-of-bounds value in that register,
  `states_equal` ignored the register (because `precise == false` in
  $S_{\text{old}}$) and pruned the unsafe path as "already verified"!
- **Technical root cause:** Dynamic backward precision tainting coupled with
  state-equivalence pruning is a fragile global optimization: if the backward
  walk misses *any* predecessor edge in the CFG, `states_equal` treats an
  unconstrained $\top$ bound as equivalent to a verified bound, creating an
  immediate soundness hole.
- **Architectural lesson for Anneal (Certifying Post-Fixpoint Checkers UC-5.1):**
  Anneal completely decouples *fixpoint search/pruning* (done by an untrusted
  external analyzer) from *fixpoint verification* (done by `checkNumFixpoint` in
  `theory/`). The untrusted analyzer can use whatever heuristic state pruning or
  precision tainting it likes; it must emit an explicit invariant table
  `inv : BasicBlockId → AbstractVal` to `theory/`, where `checkNumFixpoint`
  locally verifies $F^{\#}(\text{inv}[bb]) \sqsubseteq^{\#} \text{inv}[bb']$ on
  **every** CFG edge $(bb, bb')$ and verifies that $\text{inv}[bb]$ discharges
  all UB guards inside $bb$. If pruning dropped a precision bit needed at a downstream
  sink, the local check at that sink or join edge fails closed in the Lean
  kernel!

#### F-3.6: Automated Discovery of Unsound Kernel `tnum` Abstract Operators (`Agni`, CGO 2022 & CAV 2023)

Basis: **documentation** — Vishwanathan et al., *"Sound, Precise, and Fast
Abstract Interpretation with Tristate Numbers,"* CGO 2022, DOI
`10.1109/CGO53902.2022.9741267`; Vishwanathan et al., *"Verifying the Verifier:
eBPF Range Analysis Verification,"* CAV 2023, DOI
`10.1007/978-3-031-37709-9_12`.

- **Historical failure:** When Vishwanathan et al. built **Agni** to extract the
  Linux kernel's C range-analysis and `tnum` operators into SMT bitvector
  formulas and verify their soundness across kernel versions 4.14 through 5.19,
  they discovered multiple previously unknown soundness bugs and precision
  anomalies in `tnum_mul` (tristate multiplication), `scalar_min_max_and`,
  `scalar_min_max_or`, `scalar_min_max_xor`, and 32/64-bit synchronization
  routines where the kernel's abstract output violated the Galois/concretization
  soundness condition $\forall x \in \gamma(a),\, y \in \gamma(b) \implies
  (x \oplus y) \in \gamma(a \oplus^{\#} b)$.
- **Technical root cause:** Implementing bit-level abstract transformers in C
  without mechanized bitvector verification against the concrete ALU semantics
  inevitably introduces sign-extension, overflow, and bitmask propagation bugs.
- **Architectural lesson for Anneal (`bv_decide` Constructive Domain Proofs):**
  As designed in UC-5.2, Anneal's `KnownBits` (`tnum`) and interval abstract
  transformers are written in pure Lean 4 in `theory/` and proved sound once and
  for all against `BitVec 64` operations using `bv_decide` (checked LRAT
  certificates in the Lean kernel), providing permanent immunity against
  `Agni`-class abstract operator bugs.

#### F-3.7: Widening Precision Collapse and Unmodeled Library Stubs (`Astrée`, `Frama-C Eva`, `IKOS`, `MIRAI`)

Basis: **documentation** — Cousot et al., *Astrée* experience reports; NASA
`IKOS` and Frama-C `Eva` documentation; Meta `MIRAI` repository archive.

- **Historical failure:** Industrial abstract interpreters face a dual failure
  mode between **widening precision collapse** (usability failure) and **missing
  library/environment models** (soundness failure):
  1. **Threshold widening collapse (`Astrée`, `Frama-C Eva`, `IKOS`):** To force
     termination on loops, interval/octagon widening $\nabla$ extrapolates
     changing bounds to $\pm \infty$ or fixed thresholds. When a Rust or C loop
     index depends on a dynamic slice length `i < slice.len()` or nonlinear
     stride, non-relational interval widening widens `i` to `[0, +∞]`, causing
     cascade false-positive alarms on every subsequent array access unless
     relational domains (Octagons/Polyhedra) or manual loop unrolling directives
     are supplied.
  2. **Unmodeled standard-library and intrinsic stubs (`MIRAI`, `IKOS`):** Meta's
     `MIRAI` abstract interpreter for Rust MIR (eventually archived) and C++
     uses of `IKOS` suffered soundness gaps whenever an analyzed function called
     an unmodeled `core`/`std` intrinsic or trait method whose default fallback
     summary under-approximated heap mutations or assumed normal return without
     panicking.
- **Architectural lesson for Anneal (`VerificationResult` + `StepResult.externalCall`):**
  1. Because Anneal's certifying abstract interpreter (UC-5.1) checks
     *Farkas-witnessed relational polyhedra/octagon invariants* emitted by an
     offline solver rather than running fixed widening heuristics inside the
     Lean kernel, precision can be refined offline without touching the TCB.
  2. Any unverified external or `std` callee in `L_mir` steps via
     `StepResult.externalCall boundaryInv branches` (or creates an explicit
     obligation in `VerificationResult`), preventing silent under-approximating
     fallback stubs.

---

### 5. Usability, Proof-Maintenance, and Expressiveness Failures

#### F-4.1: Functional Lens Explosion and Interior-Mutability Expressiveness Wall (`Electrolysis`, Ullrich 2016)

Basis: **documentation** — Ullrich, *"Simple Verification of Rust Programs via
Functional Purification"* (`Electrolysis`), Master's Thesis, Karlsruhe Institute
of Technology (KIT), 2016 (`kha/electrolysis`).

- **Historical failure:** `Electrolysis` was the pioneering translator from Rust
  MIR into pure Lean 2 definitions. It translated mutable references `&mut T`
  into functional **lenses** (`Lens S T` with `get : S → T` and
  `set : S → T → S`). While effective on small functional data structures (like
  binary search trees and `VecDeque`), `Electrolysis` hit three architectural
  walls that led to its abandonment:
  1. **No semantic foundation for `unsafe` or interior mutability:** Because the
     entire target language was pure functional Lean without an underlying
     machine/heap semantics, `Electrolysis` could not verify the actual `unsafe`
     implementations of `Vec<T>`, `Cell<T>`, `RefCell<T>`, `Rc<T>`, or `Arc<T>`;
     those types had to be axiomatized by hand as trusted functional primitives.
  2. **Combinatorial lens explosion on reborrows and struct projections:**
     Functions returning mutable borrows from multiple branches or storing
     mutable borrows inside structs/iterators (`IterMut<'a, T>`) required
     dynamic lens composition whose lens-law proof obligations grew rapidly.
  3. **Unverified direct MIR-to-Lean AST translation:** The Rust-to-Lean
     transpiler was an unverified Rust binary; any bug in how `Electrolysis`
     reconstructed loops or borrow lifetimes silently produced a Lean function
     whose behavior differed from the compiled Rust code.
- **Architectural lesson for Anneal (`L_mir` Base + Certifying `Abstracts L_pure L_mir`):**
  Anneal solves all three problems by making operational `L_mir`
  (`SmallStepMachine`) the ground truth in `trusted/lean/` and treating pure
  functional translation (UC-1.1) as an **upward abstraction (`Abstracts L_pure L_mir codec f_pure f_mir`)
  proved in `theory/`**:
  - When a Rust function is safe and borrow-structured, `Abstracts L_pure L_mir`
    gives the user a pure Lean 4 function `f_pure` to reason about, **backed by
    a machine-checked proof** that `f_mir` refines `f_pure`.
  - When a function uses `unsafe` raw pointers, `UnsafeCell` interior
    mutability, or custom ownership (`Vec`, `Arc`, `GhostCell`), the user proves
    its spec in `theory/` using separation logic (UC-2.1/UC-2.2) or symbolic
    bitvector execution (UC-1.4) over the *exact same* `L_mir` language, and
    safe callers compose with that verified spec seamlessly!

#### F-4.2: Monolithic Viper Encoding Bottlenecks and Proof-Maintenance Collapse (`Prusti` Legacy vs. Rewrite)

Basis: **documentation** — Astrauskas et al., *"Leveraging Rust Types for
Modular Specification and Verification"* (`Prusti`), OOPSLA 2019;
`viperproject/prusti-dev` architecture redesign notes.

- **Historical failure:** Early versions of `Prusti` encoded each Rust MIR
  function—together with all implicit borrow-checker lifetime expiration loans,
  type invariants, and recursive predicate fold/unfold heuristics—into a single
  monolithic `Viper` method verified by `Silicon` (symbolic execution) or
  `Carbon` (Boogie VCGen). On realistic Rust functions with nested branches,
  loops, and trait calls, the automatically inferred `fold`/`unfold` footprint
  heuristics either failed with opaque Viper permission errors that users could
  not map back to Rust source lines, or triggered exponential Z3 branch/quantifier
  timeouts, prompting a major architectural rewrite of `Prusti`.
- **Architectural lesson for Anneal (`VerificationResult` Granular Obligations):**
  Anneal avoids monolithic black-box VC generation: `VerificationResult`
  decomposes verification into fine-grained, span-tagged `Obligation` propositions
  in `theory/`, where decidable sub-goals (bounds, alignment, bitmasks) are
  discharged by fast reflective checkers (`bv_decide`, `omega`, `checkSymHeapCert`)
  and complex algorithmic invariants are proved interactively in Lean 4.

#### F-4.3: Reference-Synthesizing Frontend Rewrites and Silent Partial Extraction (`Aeneas` & `Charon` `#583`, `#534`)

Basis: **source** + **documentation** —
`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`,
`charon/src/options.rs`,
`charon/src/transform/simplify_output/index_to_function_calls.rs`,
`charon-ml/src/OfJson.ml`; Charon issues `#583` and `#534`; corpus report
`charon-support-and-unsoundness-nightly-2026-06-03`.

- **Historical failure:** As established in our corpus report
  `charon-support-and-unsoundness-nightly-2026-06-03`, the `Charon` MIR
  extractor (`0.1.210`, pinned by `Aeneas` `nightly-2026.06.03`) exhibits three
  severe frontend-pipeline hazards:
  1. **UB-introducing indexing transformation (`Charon #583`):** `Preset::Aeneas`
     enables `--index-to-function-calls`, which rewrites array/slice place
     indexing `(*raw_ptr)[i]` by synthesizing a shared or mutable reference
     `&(*raw_ptr)[i]` and passing it to a helper function—a transformation whose
     own source comment warns *"may introduce UB"* when indexing behind a raw
     pointer.
  2. **Bound-lifetime erasure in associated-type normalization (`Charon #534`):**
     `expand_associated_types.rs` erases higher-ranked bound lifetimes (`for<'a>`)
     inside associated type equalities (`T: for<'a> Trait<'a, Type = &'a ()>`).
  3. **Fail-open partial extraction (`OfJson.ml`):** By default, `Charon`
     continues after item translation panics/errors, serializes an LLBC JSON
     file with `"has_errors": true` and `Body::Error` placeholders, and exits
     with status `0`, while `Aeneas`'s `charon-ml/src/OfJson.ml` parser discards
     the third JSON field (`has_errors`)!
- **Architectural lesson for Anneal (`trusted/rustc-capture/` & `trusted/audit/`):**
  `anneal-rustc-capture` operates as a fail-closed extractor over
  `Runtime(PostCleanup)` MIR without running reference-synthesizing AST passes,
  and `trusted/cargo-anneal` + `trusted/audit` require `Trusted.CrateTheorem` to
  cover every captured function in the crate without `Body::Error` omissions.

#### F-4.4: Pure Functionalization Boundaries on Raw Pointers and Cyclic/Interior Mutability (`Aeneas` & `RustHorn`)

Basis: **documentation** — Ho and Protzenko, *"Aeneas: Rust Verification by
Functional Translation,"* ICFP 2022, DOI `10.1145/3547647`; Matsushita, Tsukada,
and Kobayashi, *"RustHorn: CHC-Based Verification for Rust Programs,"* TOPLAS
2021.

- **Historical failure:** Both `Aeneas` (backward functions) and `RustHorn`
  (first-order prophecies) rely fundamentally on the invariant that **no two
  live pointers alias the same mutable memory location unless one is a direct
  reborrow of the other**. Consequently, neither technique can directly
  translate:
  - Unsafe raw-pointer graphs (`*mut Node`), doubly-linked lists, or intrusive
    kernel data structures;
  - Shared interior mutability (`UnsafeCell<T>`, `Cell<T>`, `RefCell<T>`,
    `Mutex<T>`, `AtomicUsize`); or
  - Low-level byte-manipulation and zero-copy transmutation (`zerocopy`,
    `MaybeUninit`).
- **Architectural lesson for Anneal (Multi-Modal Composition via `Language SemObs`):**
  Anneal does not force an entire Rust crate through a single verification
  paradigm. Because `Language SemObs` and `BehaviorCodec` provide a uniform
  semantic interface in `trusted/lean/`, a single crate can verify its low-level
  `unsafe` pointer/byte primitives via Iris separation logic (UC-2.1) or
  `bv_decide` symbolic execution (UC-1.4) and expose clean `SpecOn` / `Abstracts`
  summaries that `Aeneas`-style functional translations (UC-1.1) consume for
  high-level algorithmic callers.

#### F-4.5: The SMT "Butterfly Effect," Trigger Matching Loops, and Proof Instability (`IronFleet`, `Dafny`, `Verus`, `Mariposa`)

Basis: **documentation** — Hawblitzel et al., *"IronFleet: Proving Practical
Distributed Systems Correct,"* SOSP 2015, DOI `10.1145/2815400.2815428`; Leino
and Pit-Claudel, *"Trigger Selection Strategies to Stabilize Program Verifiers,"*
CAV 2016, DOI `10.1007/978-3-319-41528-4_20`; Zhou et al., *"Mariposa: Measuring
and Mitigating SMT Instability,"* OOPSLA 2023, DOI `10.1145/3622852`.

- **Historical failure:** Large-scale SMT-based verification projects (`IronFleet`,
  `Komodo`, `VeriBetrKV` in `Dafny`, and systems proofs in `Verus` and `F*`)
  universally report **SMT instability ("the butterfly effect")** as their single
  largest engineering cost:
  - In `IronFleet` (SOSP 2015) and `Dafny` (CAV 2016), renaming a local variable,
    reordering two independent `assert` statements, or upgrading Z3's minor
    version changed hash-table ordering and E-matching quantifier instantiation
    priorities inside Z3, causing proofs that previously succeeded in 1.2
    seconds to time out after 60 seconds (`matching loops`).
  - In `Mariposa` (OOPSLA 2023), testing semantics-preserving mutations
    (variable alpha-renaming, assertion shuffling, random seed permutation)
    across large `Dafny`, `Verus`, `F*`, and `Serval` benchmarks revealed that a
    significant fraction of nontrivial quantified VCs exhibit high variance or
    spurious failure under trivial syntactic perturbations.
- **Technical root cause:** Entrusting proof checking to a time-bounded,
  heuristic SMT search procedure at every compile means a "proof" is not a
  durable mathematical object—it is a fragile coincidence that a heuristic search
  converged within $T$ seconds on a specific machine load and solver binary.
- **Architectural lesson for Anneal (Durable Kernel Certificates in `theory/`):**
  Anneal never runs time-bounded heuristic SMT search inside its trusted
  verification check. When an external solver (`Bitwuzla`, `CaDiCaL`, `cvc5`,
  `Z3`) is used during development, its output is a **static, deterministic
  certificate** (`LRAT` bit-blasting trace, `Alethe` proof DAG, ground
  instantiation witness $\vec{t}_j$, or Farkas multiplier vector $\vec{\lambda}$)
  checked in linear/polynomial time by Lean 4's kernel reducer (`decide` /
  `bv_decide`). Variable renaming or host CPU load cannot cause a checked Lean
  kernel proof or `LRAT` certificate to flip from valid to invalid.

#### F-4.6: Cross-Version Proof Session and Compiler Nightly Drift (`Why3`, `F*`, `Creusot`)

Basis: **documentation** — Bobot et al., *"Preserving User Proofs Across
Specification Changes,"* VSTTE 2013, DOI `10.1007/978-3-642-54108-7_10`; corpus
report `why3-durable-proof-sessions-2011-2025`.

- **Historical failure:** In `Why3` and `Creusot`, user proof sessions are stored
  as XML trees (`why3session.xml`) keyed by VC goal shapes and transformation
  hashes. When `rustc` updates its MIR lowering or `Creusot` adjusts its WhyML
  translation, goal shapes shift across the crate, leaving orphaned proof nodes
  in `why3session.xml` and forcing manual interactive session repair.
- **Architectural lesson for Anneal (`VerificationResult` & Compositional `Abstracts`):**
  By anchoring functional abstractions (`Abstracts L_pure L_mir`) at stable
  function-signature boundaries and discharging low-level MIR stepping via
  automated per-function simulation tactics in `theory/`, user-authored interactive
  Lean 4 theorems reason over the stable pure model `f_pure` rather than brittle
  basic-block numbers in `MirBody`.

---

### 6. Deterministic Mathematical Witnesses for the Six Core Failure Mechanisms

Basis: **execution** — `support/failure_mechanisms_probe.py` and
`support/probe-results.json`.

To make the six cross-cutting failure mechanisms concretely auditable and
reproducible without external solver installations,
`support/failure_mechanisms_probe.py` executes six deterministic finite
models comparing naive verification checks against Anneal's four `trusted/`
primitives:

| Witness ID | Historical Failure Mode Modeled | Naive Verification Gate Result | Anneal `trusted/` Primitive Gate Result | Discriminating Primitive |
| :--- | :--- | :--- | :--- | :--- |
| `witness_1_prophecy_vacuity` | Over-constrained prophecy / demonic miracle (`(sem q).val h = ∅`) proving `ensures false` (F-1.4, F-1.5) | `naive_vc_accepts_ensures_false: true` | `anneal_productive_on_accepts: false` | `L.ProductiveOn pre prog` |
| `witness_2_contradictory_pre` | Contradictory refinement / prelude axiom (`q > 10 ∧ q < 5`) on a UB program (F-1.1, F-1.7) | `spec_on_vacuously_holds: true`, `productive_on_vacuously_holds: true` | `anneal_inhabited_pre_accepts: false` | `InhabitedPre pre` |
| `witness_3_antecedent_waiver` | Waived false lemma (`ob_1 = False`) discharging unwaived buggy check (`ob_2 = False`) via antecedent implication (F-1.4) | `antecedent_waiver_accepts_unwaived_bug: true` | `anneal_positive_verification_result_accepts: false` | `VerificationResult` positive disjunction |
| `witness_4_reentrancy_unwind` | Mid-method broken `AdtInv` (`len = 2 > init = 1`) across callback and unwind path (`Vec::dedup_by`, F-2.3) | `naive_normal_post_only_accepts: true` | `anneal_external_call_boundary_inv_accepts: false`, `anneal_unwind_terminal_check_accepts: false` | `StepResult.externalCall` `boundaryInv` + `Terminal.panic` |
| `witness_5_stacked_vs_tree_borrows` | Two-phase borrow read-before-write (`v.push(v.len())`) under Stacked Borrows vs. Tree Borrows (F-2.4) | `stacked_borrows_accepts_two_phase_pattern: false` (false-positive UB) | `tree_borrows_accepts_two_phase_pattern: true`, `tree_borrows_state_after_conflicting_read: "Disabled"` | `Tree Borrows` `Reserved → Active` transition |
| `witness_6_ebpf_cve_2021_31440` | 64-to-32-bit interval projection on `[0x0_ffffffff, 0x1_00000000]` without upper-32-bit guard (`CVE-2021-31440`, F-3.3) | `buggy_64_to_32_projection_sound: false` | `fixed_64_to_32_projection_sound: true` | `bv_decide` domain soundness theorem |

## Boundaries

- **Not examined:** Live execution of historical buggy versions of `Dafny`,
  `Verus`, `Creusot`, `Prusti`, `Kani`, `F*`, or vulnerable Linux kernels
  (`5.5`–`6.3`). All tool bugs and CVEs are established from primary upstream
  commit diffs, CVE records, issue trackers, and peer-reviewed postmortems,
  paired with the self-contained mathematical witnesses in
  `support/failure_mechanisms_probe.py`.
- **Known not to apply:** Anneal's four `trusted/lean/` primitives prevent
  vacuous specifications, antecedent waiver contamination, silent callback
  re-entrancy, and unverified VC/domain lowering only when `L_mir` in
  `trusted/lean/` and `anneal-rustc-capture` faithfully capture the target Rust
  program's operational semantics. A bug inside `trusted/lean/`'s own definition
  of `L_mir` or `anneal-rustc-capture`'s MIR serialization remains inside the
  TCB and must be mitigated via TCB semantic mutation testing (`#228`) and
  differential Miri conformance testing (`#229`).
- **Unsupported:** Treating `rustc`'s built-in borrow checker or type checker as
  an unverified axiom of memory disjointness for arbitrary higher-ranked trait
  bounds (`rust-lang/rust#25860`, `#84591`) without an accompanying `L_mir`
  operational or Polonius certificate check.

## Evidence

Observed 2026-10-31. Primary sources, immutable commits, DOIs, and executable
package artifacts:

| Subject / Claim | Primary Coordinate / Identifier | Evidence Role |
| :--- | :--- | :--- |
| Anneal `trusted/` boundary and workspace | `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`, `trusted/lean/Trusted.lean`, `trusted/audit/TrustedBoundary.lean` | source |
| `Dafny` prelude axiom & solver soundness bugs | `dafny-lang/dafny` issues `#6534` (`$Box($Unbox(x))`), `#6537` (`Map#Items`), `#4053` (`smt.arith.solver=6`) | documentation |
| `Verus` ghost erasure, `Tracked`, and SMT trust | `verus-lang/verus@0141ebc6f14410dfc87fef1da57408578002eb7c`, `builtin/src/lib.rs:546–570`, `air/src/smt_verify.rs:249–364`; arXiv `2303.05491v2` | source + documentation |
| `Creusot` & `RustHornBelt` prophetic borrows | Matsushita, Denis, Jourdan, and Dreyer, PLDI 2022, DOI `10.1145/3519939.3523704`; `creusot-rs/creusot` `label:soundness` | documentation |
| `Boogie` & `Viper` failure-reflection certificates | Parthasarathy et al., CAV 2021 (DOI `10.1007/978-3-030-81688-9_33`) and PLDI 2024 (DOI `10.1145/3656438`) | documentation |
| `Kani` soundness false-negative tracker | `model-checking/kani` issues under label `[F] Soundness` | documentation |
| `F*` reflection and VC-simplifier soundness bugs | `FStarLang/FStar` issues `#4478`, `#4485`, `#4487` (`kind/unsoundness`) | documentation |
| `RustBelt` `MutexGuard::map` & `Arc::get_mut` bugs | Jung et al., POPL 2018 (DOI `10.1145/3158154`, `rust-lang/rust#25760`); Dang et al., POPL 2020 (DOI `10.1145/3371102`, `rust-lang/rust#51780`) | documentation |
| `Stacked Borrows` vs. `Tree Borrows` | Jung et al., POPL 2020 (DOI `10.1145/3371109`); Villani et al., PLDI 2025 (DOI `10.1145/3729338`) | documentation |
| `rustc` implied bounds & HRTB soundness bugs | `rust-lang/rust` issues `#25860`, `#84591`, `#100013` | documentation |
| LLVM/C/Rust pointer provenance miscompilations | Lee et al., PLDI 2017 (DOI `10.1145/3062341.3062343`); Kang et al., OOPSLA 2018 (DOI `10.1145/3276495`); `llvm#34548`, `llvm#35229` | documentation |
| Linux eBPF verifier soundness CVEs | `torvalds/linux` commits `581738a681b6` (`CVE-2020-8835`), `049c4e13714e` (`CVE-2021-3490`), `10bf4e83167c` (`CVE-2021-31440`), `64620e0a1e71` (`CVE-2022-23222`), `71b547f56124` (`CVE-2023-2163`) | source + documentation |
| `Agni` eBPF `tnum` & range analysis verification | Vishwanathan et al., CGO 2022 (DOI `10.1109/CGO53902.2022.9741267`) and CAV 2023 (DOI `10.1007/978-3-031-37709-9_12`) | documentation |
| `Charon` & `Aeneas` extraction hazards | `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`#583`, `#534`, `OfJson.ml`); Ho and Protzenko, ICFP 2022 (DOI `10.1145/3547647`) | source + documentation |
| SMT instability & trigger selection (`Mariposa`) | Hawblitzel et al., SOSP 2015 (DOI `10.1145/2815400.2815428`); Leino and Pit-Claudel, CAV 2016 (DOI `10.1007/978-3-319-41528-4_20`); Zhou et al., OOPSLA 2023 (DOI `10.1145/3622852`) | documentation |
| Six mathematical failure-mechanism witnesses | `support/failure_mechanisms_probe.py` and `support/probe-results.json` | execution |

## Revalidation

1. **Rerun the deterministic mathematical witnesses:**
   ```console
   python3 reports/anneal-deductive-logics-types-abstract-interp-verification-failures-2026/support/failure_mechanisms_probe.py
   ```
   Verify that the script exits with code `0` and reproduces
   `support/probe-results.json` byte-for-byte, confirming that each naive gate
   accepts the unsound/vacuous construction while the corresponding Anneal
   primitive (`ProductiveOn`, `InhabitedPre`, positive `VerificationResult`,
   `StepResult.externalCall`, `Tree Borrows` `Reserved`, and guarded 64-to-32
   interval projection) rejects it.
2. **Audit `trusted/lean/` primitive invariants on future Anneal revisions:**
   Whenever `Trusted/Refinement.lean` or `Trusted/StepResult.lean` is modified,
   verify that:
   - `Trusted.CrateTheorem` requires `InhabitedPre pre` and `ProductiveOn pre`
     alongside behavioral refinement (`SpecOn` / `Abstracts` / `Compiles`);
   - `VerificationResult` remains positively polarity-isolated (`ob.id ∈ waived ∨ ob.prop`)
     and never injects waived obligations as hypotheses into the context of
     unwaived obligations; and
   - `StepResult.externalCall` evaluates `boundaryInv : Bool` before branching
     to `branches : State → Prop` and transitions to `.failed .ub` when
     `boundaryInv = false`.

*Authored by an AI agent acting on joshlf's behalf.*
