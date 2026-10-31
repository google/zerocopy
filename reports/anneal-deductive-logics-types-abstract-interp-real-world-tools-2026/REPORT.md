# Deductive verification, program logics, type systems, and abstract interpretation tools mapped onto Anneal's four-primitive trusted core

## Summary

Every major deductive verifier, separation-logic framework, borrow-and-aliasing
model, refinement or typestate checker, sound abstract interpreter, and
verification-condition generator (VCGen) across the Rust, C, LLVM, and
interactive-theorem-proving ecosystems reduces to constructing, composing, or
discharging edges in Anneal's four-primitive `trusted/lean/` foundation—without
adding separation logic, predicate transformers, borrow trees, or abstract
domains to the Trusted Computing Base (TCB):

1. **`Language (SemObs : Type)` and `BehaviorCodec L₁ L₂`
   (`Trusted/Refinement.lean`):**
   - `Language SemObs` packages `Prog : Type`, `Query : Type`, `Out : Type`, an
     observation classifier `obs : Out → SemObs`, and a semantic function
     `sem : Prog → Behavior Query Out` where
     `Behavior Query Out := Query → Partial (Out → Prop)`.
   - `BehaviorCodec L₁ L₂` pairs a query retraction
     (`decodeQuery (encodeQuery q₁) = q₁`) with a partial outcome bijection
     (`decodeOut (encodeOut o₁) = some o₁` and
     `decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`) that preserves the
     observable spine (`obs_decodeOut : decodeOut o₂ = some o₁ →
     L₂.obs o₂ = L₁.obs o₁`).
   - Downward/horizontal compilation (`Compiles L₁ L₂ codec s t`) and upward
     abstraction (`Abstracts L_v L_src codec v s`) are dual instances of the
     single behavioral refinement inequality
     `L_low.sem t ≤ codec.toMorphism (L_high.sem s)`.

2. **`Language.ProductiveOn` and `InhabitedPre` (`Trusted/Refinement.lean`):**
   - `InhabitedPre pre := ∃ q, pre q`.
   - `L.ProductiveOn pre prog := ∀ q, pre q → ∃ h : (L.sem prog q).defined,
     ∃ o : L.Out, (L.sem prog q).val h o`.
   - Under the order isomorphism between `Behavior Query Out` and monotonic
     predicate transformers, `ProductiveOn` is exactly Dijkstra's Law of the
     Excluded Miracle ($\neg \text{wp}(p, \text{False})$). It blocks
     unsatisfiable prophecy constraints in functional translators (`RustHorn`,
     `Creusot`), prevents contradictory refinement preconditions (`Flux`,
     `Liquid Haskell`) via `InhabitedPre`, and yields **exact determinism as a
     free theorem** whenever composed with a singleton specification.

3. **Positive per-obligation `VerificationResult`
   (`Trusted/Refinement.lean`):**
   - `VerificationResult policy waived obligations :=
     AllHold (waived.map policy.isAllowed) ∧
     AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))`.
   - Replaces antecedent `hTcb → ...` implications so an omitted or waived
     obligation (`ob.id ∈ waived`) cannot discharge other obligations by the
     Principle of Explosion, and allows independent analyzers (e.g., intervals
     in `UC-5.1` and `KnownBits` in `UC-5.2`) to discharge disjoint obligations
     within the same function.

4. **`SmallStepMachine` with `EventualBehaviorOf` and
   `StepResult.externalCall` (`Trusted/StepResult.lean`):**
   - `EventualBehaviorOf` sets `Query := State`, `Out := EventualOut Obs Val`
     (`.terminated (trace : List Obs) (term : Terminal Val)` or `.diverges`),
     and `SemObs := EventualOut Obs Unit`. Because `.failed .ub` and `.stuck`
     make `defined = False` while `.diverges` is a defined outcome in
     `EventualOut`, prefix safety is cleanly decoupled from termination—matching
     step-indexed Iris adequacy (`UC-2.1`) and 1-step abstract-interpretation
     invariants (`UC-5.1`).
   - `StepResult.externalCall (boundaryInv : Bool) (branches : State → Prop) :=
     if boundaryInv then .choice .demonic branches else .failed .ub` enforces
     open-world call-site invariants (`AdtInv` re-entrancy guards in `UC-6.4`,
     Tree Borrows protectors in `UC-3.1`, MMIO/DMA typestates in `UC-4.2`, and
     library safety preconditions in `UC-5.4`) at the exact transition of an
     external call.

Five cross-cutting constraints govern how tools in `theory/` instantiate these
four primitives:

- **The `BehaviorCodec` query-retraction and partial-bijection laws:** Because
  `decodeQuery (encodeQuery q₁) = q₁` requires $|L_1.\text{Query}| \le
  |L_2.\text{Query}|$, upward abstractions (`Abstracts L_v L_mir`) cannot add
  unconstrained ghost state to `L_v.Query`; ghost state (`Fractional`
  permissions, `BorrowTree` tags) must either be initialized deterministically
  inside `L_v.sem`, quantified internally via demonic/angelic choice, or framed
  horizontally via `Compiles L_mir L_ghost`. Similarly, because
  `decodeOut o₂ = some o₁ → encodeOut o₁ = o₂` forbids many-to-one outcome
  maps, uninitialized struct padding bytes (`MiniRust`, `CompCert Memdata`) or
  erased ghost metadata must either be projected out of `L_mir.Out` before the
  codec boundary or retained in `L_v.Out` and quotiented in `L_v.obs`.
- **Fuel exhaustion Polarity (`Abstracts` vs. `Compiles`):** In upward
  abstraction (`Abstracts L_loop L_mir`), exhausting loop fuel in `L_loop` must
  map to demonic universal choice (`defined := True`, `val := fun _ => True` or
  `.diverges`), never `.stuck` (`defined := False`), whereas bounded model
  checkers (`Kani`, `crux-mir`) restrict `Query` to bounded-unroll inputs.
- **Angelic vs. demonic provenance (`with_exposed_provenance`):** Because
  `Behavior Query Out` orders nondeterminism demonically, modeling C/Rust
  exposed provenance (`PNVI-ae-udi`, `Cerberus`, `MiniRust`) as a demonic choice
  over all exposed `AllocId`s would falsify `defined` whenever two allocations
  are exposed; `L_mir` must resolve exposed provenance deterministically from
  the unique live allocation covering the target address.
- **Trace safety on diverging loops without coinductive streams:** Although
  `EventualOut.diverges` omits `List Obs`, encoding temporal protocol guards
  (`DMA` pinning, `MMIO` sequencing, `AdtInv`) into `boundaryInv` of
  `StepResult.externalCall` converts any finite-prefix protocol violation on a
  diverging loop into `.failed .ub` (`defined = False`).
- **Diverging external callees in total-correctness proofs:** For termination
  verifiers (`UC-6.3`) to remain sound across `StepResult.externalCall`, any
  external callee that may diverge must either include a diverging transition in
  `branches` or carry an explicit termination obligation in
  `VerificationResult`.

## Applicability

This report applies to the design of verification engines, specification
languages, and certificate checkers in Anneal's `theory/` layer targeting
Anneal's `trusted/lean/` boundary (`joshlf/anneal` repository revision
`24367bd1a8c784f2578535954f9915e24894a56f`, baseline refinement definitions in
worktree revision `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` at
`trusted/lean/Trusted/Refinement.lean` and
`trusted/lean/Trusted/StepResult.lean`, and the four-primitive model-refined
architecture in `Trusted/Refinement.lean` and `Trusted/StepResult.lean`
synthesized in `anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026`
and `anneal-structural-external-calls-and-tcb-mutation-testing-2026`).

The 28 external tool-family subjects in `REPORT.json` are examined as
comparative architectural specimens and source-of-truth implementations across
six verification families (`UC-1.1` through `UC-6.4`):

1. **Category A (`UC-1.1`–`UC-1.4`):** Functional translators and symbolic
   evaluators (`Aeneas`, `Charon`, `RustHorn`, `RustHornBelt`, `Creusot`/`Coma`,
   `coq-of-rust`/`rocq-of-rust`, `Electrolysis`, `hacspec`/`hax`,
   `AutoCorres`/`AutoCorres2`, `Interaction Trees`/`Vellvm`,
   `FreeSpec`/`DimSum`, `Lean 4 bv_decide`, `SAW`/`Crucible`/`crux-mir`, `Kani`,
   `Rosette`/`Serval`, `HolBA`/`Islaris`/`Sail`).
2. **Category B (`UC-2.1`–`UC-2.4`):** Separation logics and spatial resource
   engines (`Iris`/`MoSeL`, `iris-lean`, `RustBelt`, `RefinedC`/`Caesium`,
   `RefinedRust`, `VST`, `CN`/`Fulminate`, `VeriFast`, `Viper`/`Prusti`,
   `Gillian`/`Gillian-Rust`, `Smallfoot`/`Infer`/`Pulse`, `VerCors`,
   `Steel`/`Pulse` in F\*, `GhostCell`/`qcell`, `Verus` `Tracked<PointsTo<T>>`
   and `PCell`).
3. **Category C (`UC-3.1`–`UC-3.4`):** Aliasing and borrow models (`Miri`,
   `Stacked Borrows`, `Tree Borrows`, `BorrowSanitizer`, `Polonius`,
   `Oxide`/`Patina`, `Aquascope`, `Strict/Exposed Provenance`, `VIP`,
   `CompCertS`/`Quasi-Concrete`, `CHERI`/`Morello`, `MiniRust`, `Cerberus`,
   `CompCert Memdata`).
4. **Category D (`UC-4.1`–`UC-4.4`):** Type systems, typestates, and effect
   checkers (`Flux`, `Liquid Haskell`, `Stainless`, `embedded-hal`/`embassy`,
   `Verus tokenized_state_machine!`, `Austral`/`Vale`, `no-panic`,
   `rtsan`/`cargo-call-stack`, `F*`/`Low*`/`KaRaMeL`, `Koka`/`Effekt`).
5. **Category E (`UC-5.1`–`UC-5.4`):** Sound static analyzers and abstract
   interpreters (`Verasco`, `Astrée`, `Crab`/`SeaHorn`, `IKOS`, `MIRAI`,
   `eBPF tnum`/`Agni`/`PREVAIL`, `LLVM KnownBits`, `Frama-C Eva`, `Goblint`,
   `Mopsa`, `Rudra`/`SafeDrop`/`Lockbud`, `TVLA`/`Forester`, `MemCAD`/`Xisa`).
6. **Category F (`UC-6.1`–`UC-6.4`):** VCGens, characteristic formulae,
   termination engines, and modular object invariants (`F*`/`DM4All`, `Why3`,
   `Boogie`, `Lean 4 MPL`/`Std.Do`, `CFML 2.0`/`SPLean`, `CakeML CF`,
   `AProVE`/`Ultimate Automizer`, `CeTA`/`IsaFoR`, `Foetus`,
   `Terminator`/`RankFinder`, `Dafny`/`VCC`).

Claims about each external tool apply to its pinned repository revision or
published paper in `REPORT.json`; architectural mappings onto Anneal's four
primitives are `derived` engineering designs for `theory/` verified against the
definitions in `Trusted/Refinement.lean` and `Trusted/StepResult.lean`.

## Findings

### 1. Cross-cutting mathematical foundations of the four-primitive mapping

#### 1.1 The `BehaviorCodec` query-retraction and partial-bijection laws

In `Trusted/Refinement.lean`, `Language (SemObs : Type)` equips a language's
outcome type `Out` with an observation projection `obs : Out → SemObs`, and
`BehaviorCodec L₁ L₂` links two languages over the same `SemObs` via four laws:

- `decodeQuery_encodeQuery : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁`
- `decodeOut_encodeOut : ∀ o₁, decodeOut (encodeOut o₁) = some o₁`
- `encodeOut_of_decodeOut : ∀ o₂ o₁, decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`
- `obs_decodeOut : ∀ o₂ o₁, decodeOut o₂ = some o₁ → L₂.obs o₂ = L₁.obs o₁`

Theinduced monotone behavior morphism `codec.toMorphism : L₁.Behavior →
L₂.Behavior` maps a behavior `b₁ : L₁.Query → Partial (L₁.Out → Prop)` to:

```lean
fun q₂ =>
  let p₁ := b₁ (codec.decodeQuery q₂)
  { defined := p₁.defined
    val := fun h o₂ =>
      ∃ o₁, codec.decodeOut o₂ = some o₁ ∧ p₁.val h o₁ }
```

Two immediate cardinal constraints follow from these laws:

1. **Query Retraction ($|L_1.\text{Query}| \le |L_2.\text{Query}|$):** Because
   `decodeQuery` is a left inverse to `encodeQuery`, `encodeQuery` is injective.
   In upward abstraction `Abstracts L_v L_mir codec v s`
   (`L_mir.sem s ≤ codec.toMorphism (L_v.sem v)`), `L_v.Query` must be a
   coarser or projected query space (such as mathematical input values `PureIn`
   paired with a layout witness) that `encodeQuery` embeds into a canonical
   initial `MirState`. When a verifier instead augments `MirState` with ghost
   state (e.g., fractional permissions `Addr → Rat` in `UC-2.3` or Tree Borrows
   shadow trees in `UC-3.1`), `MirState × GhostState` is strictly larger than
   `MirState` and cannot serve as `L_v.Query` with `decodeQuery : MirState →
   MirState × GhostState`. Instead, `theory/` has three sound options:
   - keep `L_v.Query := MirState` and initialize the ghost state
     deterministically inside `L_v.sem` via `initGhost : MirState → GhostState`
     (or quantify over valid initial ghost states inside `L_v.sem`);
   - formulate the ghost instrumentation horizontally as
     `Compiles L_mir L_ghost codec s v`, where
     `encodeQuery : MirState → MirState × GhostState` injects initial ghost
     state and `decodeQuery := Prod.fst` satisfies
     `decodeQuery (encodeQuery s) = s`; or
   - discharge `L_mir.sem s ≤ L_mir.SpecOn pre post` directly inside `theory/`
     via a relational simulation invariant
     $\mathcal{R} : \text{MirState} \to \text{GhostState} \to \text{Prop}$
     (as in Iris adequacy, `UC-2.1`).

2. **Outcome Partial Bijection (`encodeOut_of_decodeOut`):** The law
   `decodeOut o₂ = some o₁ → encodeOut o₁ = o₂` forces `decodeOut` to be
   injective on its `some` domain, preventing a rogue codec from collapsing
   distinct concrete outcomes onto a single abstract value. Consequently, if two
   concrete outcomes $o_2 \neq o_2'$ in `L_mir.Out` differ only in uninitialized
   struct padding bytes (`UC-3.4`, `UC-5.3`) or erased ghost state, `decodeOut`
   cannot map both to `some o₁`. Either `L_mir.Out` must project out
   non-observable heap padding before constructing `EventualOut Obs ReturnVal`,
   or `L_v.Out` must retain the representation choice and quotient it in
   `L_v.obs : L_v.Out → SemObs`.

Basis: **source** — `Trusted/Refinement.lean:234-385` in
`joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` and
`anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026`;
**derived** — cardinal constraints on ghost state and padding bytes.

#### 1.2 Predicate-transformer isomorphism and `ProductiveOn` as the Law of the Excluded Miracle

Every `b : Behavior Query Out` (`Query → Partial (Out → Prop)`) corresponds
bijectively to a monotonic predicate transformer
$\text{toWP}(b) : (\text{Out} \to \text{Prop}) \to (\text{Query} \to \text{Prop})$:

$$\text{toWP}(b)(Q)(q) :=\; \exists h : (b\,q).\text{defined},\; \forall o,\, (b\,q).\text{val}\,h\,o \to Q(o)$$

Under this isomorphism, `b ≤ L.SpecOn pre post` is equivalent to
$\forall q,\, \text{pre}(q) \to \text{toWP}(b)(\text{post}\,q)(q)$. However, if
$(b\,q).\text{defined} = \text{True}$ and $(b\,q).\text{val}\,h = \lambda \_.\,
\text{False}$ (an empty outcome set), then $\text{toWP}(b)(Q)(q)$ holds for
*every* postcondition $Q$, including $Q = \lambda \_.\,\text{False}$—a demonic
miracle in Dijkstra's sense. Pairing `SpecOn` or `Abstracts` with:

$$\text{L.ProductiveOn}\,\text{pre}\,p :=\; \forall q,\, \text{pre}(q) \to \exists h : (L.\text{sem}\,p\,q).\text{defined},\; \exists o,\, (L.\text{sem}\,p\,q).\text{val}\,h\,o$$

and `InhabitedPre pre := ∃ q, pre q` enforces $\neg \text{toWP}(L.\text{sem}\,p)
(\lambda \_.\,\text{False})(q)$ on a non-empty domain `pre`. Furthermore, when a
concrete program `s` satisfies both `Abstracts L_det L_mir codec v_det s`
against a deterministic singleton model `(L_det.sem v_det q).val h =
fun o => o = f q` and `L_mir.ProductiveOn pre s`, every concrete outcome set is
a non-empty subset of a singleton ($\emptyset \subsetneq S \subseteq
\{\text{encodeOut}(f(\text{decodeQuery}\,q))\}$), establishing exact
determinism without a dedicated determinism primitive in `trusted/`.

Basis: **source** — `Trusted/Refinement.lean:260-358`; **derived** — Dijkstra
predicate-transformer bijection and singleton determinism theorem.

---

### 2. Category A: Functional translators and symbolic evaluators (`UC-1.1`–`UC-1.4`)

#### 2.1 `UC-1.1`: Lens and prophecy functional translators (`Aeneas`, `Charon`, `RustHorn`, `RustHornBelt`, `Creusot`/`Coma`, `coq-of-rust`, `Electrolysis`, `hacspec`/`hax`)

##### Goals, problem domain, and target users

Functional translators eliminate mutable memory and pointer aliasing from safe
(and borrow-disciplined) Rust programs by translating them into pure functional
specifications in interactive theorem provers (Lean 4, Rocq/Coq, F\*, HOL4) or
SMT-backed deductive verifiers (Why3/Coma, CHC solvers). Their target users are
verification engineers proving rich algorithmic invariants—such as B-tree
balancing, cryptographic protocols (TLS, MLS, post-quantum Kyber/ML-KEM), and
zero-copy parsers—who want to reason by induction over algebraic datatypes
rather than spatial heap separation (`*`).

##### Development history, lineage, and evolution

- **`Electrolysis` (`Kha/electrolysis`, Sebastian Ullrich, MSc Thesis 2016):**
  Pioneered translating safe Rust MIR into Lean 2 by interpreting nested mutable
  borrows (`&mut (*x).field`) as compositional functional **lenses** (`get : S →
  A`, `set : S → A → S`) whenever borrow lifetimes follow a strict stack
  discipline.
- **`RustHorn` (Matsushita, Tsukada, Kobayashi, ESOP 2020 / TOPLAS 2021, DOI
  `10.1145/3462205`) and `RustHornBelt` (Matsushita, Denis, Jourdan, Dreyer,
  PLDI 2022, DOI `10.1145/3519939.3523704`):** Replaced lenses with **prophecy
  variables**: a mutable borrow `&'a mut T` is represented as a pair
  $(v_{\text{cur}}, v_{\text{final}}) : T \times T$, where $v_{\text{final}}$
  prophesies the value stored in the referent when lifetime `'a` ends.
  `RustHorn` compiles safe Rust directly into Constrained Horn Clauses (CHCs);
  `RustHornBelt` proved this prophetic translation sound inside Iris (`lambda-rust`)
  and extended it with parametric separation-logic specifications (`RustBelt`)
  at `unsafe` abstraction boundaries.
- **`Creusot` and `Coma` (`creusot-rs/creusot@c4e9770ac1371ac4274bfe02145266d315c2fb86`,
  Denis, Jourdan, Marché ICFEM 2022; Patault, Pereira, Why3/Coma ESOP 2025):**
  Builds on `RustHornBelt`'s prophetic mutable-borrow semantics (`^x` for final
  prophetic value, `*x` for current value) in its first-order specification
  language **Pearlite**, compiling Rust MIR to the **Coma** continuation-passing
  intermediate verification language and discharging VCs through Why3 to Z3,
  cvc5, and Alt-Ergo.
- **`Charon` (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`,
  v0.1.210) and `Aeneas` (`AeneasVerif/aeneas@70683bd4ab876179a23e5f994d02947b3e5c4f0d`,
  Ho & Protzenko ICFP 2022 DOI `10.1145/3547647`; Ho, Ayoun, Protzenko ICFP 2024
  DOI `10.1145/3674640`):** `Charon` hooks into `rustc` to extract unstructured
  (`ULLBC`) and structured (`LLBC`) Low-Level Borrow Calculus ASTs. `Aeneas`
  symbolically executes `LLBC` using a borrow-aware symbolic loan environment,
  translating functions that take/return mutable borrows into pure functions
  returning **backward functions** (which compute updated borrowed inputs when
  outer region lifetimes end) in Lean 4, F\*, Rocq, and HOL4.
- **`hacspec` and `hax` (`cryspen/hax@1ec88cdb2c8e546845e64eb2cd2321b4f58069c4`,
  Bhargavan et al. / Cryspen):** Evolved from the executable cryptographic
  specification subset `hacspec` into the general `rustc` frontend `hax`, which
  extracts THIR into pure functional ASTs for F\*, Rocq, ProVerif, and Lean 4
  (where `hax`'s Lean 4 backend `Hax/Tactic/HaxMvcgen.lean` now interoperates
  with Lean's `Std.Do` / `mvcgen` infrastructure and Aeneas).
- **`coq-of-rust` / `rocq-of-rust`
  (`formal-land/rocq-of-rust@ca1374ae2fdeb28b069fe77ba412db5604525261`):**
  Translates `rustc` THIR into a shallow monadic embedding in Rocq (`M` monad
  with `M.alloc`, `M.read`, `M.write`, and trait-hierarchy typeclasses), used
  to verify `revm` and `core`/`alloc` slices via manual user-written simulation
  relations linking the `M` monad to purely functional Rocq models.

##### Design philosophy, architectural tradeoffs, and ecosystem comparisons

| Tool | Extraction Hook | Mutable-Borrow Elimination Mechanism | Loop Handling | `unsafe` Code Strategy | TCB / Soundness Basis |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`Electrolysis`** | `rustc` MIR | Stack-disciplined lenses (`get`/`set`) | Structural recursion | Axiom stubs | Untrusted Rust-to-Lean translator |
| **`RustHorn` / `Creusot`** | `rustc` MIR | First-order prophecy variables (`*x`, `^x`) | Loop invariants in Pearlite / Coma handlers | Trusted `#[trusted]` axioms justified on paper by `RustHornBelt` | Trusts `rustc`, `Creusot` MIR-to-Coma translator, Why3, and SMT solvers |
| **`Aeneas` + `Charon`** | `rustc` MIR $\to$ LLBC | Symbolic borrow graphs $\to$ pure backward functions | Fixed-point `loop` combinator + `Std/WP.lean` (`loop.spec_decr_nat`) | Assumed external models (`Std/Primitives.lean`); ongoing spatial PR1352 | Paper soundness theorem (`ICFP 2022`/`2024`); `Charon` + `Aeneas` OCamls in TCB |
| **`hax`** | `rustc` THIR | Pure functional value updates (in-place mutation without returned `&mut`) | Functional fold/recursion | Assumed backend primitives | Trusts `hax` THIR extractor and printer |
| **`rocq-of-rust`** | `rustc` THIR | None at extraction (kept in state/address monad `M`, proved away interactively) | Fuel-indexed monadic recursion | Monadic memory simulation | Trusts `rocq-of-rust` THIR translator |

**Prophecies (`RustHorn`/`Creusot`) vs. Backward Functions (`Aeneas`):**
Prophecies collapse forward execution and future borrow updates into a single
first-order relation by guessing $v_{\text{final}}$ upfront and asserting
$v_{\text{actual}} = v_{\text{final}}$ when the borrow expires. This suits
automated first-order SMT/CHC solvers (`Z3`, `Spacer`) because it avoids
higher-order continuations, but in an interactive proof assistant (Lean 4, Rocq)
it forces users to thread existential prophecy witnesses through definitions.
Conversely, `Aeneas`'s backward functions (`f_fwd` / `f_back` or combined tuple
returns in `Std/Primitives.lean` with `Result α`) produce executable,
deterministic functional definitions in Lean 4 (`@[step]` / `StepStar` in
`Tactic/Step/`), at the cost of requiring region-hierarchy splitting when a
function returns a mutable borrow aliased to multiple input regions.

##### Formal theory, specification methodology, proof automation, and TCB

In `Aeneas@70683bd4ab876179a23e5f994d02947b3e5c4f0d`, translated Lean 4 functions
live in the error monad `Result α` (`ok : α → Result α`, `fail : Error →
Result α`, `div : Result α` in `backends/lean/Aeneas/Std/Primitives.lean`).
Verification uses a syntax-directed weakest-precondition calculus (`Std/WP.lean`
and `Tactic/Step/`) coupled with domain-specific arithmetic automation
(`scalar_tac` in `Tactic/Solver/ScalarTac.lean` and `bv_tac` in
`Tactic/Solver/BvTac.lean`). However, in standalone `Aeneas`, `Creusot`, and
`hax`, the OCaml/Rust translation pipeline from `rustc` MIR/THIR to the target
prover AST is **unverified and inside the TCB**: a bug in `Charon`'s borrow
reconstruction or `Creusot`'s prophecy resolution silently produces a Lean/Coma
model that diverges from actual `rustc` MIR semantics.

##### Exact mapping onto Anneal's four `trusted/` primitives

In Anneal, the functional translator is **removed from the TCB** by formulating
each translated pure Lean function `f_pure` in `theory/` as an upward
abstraction of the captured `Runtime(PostCleanup)` MIR body `f_mir`:

1. **`Abstracts L_pure L_mir codec f_pure f_mir` (`Language SemObs` +
   `BehaviorCodec`):**
   - `L_pure.Query := PureIn × LayoutWitness` (algebraic input values plus
     disjoint heap layout coordinates).
   - `L_pure.Out := EventualOut Obs PureOut` and
     `L_pure.SemObs := EventualOut Obs Unit` (identical to `L_mir.SemObs`).
   - `codec.encodeQuery` materializes `PureIn` into disjoint allocations in
     `MirState`; `codec.decodeQuery` reads them back (`decodeQuery (encodeQuery q) = q`).
   - `codec.decodeOut : L_mir.Out → Option L_pure.Out` checks that the final
     `MirState` satisfies the backward-function or prophecy equations and that
     all non-borrowed memory frames are preserved, returning `none` on any frame
     violation. Because `Abstracts` requires every concrete outcome of `f_mir`
     to lie in the `some` domain of `decodeOut`, proving `Abstracts`
     automatically certifies memory framing.
2. **`L_pure.ProductiveOn pre_pure f_pure` and `InhabitedPre pre_pure`:**
   - In a `RustHorn`/`Creusot`-style prophetic translation, an over-constrained
     or buggy prophecy resolution equation $v_{\text{actual}} = v_{\text{final}}$
     would make the outcome predicate `(L_pure.sem f_pure q).val h` empty
     (`fun _ => False`), vacuously satisfying every postcondition.
     `L_pure.ProductiveOn pre_pure f_pure` forces `theory/` to exhibit a valid
     execution outcome `o` for every `q` satisfying `pre_pure`, mathematically
     ruling out prophetic miracles.

Basis: **source** — `AeneasVerif/aeneas@70683bd4ab876179a23e5f994d02947b3e5c4f0d`,
`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`,
`creusot-rs/creusot@c4e9770ac1371ac4274bfe02145266d315c2fb86`,
`cryspen/hax@1ec88cdb2c8e546845e64eb2cd2321b4f58069c4`,
`formal-land/rocq-of-rust@ca1374ae2fdeb28b069fe77ba412db5604525261`, and
`rust-verification-aeneas-lithium-tracked-funclang-and-loops-2026`;
**derived** — `Abstracts` + `ProductiveOn` bridge in `theory/`.

---

#### 2.2 `UC-1.2`: Loop-fuel and cut-point invariant functional extractors (`AutoCorres`/`AutoCorres2`, `Aeneas` `CCPO`/`loop`)

##### Goals, problem domain, and target users

Low-level systems languages (`Runtime(PostCleanup)` MIR, C SIMPL) represent
arbitrary control flow (`while`, `for`, `loop`, `break`, `continue`, `?` early
returns, and unwinding cleanup ladders) as cyclic basic-block control-flow
graphs (CFGs). Interactive theorem provers (Lean 4, Isabelle/HOL, Rocq) require
pure definitions to be total—either by well-founded recursion, fuel indexing,
or complete partial order (`CCPO`) least fixed points.

##### Development history, lineage, and evolution

- **`AutoCorres` (Greenaway, Lim, Andronick, Klein, PLDI 2014, DOI
  `10.1145/2594291.2594296`) and `AutoCorres2` (Isabelle/HOL Archive of Formal
  Proofs):** Built on Norrish's C-to-Isabelle parser (`SIMPL`) for the seL4
  microkernel proof. `AutoCorres` translates deeply embedded C `SIMPL`
  statements into shallowly embedded monadic Isabelle/HOL functions through a
  staged pipeline (`L1` control-flow exception elimination $\to$ `L2` local
  variable lifting to SSA-like monadic bindings $\to$ `HL` heap abstraction
  splitting typed pointers $\to$ `WA` word abstraction from `word32` to `nat`/`int`
  with overflow guards $\to$ `TS` type strengthening into `option`/pure
  functions), generating an end-to-end Isabelle/HOL refinement proof for every
  translated function.
- **`Aeneas` `CCPO` Fixed-Point Loop Combinator
  (`AeneasVerif/aeneas@70683bd4ab876179a23e5f994d02947b3e5c4f0d`,
  `backends/lean/Aeneas/Std/Primitives.lean` and `Std/WP.lean`):** Uses
  Bourdoncle's weak topological ordering (WTO) in OCaml (`charon` / `aeneas`) to
  reconstruct structured loops from MIR CFGs, emitting recursive body
  definitions tied by a partial-order fixed point `loop` in `Result α` and
  providing both partial-correctness and total-correctness (`loop.spec_decr_nat`)
  WP rules.

##### Design philosophy, architectural tradeoffs, and formal theory

`AutoCorres` is **certifying** (proof-producing): its ML tactic constructs an
Isabelle kernel proof that the shallow monadic function refines the deeply
embedded `SIMPL` AST. By contrast, `Aeneas`'s WTO loop reconstruction happens
outside Lean in OCaml. When reconstructing loops from arbitrary MIR CFGs in
Anneal's `theory/`, a cut-point invariant or fuel-unrolling combinator must
handle diverging executions soundly.

##### Exact mapping onto Anneal's four `trusted/` primitives

In `Abstracts L_loop L_mir codec f_loop f_mir`
(`L_mir.sem f_mir ≤ codec.toMorphism (L_loop.sem f_loop)`):

- **Total correctness via well-founded measure $\mu : \text{CutState} \to
  \mathbb{N}$:** `f_loop` is defined by well-founded recursion on $\mu(q)$, and
  `(L_loop.sem f_loop q).val h .diverges` is `False`. By `Abstracts`,
  `L_mir.sem f_mir ≤ codec.toMorphism (L_loop.sem f_loop)` immediately proves
  `¬ (L_mir.sem f_mir q).val h .diverges` (termination of the concrete MIR
  CFG).
- **Partial correctness / fuel unrolling (`Fuel : Nat`):** If a fuel-indexed
  abstract evaluator `L_loop` mapped fuel exhaustion ($k = 0$) to `.stuck` or
  `.failed` (`defined := False`), then `Abstracts` would require `L_loop` to be
  `defined` whenever `L_mir` is `defined`—which is **false** if the concrete
  loop executes $k + 1$ iterations! Therefore, in upward `Abstracts`, unverified
  or fuel-exhausted cut-off paths in `L_loop` must map to **demonic universal
  choice** (`defined := True`, `val := fun _ => True` or `.diverges`), whereas
  bounded model checking restricts `Query` to inputs that terminate within $k$
  iterations.

Basis: **source** — `autocorres-guarded-model-certificates-pldi-2014`,
`AeneasVerif/aeneas@70683bd4ab876179a23e5f994d02947b3e5c4f0d`, and
`Trusted/Refinement.lean:380-385`; **derived** — opposite polarity of fuel
exhaustion in `Abstracts` vs. `Compiles`.

---

#### 2.3 `UC-1.3`: Higher-order closures, `dyn Trait`, and interaction trees (`Interaction Trees`/`Vellvm`, `FreeSpec`/`DimSum`)

##### Goals, problem domain, and target users

Systems and library code in Rust and LLVM invokes unknown callbacks (`FnMut`,
`&mut dyn Write`), FFI routines, and cross-language modules, interleaving
internal state transitions with observable external events and nondeterminism.

##### Development history, lineage, and evolution

- **`Interaction Trees` (`DeepSpec/InteractionTrees@a2bc2c38ad998dccadb932559c922139dd957c4f`,
  Xia et al., POPL 2020, DOI `10.1145/3371119`) and `Vellvm`
  (`vellvm/vellvm@506f1eb0be542611521985719b971fbce8498dc9`, Zakowski et al.,
  ICFP 2021):** `ITree E R` is a coinductive free monad with three constructors:
  `Ret (r : R)`, `Tau (t : ITree E R)` (silent internal step), and
  `Vis {A : Type} (e : E A) (k : A → ITree E R)` (visible external event with
  answer continuation $k$). `Vellvm` layers an algebraic handler stack (`L0`
  syntactic VIR $\to$ `L1` global environment $\to$ `L2` local stack $\to$ `L3`
  byte/poison memory `DTYPE_B` $\to$ `L4` angelic/demonic nondeterminism `PropT`)
  and reasons via weak bisimulation (`eutt`, equivalence up to tau).
- **`FreeSpec` and `DimSum` (Sammler et al., POPL 2023, DOI `10.1145/3571220`):**
  `DimSum` models open multi-language modules (Rec, Asm, C) as transition
  systems over explicit incoming and outgoing call/return events, enabling
  horizontal and vertical linking of mutually recursive callbacks across
  language boundaries.

##### Design philosophy, architectural tradeoffs, and ecosystem comparisons

Coinductive `ITree` weak bisimulation (`eutt`) in Rocq requires extensive PACO
(parameterized coinduction) machinery, struggles when composing with relational
set-of-traces (`PropT`) nondeterminism (`eutt` is not a congruence under
unbounded demonic choice without carefully stratified monad transformers), and
cannot be natively defined as a primitive `coinductive` type in Lean 4's kernel
without quotient polynomial functors (`alexkeizer/QpfTypes@5b5dd4f83121662838b99d129b92f632f263c508`).

##### Exact mapping onto Anneal's four `trusted/` primitives

Anneal achieves the full compositional power of `ITrees` and `DimSum` inside
`trusted/lean/` **without coinduction or `Classical.choice`**:

1. **Tau-Insensitive Step Elasticity via `EventualBehaviorOf`:**
   `EventualBehaviorOf` defines `Out := EventualOut Obs Val` with inductive
   reachability `.terminated (trace : List Obs) (term : Terminal Val)` and
   universal non-termination `.diverges`. Silent internal transitions (`Tau` /
   `.choice .demonic`) do not append to `trace : List Obs` and are existentially
   quantified over step count $n : \mathbb{N}$ in `.terminated`, giving `eutt`'s
   finite-tau erasure (`1 → 0`, `1 → k`, `k → 1`) by ordinary inductive
   reachability.
2. **External Call Effects via `StepResult.externalCall` and Shared `SemObs`:**
   When `SmallStepMachine` executes an unresolved indirect call (`dyn Trait`
   vtable or external symbol), it steps via
   `StepResult.externalCall boundaryInv branches` and emits `Obs.extCall`. Both
   an abstract interaction-tree model `L_itree` in `theory/` and `L_mir` share
   `SemObs := EventualOut Obs Unit`, so `codec.obs_decodeOut` holds by `rfl` on
   `trace : List Obs`.

Basis: **source** — `DeepSpec/InteractionTrees@a2bc2c38ad998dccadb932559c922139dd957c4f`,
`vellvm/vellvm@506f1eb0be542611521985719b971fbce8498dc9`, DimSum POPL 2023 DOI
`10.1145/3571220`, and `Trusted/StepResult.lean`; **derived** — coinduction-free
`EventualBehaviorOf` + `StepResult.externalCall` correspondence.

---

#### 2.4 `UC-1.4`: Bit-precise symbolic evaluators (`Lean 4 bv_decide`, `SAW`/`Crucible`/`crux-mir`, `Kani`, `Rosette`/`Serval`, `HolBA`/`Islaris`/`Sail`)

##### Goals, problem domain, and target users

Cryptographic primitives (AES, SHA-256, ChaCha20, Curve25519), binary wire
parsers, `zerocopy` byte transmutations, SIMD routines, and OS kernel/firmware
handlers require bit-exact reasoning over fixed-width two's-complement integers
(`UInt8`..`UInt128`), bitshifts, endianness, and byte arrays without interactive
arithmetic proofs.

##### Development history, lineage, and evolution

- **`SAW`, `Crucible`, and `crux-mir`
  (`GaloisInc/saw-script@27a7ae98256544b55a7a3ce4ce620c1a7889713b`,
  `GaloisInc/crucible@7f49dac06c656f7b92c8b6cc054f47c63b60abe4`):** Galois's
  Software Analysis Workbench (`SAW`) symbolically executes LLVM, JVM, and Rust
  MIR (`crux-mir`) through the `Crucible` SSA symbolic simulator, merging paths
  into shared And-Inverter Graphs (AIGs) / `What4` terms and discharging
  equivalence against Cryptol specifications via ABC, Yices, or Z3 (used to
  verify `AWS-LC` / `s2n-bignum`).
- **`Kani` (`model-checking/kani@9461e07af7ec929f050aa4192f29363c9be07779`):**
  Compiles Rust MIR into CBMC `GOTO` programs (`codegen_cprover_gotoc`) with
  shadow-memory object tables tracking pointer allocation validity and byte
  initialization, unrolling loops to a bound $k$ (or using `#[kani::loop_invariant]`)
  and bit-blasting to Kissat/CaDiCaL.
- **`Rosette` (`emina/rosette@373c8c35e4a7667f38fce10cf0b74ae17de07f1d`, Torlak
  & Bodik, PLDI 2014, DOI `10.1145/2594291.2594340`) and `Serval`
  (`uw-unsat/serval@72adc4952a1e62330aea527214a26bd0c09cbd05`, Nelson et al.,
  SOSP 2019, DOI `10.1145/3341301.3359641`):** `Rosette` lifts a host language
  interpreter into a symbolic evaluator by merging symbolic states at control
  joins (`ite` value merging) rather than forking paths. `Serval` applies
  `Rosette` to verify RISC-V (`CertiKOS`/`Komodo`) and x86-32 (`cks`) monitors by
  requiring finite state-machine structures without unbounded loops.
- **`Sail` (`rems-project/sail@0f51056900af85d0b18928d6ea2d2271d18184e8`),
  `Islaris` (`rems-project/islaris@c978e10f50db5c40f0fdf113f5f76a779782c6f9`,
  Sammler et al., PLDI 2022, DOI `10.1145/3519939.3523434`), and `HolBA`
  (`kth-step/HolBA@ef22c1fd8da612c57f2e7f273cb14594a7e529d3`):** `Islaris` uses
  the `Isla` symbolic evaluator over authoritative `Sail` Armv8-A/Morello/RISC-V
  specifications to emit simplified per-instruction symbolic traces that are
  verified foundationally inside Rocq/Iris (`Lithium`). `HolBA` lifts Armv8/RISC-V
  machine code to the `BIR` intermediate representation in HOL4 with
  proof-producing bitvector steps.
- **`Lean 4 bv_decide` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`,
  v4.34.1, `src/Lean/Elab/Tactic/BVDecide/`, Böving et al., CAV 2025):**
  Normalizes Lean `BitVec w` goals by rewrite lemmas, bit-blasts to a verified
  AIG (`Std.Sat.AIG`), invokes an external CDCL SAT solver (`CaDiCaL`) to
  produce an `LRAT` unsatisfiability certificate, and checks the `LRAT`
  certificate inside Lean's kernel via computational reflection (`decide` /
  `ofReduceBool`).

##### Design philosophy, architectural tradeoffs, and TCB comparisons

`SAW`/`crux-mir`, `Kani`, and `Serval` achieve push-button automation on
fixed-bound bitvector code, but their symbolic execution engines (`Crucible`,
`CBMC`, `Rosette`) and external solvers (`Z3`, `Yices`, `CaDiCaL`) sit entirely
inside their TCB. Conversely, `Islaris` and `Lean 4 bv_decide` decouple search
from checking: `Islaris` re-checks `Isla`'s symbolic traces in Rocq/Iris, and
`bv_decide` checks `CaDiCaL`'s `LRAT` proof inside the Lean 4 kernel (note that
in Anneal, `TrustedBoundary.lean` forbids `native_decide`, so `bv_decide` must
use kernel Whnf reduction `decide` as characterized in
`lean4-core-tactics-kernel-bvdecide-stddo-and-containers-2026`).

##### Exact mapping onto Anneal's four `trusted/` primitives

A verified symbolic evaluator `symEval : Fuel → SymState → SymResult` in
`theory/` steps `L_mir` symbolically and emits each path's UB checks (shift
width $< w$, division by non-zero, aligned pointer access, in-bounds slice
indexing) and postcondition clauses as fine-grained `Obligation` entries in
`VerificationResult`:

- Each `Obligation` has `prop : Prop` expressed as a closed `BitVec` formula
  discharged by kernel-checked `LRAT` (`bv_decide` without `native_decide`).
- A once-and-for-all theorem `symEval_sound` in `theory/` proves that
  `AllHold (obligations.map (·.prop))` implies
  `L_mir.sem f ≤ L_mir.SpecOn pre post ∧ L_mir.ProductiveOn pre f`.

Basis: **source** — `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`,
`GaloisInc/crucible@7f49dac06c656f7b92c8b6cc054f47c63b60abe4`,
`model-checking/kani@9461e07af7ec929f050aa4192f29363c9be07779`,
`emina/rosette@373c8c35e4a7667f38fce10cf0b74ae17de07f1d`,
`uw-unsat/serval@72adc4952a1e62330aea527214a26bd0c09cbd05`,
`rems-project/islaris@c978e10f50db5c40f0fdf113f5f76a779782c6f9`, and
`lean4-core-tactics-kernel-bvdecide-stddo-and-containers-2026`;
**derived** — `VerificationResult` decomposition of symbolic path obligations.

---

### 3. Category B: Separation logics and spatial resource engines (`UC-2.1`–`UC-2.4`)

#### 3.1 `UC-2.1`: Higher-order concurrent separation logics (`Iris`/`MoSeL`, `iris-lean`, `RustBelt`, `RefinedC`/`Caesium`, `RefinedRust`, `VST`)

##### Goals, problem domain, and target users

Unsafe Rust standard-library abstractions (`Arc<T>`, `Mutex<T>`, `RwLock<T>`,
`Cell<T>`, `RefCell<T>`, `OnceLock<T>`, futures, intrusive linked lists) and C
systems components violate tree-shaped borrow discipline intentionally: they
use raw pointers, `UnsafeCell` interior mutability, atomic CAS loops, and custom
ownership-sharing protocols. Higher-order separation logics provide a
foundational proof theory inside an interactive theorem prover (Rocq or Lean 4)
to verify that these unsafe primitives satisfy safe public API contracts.

##### Development history, lineage, and evolution

- **`VST` (`PrincetonUniversity/VST@3c37c2e2b574e23aee8fdd1684aa0ffed227491e`,
  Appel et al., 2014):** Verified Software Toolchain for CompCert `Clight` in
  Rocq, constructing step-indexed separation algebras (`msl/`) and tactic
  automation (`forward`, `entailer!`) directly over CompCert's operational
  semantics so proofs compose end-to-end with CompCert's verified assembly
  backend.
- **`Iris` and `MoSeL` (`rocq-iris/iris@8e4909593a3a84f850d224a344cbd3a380672088`,
  Jung et al., JFP 2018, DOI `10.1017/S0956796818000151`; Krebbers et al., ICFP
  2018, DOI `10.1145/3236772`) and `iris-lean`
  (`leanprover-community/iris-lean@81bc35088ba67d465db008f5261a9b341eb6cf6c`):**
  Unifies step-indexed higher-order ghost state into a single algebraic
  primitive—partial Commutative Monoids with Frame-Preserving Updates (**CMRAs /
  Cameras**)—combined with impredicative invariants ($\boxed{P}^{\mathcal{N}}$)
  and the tactical proof mode (`MoSeL` / `IPM`, ported to Lean 4 in `iris-lean`
  via `BI` interface classes and custom spatial context metaprogramming).
- **`RustBelt` (`iris/lambda-rust@186900b2cf948835873281646ce20c7e8f084f17`,
  Jung et al., POPL 2018, DOI `10.1145/3158154`; Dang et al., POPL 2020, DOI
  `10.1145/3371102`):** Built the **Lifetime Logic** on top of Iris to give a
  semantic model of Rust's type system over $\lambda_{\text{Rust}}$, defining
  mutable and shared borrows via temporal lifetime tokens (`[κ]_q`) and semantic
  type interpretations $\llbracket \tau \rrbracket(\text{tid}, \vec{v})$ to
  prove soundness of `Send`, `Sync`, `Arc`, `Mutex`, `RefCell`, and `Cell`.
- **`RefinedC` and `Caesium`
  (`iris/refinedc@d057583986651a28047164581f05fbee3a83ed9d`, Sammler et al.,
  PLDI 2021, DOI `10.1145/3453483.3454036`) and `RefinedRust`
  (`lgaeher/refinedrust-dev@8a07f4f2e6a499625b4b25e94f0b2ab78592cb52`, Gäher et
  al., PLDI 2024, DOI `10.1145/3656423`):** Automate foundational Iris proofs by
  introducing **refinement ownership types** (`r @ ty`) checked by the
  goal-directed **Lithium** separation-logic interpreter (`theories/lithium/`).
  In `RefinedC`, Lithium checks C code over the `Caesium` operational C
  semantics; in `RefinedRust`, the `radium` rustc frontend extracts MIR into
  Rocq, and Lithium automates both safe borrow checking (subsuming prophetic
  functional updates) and unsafe raw-pointer reasoning in a single Iris type
  system.

##### Design philosophy, architectural tradeoffs, and formal theory

Foundational separation logics (`Iris`, `VST`, `RefinedC`, `RefinedRust`) have a
**minimal TCB**: the separation logic itself (`iProp Σ`, cameras, lifetime
tokens, Lithium's goal-directed proof search) is 100% untrusted by the kernel
because an **Adequacy Theorem** erases the logic down to a statement about the
underlying operational semantics (`Caesium`, $\lambda_{\text{Rust}}$, or
`CompCert Clight`). The primary tradeoff is interactive proof latency when
Lithium's syntax-directed subsumption rules hit non-deterministic spatial
quantifier instantiations.

##### Exact mapping onto Anneal's four `trusted/` primitives

Anneal's `trusted/lean/` boundary is designed so that **`iris-lean` and all
spatial/camera machinery live 100% in `theory/`**:

1. **Step-Indexed Adequacy via `EventualBehaviorOf`:**
   In Iris, the weakest precondition `wp ⊤ f_mir Φ` proves by induction on step
   index $n : \mathbb{N}$ that every $n$-step execution prefix of
   `SmallStepMachine` is safe (never reaches `.failed .ub` or `.stuck`) and
   satisfies $\Phi$ upon `.terminated`. Because `EventualBehaviorOf` defines
   `(L_mir.sem f_mir q).defined` as universal safety over all finite reachable
   prefixes (`∀ n tr out, ReachesPrefix ... → out.isSafe`) while mapping
   infinite execution to `.diverges : EventualOut Obs Val` (which is a
   *defined* outcome inside `val`), the Iris Adequacy Theorem (`iris_adequacy`)
   in `theory/` directly discharges:
   $$(\vdash \text{wp}\;\top\;f_{\text{mir}}\;\Phi) \implies L_{\text{mir}}.\text{sem}\,f_{\text{mir}} \le L_{\text{mir}}.\text{SpecOn}\,\text{pre}\,\Phi \;\wedge\; L_{\text{mir}}.\text{ProductiveOn}\,\text{pre}\,f_{\text{mir}}$$
   (given `TotalStep` / `InhabitedDemonic` for `L_mir`).
2. **No Separation Logic in `trusted/lean/`:** Neither `CMRA`, `iProp`, nor
   step-indices appear in `Trusted/Refinement.lean` or `Trusted/StepResult.lean`.

Basis: **source** — `rocq-iris/iris@8e4909593a3a84f850d224a344cbd3a380672088`,
`leanprover-community/iris-lean@81bc35088ba67d465db008f5261a9b341eb6cf6c`,
`iris/lambda-rust@186900b2cf948835873281646ce20c7e8f084f17`,
`iris/refinedc@d057583986651a28047164581f05fbee3a83ed9d`,
`lgaeher/refinedrust-dev@8a07f4f2e6a499625b4b25e94f0b2ab78592cb52`,
`PrincetonUniversity/VST@3c37c2e2b574e23aee8fdd1684aa0ffed227491e`, and
`lean4-separation-logics-iris-lean-iprop-and-choicekind-adequacy-2026`;
**derived** — adequacy bridge to `EventualBehaviorOf`.

---

#### 3.2 `UC-2.2`: Automated symbolic-heap frame-inference engines (`CN`/`Fulminate`, `VeriFast`, `Viper`/`Prusti`, `Gillian`/`Gillian-Rust`, `Smallfoot`/`Infer`/`Pulse`)

##### Goals, problem domain, and target users

Systems programmers writing OS kernels (`pKVM`), allocators, and C/Rust data
structures often want fast, predictable separation-logic verification without
interactive Rocq/Lean proof scripts. Automated symbolic-heap engines restrict
assertions to the **Symbolic Heap (`SymHeap`)** fragment—a pair $(\Pi \mid
\Sigma)$ of a pure first-order constraint $\Pi$ and a spatial conjunction
$\Sigma = p_1 \mapsto v_1 * \dots * p_k \mapsto v_k * P_1(\vec{x}_1) * \dots$—where
frame inference (subtracting a callee's precondition footprint from the caller's
heap) is decidable or syntax-directed.

##### Development history, lineage, and evolution

- **`Smallfoot` (Berdine, Calcagno, O'Hearn, FMCO 2005) and `Infer` / `Pulse`
  (`facebook/infer@5aac32c06952a2f3a6b7043e91457920f065833b`, Calcagno et al.
  JACM 2011; Le et al. 2022):** `Smallfoot` introduced decidable symbolic
  execution and frame inference over symbolic heaps with hard-coded linked-list
  and tree predicates. `Infer` added **bi-abduction** ($H * \text{?anti-frame}
  \vdash P * \text{?frame}$) to synthesize procedure summaries bottom-up without
  user annotations; `Pulse` reformulated bi-abduction as an incorrectness/under-approximate
  separation logic engine for C++, Java, and Rust MIR.
- **`VeriFast` (`verifast/verifast@0a83dba42db7ce0b445034ece5298afe980e57dc`,
  Jacobs et al., NFM 2011; Foundational VeriFast, Jacobs et al., 2026,
  `arXiv:2601.13727v1`):** Achieves sub-second symbolic execution of C, Java,
  and Rust by requiring explicit ghost statements (`open`, `close`, lemma
  function calls) whenever inductive predicates are folded/unfolded, avoiding
  backtracking search. In 2026, *Foundational VeriFast* added **hinted
  mirroring**, emitting execution hints from `VeriFast` that are replayed inside
  Rocq against an axiomatic semantics to produce a kernel-checked proof.
- **`Viper` (`viperproject/silver@da1c8993b66feb39976e3609e2580a4661137a0f`,
  Müller et al., VMCAI 2016) and `Prusti`
  (`prusti/prusti@0d4a8d497ac1e540d48ef50a031d53b4e3ae36e2`, Astrauskas et al.,
  OOPSLA 2019, DOI `10.1145/3360573`):** `Viper` is an intermediate verification
  language based on **Implicit Dynamic Frames (IDF)** (`acc(x.f, p)`), with two
  backends: `Silicon` (symbolic execution) and `Carbon` (verification-condition
  generation via Boogie/Z3). `Prusti` lowers safe Rust MIR borrow checking into
  Viper permissions using *magic wands* (`P --* Q`) to represent expiring
  mutable borrows (pledges).
- **`CN` and `Fulminate`
  (`rems-project/cerberus@c8c085d4714ae17095b2e1202fa33c5545d98df1`, Pulte et
  al., POPL 2023, DOI `10.1145/3571194`; Banerjee et al., POPL 2025, DOI
  `10.1145/3704879`):** `CN` builds a decidable refinement-type and separation-logic
  system over `Cerberus` `Core` IR for C (`pKVM` hypervisor buddy allocator),
  restricting resource predicates to syntax-directed guarded conditionals so SMT
  queries remain strictly quantifier-free. `Fulminate` compiles `CN` separation-logic
  specifications into executable C runtime-testing ownership shadow checks.
- **`Gillian` and `Gillian-Rust`
  (`GillianPlatform/gillian-rust@83d739e83034d71162fb66b569041cf301123df7`,
  Ayoun et al., PLDI 2025, DOI `10.1145/3729289`):** Parametric compositional
  symbolic execution platform in OCaml. `Gillian-Rust` uses a **hybrid memory
  model** combining fast tree-structured algebraic state for safe Rust places
  with a byte-level flat memory block fallback when pointers are cast to raw
  byte offsets, plus prophecy servers for mutable borrows.

##### Design philosophy, architectural tradeoffs, and TCB comparisons

Standalone `Viper`/`Prusti`, `CN`, and `Gillian-Rust` achieve high automation by
keeping the symbolic heap engine and Z3/cvc5 inside the TCB. *Foundational
VeriFast* (`arXiv:2601.13727v1`) and *Boogie/Viper Certificate Generation*
(Parthasarathy et al., CAV 2021, DOI `10.1007/978-3-030-81688-9_33`; OOPSLA 2024)
demonstrate that an automated symbolic-heap or IDF verifier can emit a compact
**fold/unfold and frame-matching witness certificate** (`SymHeapCert`) that a
simple kernel-verified checker replays without search.

##### Exact mapping onto Anneal's four `trusted/` primitives

In Anneal's `theory/`, a verified boolean certificate checker
`checkSymHeapCert : MirBody → SymHeapSpec → SymHeapCert → Bool` interprets a
`SymHeap` as a predicate `interpSH : SymHeap → MirState → Prop` over disjoint
sub-heaps (`Heaplet.Disjoint h_active h_frame`) and checks explicit predicate
`open`/`close` hints and frame-matching permutations at each MIR basic block:

1. **Soundness via `L_mir.SpecOn` and `ProductiveOn`:**
   `checkSymHeapCert_sound` proves that when `checkSymHeapCert body spec cert = true`
   and the pure side conditions (`VerificationResult` obligations) hold,
   `L_mir.sem body ≤ L_mir.SpecOn spec.pre spec.post ∧ L_mir.ProductiveOn spec.pre body`.
2. **Framing Across `StepResult.externalCall`:**
   When a function holds a spatial frame $R$ disjoint from the arguments passed
   to an external call (`StepResult.externalCall boundaryInv branches`), the
   external call's `branches : MirState → Prop` transition relation in `L_mir`
   must preserve all unescaped/unexposed heap allocations in $R$. This surfaces
   a concrete requirement on `L_mir`: `StepResult.externalCall` branches must
   constrain modifications to allocations reachable from exposed provenance or
   passed arguments.

Basis: **source** — `rems-project/cerberus@c8c085d4714ae17095b2e1202fa33c5545d98df1`,
`verifast/verifast@0a83dba42db7ce0b445034ece5298afe980e57dc`,
`viperproject/silver@da1c8993b66feb39976e3609e2580a4661137a0f`,
`prusti/prusti@0d4a8d497ac1e540d48ef50a031d53b4e3ae36e2`,
`GillianPlatform/gillian-rust@83d739e83034d71162fb66b569041cf301123df7`, and
`facebook/infer@5aac32c06952a2f3a6b7043e91457920f065833b`;
**derived** — certifying `SymHeapCert` checker and `externalCall` frame condition.

---

#### 3.3 `UC-2.3`: Fractional and counting permission verifiers (`VerCors`, `Steel`/`Pulse` in F\*, Boyland fractional permissions)

##### Goals, problem domain, and target users

Rust code routinely splits mutable slices into disjoint sub-slices
(`slice::split_at_mut`), shares immutable buffers across concurrent readers
(`Arc<[u8]>`, `RwLockReadGuard<T>`, zero-copy network views), and recombines
exclusive write access once all readers finish. Boyland's **fractional
permissions** $q \in (0, 1]_{\mathbb{Q}}$ (where $q = 1$ grants read/write access
and $0 < q < 1$ grants read-only shared access, with $p_1 \stackrel{q_1}{\mapsto} v *
p_1 \stackrel{q_2}{\mapsto} v \iff p_1 \stackrel{q_1 + q_2}{\mapsto} v$) and
Bornat's **counting permissions** model shared read/write recombines cleanly.

##### Development history, lineage, and evolution

- **`VerCors` (`utwente-fmt/vercors@3300d5b007286225a33c17a233bda77db9471213`,
  Blom & Huisman, FM 2014):** Verifies concurrent Java, C, OpenCL, and Halide
  programs by lowering fractional-permission annotations (`Perm(loc, q)`) and
  fork/join barriers into Viper.
- **`Steel` and `Pulse` in F\*
  (`FStarLang/FStar@e2b5042ffd8272ad6287e4ad8748d8e52dadd93d`, Fromherz et al.,
  ICFP 2021):** Embeds a concurrent separation logic DSL (`Pulse`) inside
  dependent type theory (F\*) where `pts_to r #p v` carries a fractional
  permission `#p : perm` manipulated by an automated AC-matching frame solver
  that discharges linear rational arithmetic (`p == p1 +. p2`) via Z3.

##### Exact mapping onto Anneal's four `trusted/` primitives

Modeling fractional permissions as an abstract machine `L_frac` over `L_mir`
directly tests the **`BehaviorCodec` query-retraction law**
(`decodeQuery (encodeQuery q₁) = q₁`):

- In `L_frac`, each state pairs `MirState` with a ghost permission map
  `perm : Addr → Rat` where loads require `perm a > 0`, stores require
  `perm a = 1`, and ghost split/merge steps conserve $\sum \text{perm}(a) \le 1$.
- Because `L_frac` fails *more often* than `L_mir` (a store with $0 < \text{perm}(a)
  < 1$ triggers `.failed .ub` in `L_frac` even when allocated in `L_mir`),
  `L_mir` refines `L_frac` (`Abstracts L_frac L_mir`).
- However, if `L_frac.Query` were `MirState × (Addr → Rat)` while `L_mir.Query =
  MirState`, no `encodeQuery : MirState × (Addr → Rat) → MirState` could have a
  left inverse `decodeQuery`! To satisfy `decodeQuery (encodeQuery q₁) = q₁`,
  `L_frac` sets `L_frac.Query := MirState` and initializes the initial
  permission map deterministically inside `L_frac.sem` from the function's entry
  footprint `initPerm : MirState → (Addr → Rat)` (using `BehaviorCodec.id`), or
  equivalently proves the permission invariant in `theory/` via `Compiles L_mir L_frac`.

Basis: **source** — `utwente-fmt/vercors@3300d5b007286225a33c17a233bda77db9471213`,
`FStarLang/FStar@e2b5042ffd8272ad6287e4ad8748d8e52dadd93d`, and
`Trusted/Refinement.lean:380-385`; **derived** — deterministic ghost-state
initialization pattern for `BehaviorCodec`.

---

#### 3.4 `UC-2.4`: Branded interior mutability and linear ghost permissions (`GhostCell`/`qcell`, `Verus` `Tracked<PointsTo<T>>` and `PCell`)

##### Goals, problem domain, and target users

Cyclic graphs, intrusive doubly-linked lists, B+trees with sibling pointers,
and slab allocators cannot be written in safe Rust without runtime reference
counting (`Rc<RefCell<T>>`) unless the *data location* (`UnsafeCell<T>`) is
decoupled from the *linear permission token* granting access to it.

##### Development history, lineage, and evolution

- **`GhostCell` (`iris/lambda-rust@186900b2cf948835873281646ce20c7e8f084f17`,
  Yanovski, Dang, Jung, Dreyer, ICFP 2021, DOI `10.1145/3473597`) and `qcell`
  (`jbowers/qcell`, `LCell`):** Uses Hindley-Milner rank-2 polymorphic lifetime
  branding (`GhostToken::new(|mut token: GhostToken<'brand>| ...)`):
  `&'a GhostCell<'brand, T>` can be freely aliased, while borrowing `&'a
  GhostToken<'brand>` yields `&'a T` and borrowing `&'a mut GhostToken<'brand>`
  yields `&'a mut T` at zero runtime cost (`GhostToken<'brand>` is a zero-sized
  type, ZST).
- **`Verus` (`verus-lang/verus@0141ebc6f14410dfc87fef1da57408578002eb7c`,
  Lattuada et al., OOPSLA 2023, DOI `10.1145/3586037`; SOSP 2024):** Replaces
  separation logic's spatial conjunction (`*`) with **first-class linear ghost
  types** checked by `rustc`'s own borrow checker across three modes: `exec`
  (compiled code), `tracked` (linear ghost permissions erased at compile time),
  and `spec` (duplicable mathematical specifications). A `PCell<T>` (`exec`) is
  paired with `Tracked<PointsTo<T>>` (`tracked`), so standard SMT (`Z3` via
  `VIR` $\to$ `AIR`) verifies pointer graphs without spatial frame inference!

##### Exact mapping onto Anneal's four `trusted/` primitives

In `Runtime(PostCleanup)` MIR, both `GhostToken<'brand>` and Verus's
`Tracked<PointsTo<T>>` are erased (or compiled to 0-byte ZST locals), and
`'brand` lifetimes do not exist at runtime. In Anneal:

- `anneal-rustc-capture` extracts pre-erasure `'brand` / ghost-type annotations
  as untrusted side-table metadata into `theory/`.
- `theory/` defines a pure arena language `L_arena` where the ZST token is
  reified as a pure finite map `Arena : AllocId → Val`, and proves
  `Abstracts L_arena L_mir codec f_arena f_mir` + `L_arena.ProductiveOn pre f_arena`
  directly over the lifetime-erased `L_mir` operational semantics.

Basis: **source** — `verus-lang/verus@0141ebc6f14410dfc87fef1da57408578002eb7c`
and GhostCell ICFP 2021 DOI `10.1145/3473597`; **derived** — ZST/lifetime
reification via `Abstracts L_arena L_mir`.

---

### 4. Category C: Aliasing and borrow models (`UC-3.1`–`UC-3.4`)

#### 4.1 `UC-3.1`: Operational borrow shadow-state machines (`Miri`, `Stacked Borrows`, `Tree Borrows`, `BorrowSanitizer`)

##### Goals, problem domain, and target users

Because `rustc` emits LLVM `noalias`, `readonly`, and `dereferenceable`
attributes on reference parameters (`&T`, `&mut T`), unsafe Rust code that mixes
references and raw pointers (`*const T`, `*mut T`) must obey a dynamic aliasing
state machine or risk miscompilation. Operational borrow models define that
exact state machine so interpreters (`Miri`), sanitizers (`BorrowSanitizer`),
and deductive verifiers (`Anneal`) can detect aliasing UB.

##### Development history, lineage, and evolution

- **`Stacked Borrows` (Jung, Dang, Kang, Dreyer, POPL 2020, DOI
  `10.1145/3371109`) and `Miri`
  (`rust-lang/miri@0e1a23b0794bec7860df8c06a774f4316746795a`):** Maintains a
  per-byte stack of borrow tags (`Unique(t)`, `SharedReadWrite(t)`,
  `SharedReadOnly(t)`, `Disabled`) in shadow memory. Any access through tag $t$
  pops (or disables) all tags above $t$ on the stack. While sound for basic
  `noalias`, Stacked Borrows eagerly performs a logical read on every `Retag` and
  forbids common two-phase borrow and `container_of!` raw-pointer patterns.
- **`Tree Borrows` (Villani, Hostert, Dreyer, Jung, PLDI 2025, DOI
  `10.1145/3735592`; `rust-lang/miri@0e1a23b0794bec7860df8c06a774f4316746795a`):**
  Replaces the per-byte stack with a **per-allocation borrow tree** where each
  node carries a 4-state permission automaton (`Reserved` $\to$ `Active` $\to$
  `Frozen` $\to$ `Disabled`) classified by relative tree position (`Child` vs.
  `Foreign` access). Lazy initialization (`Reserved` tolerating foreign reads
  until the first child write transitions to `Active`) validates two-phase
  borrows and out-of-bounds pointer arithmetic natively. Function-entry
  `RetagKind::FnEntry` attaches a **`Protector`** tied to the active call frame
  `CallId`, making it immediate UB for a protected tag to lose its permission
  before the function returns.
- **`BorrowSanitizer` (`BorrowSanitizer/bsan@a2fd46ab89fc97ba1cf548645dd70acbeaa17d64`):**
  Compiles Tree Borrows shadow-tree tracking directly into LLVM IR
  instrumentation passes, allowing native-speed fuzzing and cross-language
  Rust/C/C++ FFI aliasing checks that `Miri` cannot execute without source.

##### Exact mapping onto Anneal's four `trusted/` primitives

Tree Borrows interacts with Anneal's `trusted/` primitives in three ways:

1. **Tag-Erasure Abstraction (`Abstracts L_untagged L_mir_tb codec f f`):**
   Once a static borrow analysis (`UC-3.2`) or separation-logic proof (`UC-2.1`)
   establishes that a function never triggers a Tree Borrows transition to
   `Disabled` on an accessed or protected tag, `Abstracts L_untagged L_mir_tb`
   erases the `BorrowTree` shadow state so downstream functional proofs in
   `theory/` reason over plain untagged memory `(AllocId, Offset)`.
2. **Cross-Model Refinement (`Compiles L_sb L_tb codec f f`):**
   On the eager-retag fragment without lazy `Reserved` writes, Stacked Borrows
   is stricter than Tree Borrows (more states transition to `.failed .ub`),
   expressed horizontally as `L_tb.sem f ≤ codec.toMorphism (L_sb.sem f)`.
3. **Function-Entry Protectors Across `StepResult.externalCall`:**
   Because a Tree Borrows `Protector` on a reference argument requires the tag
   to remain valid until the enclosing call frame exits, an external callback
   invoked via `StepResult.externalCall boundaryInv branches` must not clobber a
   protected location of an active caller frame—requiring `MirState` in
   `trusted/` to track active `CallFrameId`s and `externalCall` to enforce
   protector survival.

Basis: **source** — `rust-lang/miri@0e1a23b0794bec7860df8c06a774f4316746795a`,
Tree Borrows PLDI 2025 DOI `10.1145/3735592`, Stacked Borrows POPL 2020 DOI
`10.1145/3371109`, `BorrowSanitizer/bsan@a2fd46ab89fc97ba1cf548645dd70acbeaa17d64`,
and `anllvm-verified-llvm-lowering-tree-borrows-noalias-and-binary-tv-2026`;
**derived** — `Abstracts` tag-erasure theorem and `externalCall` protector
invariant.

---

#### 4.2 `UC-3.2`: Static borrow-checker and loan-reachability models (`Polonius`, `Oxide`/`Patina`, `Aquascope`)

##### Goals, problem domain, and target users

Static borrow models formalize `rustc`'s compile-time borrow checker (`NLL` and
`Polonius`) so that safe Rust programs can be proved free of aliasing violations
statically without per-instruction runtime borrow-tree proofs.

##### Development history, lineage, and evolution

- **`Patina` (Reed, Univ. Washington Tech Report `UW-CSE-15-03-02`, 2015) and
  `Oxide` (Weiss et al., `arXiv:1903.00982v4`, 2019/2021):** Syntactic type
  systems for surface/HIR Rust where lifetimes are modeled directly as concrete
  provenance sets of loans (`{ℓ₁, …, ℓₖ}`) ordered by path prefixes (`x.f`).
- **`Polonius` (`rust-lang/polonius@bfd4c945b7713d0e66a3cde80475d9a4494740df`)
  and `Aquascope`
  (`cognitive-engineering-lab/aquascope@f2d0a06034b86765a91f10b7c8e40ec31ecb87a6`,
  Crichton et al., CHI 2023):** `Polonius` reformulates `rustc`'s borrow checker
  as a Datalog Horn-clause fixpoint over base facts (`loan_issued_at(O, L, P)`,
  `loan_invalidated_at(P, L)`, `loan_killed_at(L, P)`, `subset_base(O1, O2, P)`,
  `cfg_edge(P1, P2)`), computing transitive origin inclusion `subset(O1, O2, P)`
  and `origin_contains_loan_at(O, L, P)` to check that
  `loan_invalidated_at(P, L) ⋈ origin_contains_loan_at(O, L, P) ⋈ origin_live_on_entry(O, P)`
  is empty. `Aquascope` extracts and visualizes these Polonius loan permissions
  (`R`/`W`/`O`) across MIR points.

##### Exact mapping onto Anneal's four `trusted/` primitives

Instead of trusting `rustc`'s borrow checker or computing a slow Datalog
transitive closure inside Lean's kernel, `anneal-rustc-capture` (or an external
solver) emits the pre-computed relation tables `PoloniusCert`, and a verified
boolean checker `checkPolonius : PoloniusInput → PoloniusCert → Bool` in
`theory/` checks in $O(|E| \cdot |\text{Origins}|^2)$ time via `decide` that
`PoloniusCert` contains all base facts, is closed under each Polonius Horn
clause, and has an empty error relation—discharging the aliasing obligations in
`VerificationResult` needed by `UC-3.1` and `UC-1.1`.

Basis: **source** — `rust-lang/polonius@bfd4c945b7713d0e66a3cde80475d9a4494740df`,
`cognitive-engineering-lab/aquascope@f2d0a06034b86765a91f10b7c8e40ec31ecb87a6`,
and Oxide `arXiv:1903.00982v4`; **derived** — certifying Datalog post-fixpoint
checker in `theory/`.

---

#### 4.3 `UC-3.3`: Pointer-integer casts, strict/exposed provenance, and hardware capabilities (`Strict/Exposed Provenance`, `VIP`, `CompCertS`/`Quasi-Concrete`, `CHERI`/`Morello`)

##### Goals, problem domain, and target users

Lock-free data structures, radix trees, NaN-boxed runtimes, and page-table
descriptors pack metadata bits into the low alignment bits of pointers (`ptr.map_addr(|a| a | tag)`),
while FFI and serialization code casts pointers to integers (`expose_provenance`
/ `with_exposed_provenance`). Memory models must support pointer-integer
arithmetic without breaking alias analysis of unexposed allocations.

##### Development history, lineage, and evolution

- **`CompCertS` (Besson, Blazy, Wilke, POPL 2014 / JFP 2019) and
  `Quasi-Concrete Memory` (Kang, Hur, Mansky, Garbuzov, Zdancewic, Vafeiadis,
  POPL 2015, DOI `10.1145/2676726.2676985`):** Extend CompCert's block-offset
  memory `(b, ofs)` (`CompCert Memdata`) so that symbolic bitwise expressions on
  pointers are lazily evaluated (`CompCertS`) or logical blocks receive concrete
  base addresses on first integer cast (`Quasi-Concrete`).
- **`VIP` (Virtual Integer-Pointer Model in `RefinedC`, Lepigre et al., PLDI
  2022, DOI `10.1145/3519939.3523702`):** Replaces angelic provenance guessing
  with deterministic `copy_alloc_id(int_addr, orig_ptr)` operations (`with_addr`
  in Rust), enabling automated separation-logic verification of tagged pointers
  in `RefinedC`/Lithium.
- **`Rust Strict & Exposed Provenance` (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`,
  `library/core/src/ptr/`, RFC 3559):** Splits pointer-integer operations into
  deterministic **Strict Provenance** (`ptr.addr()`, `ptr.with_addr(a)`,
  `ptr.map_addr(f)`, preserving `AllocId`) and **Exposed Provenance**
  (`ptr.expose_provenance()`, `ptr::with_exposed_provenance(a)`).
- **`CHERI` and `Arm Morello`
  (`CTSRD-CHERI/sail-morello@2305f656ff84619caf50107f49dae7be52aec72b`,
  `rems-project/coq-cheri-capabilities@b39cd73409d8c2a058ba8065f81dc72d3c84fb11`):**
  Enforce provenance in hardware via 129-bit capabilities (64-bit address +
  compressed bounds + permissions + 1-bit hardware validity tag cleared on
  unaligned or out-of-bounds byte writes).

##### Exact mapping onto Anneal's four `trusted/` primitives

1. **Tagged-Pointer Algebraic Lens (`Abstracts L_tagged L_mir codec f_tagged f_mir`):**
   For Strict Provenance (`map_addr`), `L_tagged` models a $2^k$-aligned tagged
   pointer as `ValidPtr T × BitVec k`, and `codec.encodeQuery` packs it into
   `MirVal.ptr allocId (base + offset ||| tag)` with bitvector obligations
   discharged by `bv_decide` in `VerificationResult`.
2. **Demonic vs. Angelic Nondeterminism in `with_exposed_provenance`:**
   In C's `PNVI-ae-udi` (`Cerberus`) and `MiniRust`, `with_exposed_provenance(addr)`
   is specified via **angelic** choice over all previously exposed `AllocId`s.
   In Anneal's `Behavior Query Out := Query → Partial (Out → Prop)`,
   nondeterminism in `StepResult.choice` is **demonic**: refinement `≤` requires
   *every* branch to be UB-free (`defined`). If `L_mir` modeled
   `with_exposed_provenance(addr)` as a demonic choice over all exposed
   `AllocId`s, exposing two allocations would cause one branch to pick the wrong
   `AllocId` and hit `.failed .ub`, falsifying `(L_mir.sem p q).defined`!
   Therefore, `L_mir` in `trusted/` must resolve `with_exposed_provenance(addr)`
   deterministically by selecting the unique live exposed allocation whose
   concrete range $[\text{base}, \text{base}+\text{size})$ contains `addr` (or
   model one-past-the-end ambiguity in `Query`).

Basis: **source** — `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`,
VIP PLDI 2022 DOI `10.1145/3519939.3523702`, Quasi-Concrete POPL 2015 DOI
`10.1145/2676726.2676985`, `CTSRD-CHERI/sail-morello@2305f656ff84619caf50107f49dae7be52aec72b`,
and `Trusted/StepResult.lean:176-187`; **derived** — demonic-vs.-angelic
provenance resolution constraint on `L_mir`.

---

#### 4.4 `UC-3.4`: Normative byte-level memory models (`MiniRust`, `Cerberus`, `CompCert Memdata`)

##### Goals, problem domain, and target users

Normative operational semantics for Rust (`MiniRust`) and C (`Cerberus`,
`CompCert Memdata`) define memory as flat arrays of abstract bytes carrying
initialization and provenance fragments so that low-level idioms (`memcpy`,
union punning, padding bytes, `zerocopy` transmutations) have an unambiguous
ground truth.

##### Development history, lineage, and evolution

- **`CompCert Memdata`
  (`AbsInt/CompCert@f9573fb9b8ba4b4cecebe1ef3cb8b2ef9ce1fc03`, `common/Memdata.v`,
  Leroy & Blazy, JAR 2008):** Defines `memval := Undef | Byte (b : byte) |
  Fragment (v : val) (q : quantity) (n : nat)`, where a 64-bit pointer stored in
  memory is split into 8 symbolic `Fragment` bytes that read back as `Vundef` if
  partially overwritten.
- **`Cerberus` (`rems-project/cerberus@c8c085d4714ae17095b2e1202fa33c5545d98df1`,
  Memarian et al., POPL 2019):** De facto ISO C11/C2X operational reference
  model parameterized by memory models (`PNVI-ae-udi`, `VIP`, symbolic),
  translating C into typed functional `Core` IR.
- **`MiniRust` (`minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`):**
  Literate `specr` specification of Rust's operational semantics where memory
  stores `AbstractByte := Uninit | Init (data : UInt8) (provenance : Option Prov)`,
  and every typed load/store converts between structured `Value` trees and
  `List AbstractByte` through type layout descriptors (`Tuple`, `Union`, `Int`,
  `Ptr`), enforcing validity invariants (`bool` $\in \{0,1\}$, non-null references,
  initialized non-padding bytes) on every typed load and return.

##### Exact mapping onto Anneal's four `trusted/` primitives

Establishing bilateral behavioral equivalence between a mechanized MiniRust model
`L_minirust` in `theory/` and Anneal's `L_mir` (`Compiles L_minirust L_mir codec p p ∧
Abstracts L_minirust L_mir codec p p`) surfaces the **Padding-Byte Stress Test**
for `BehaviorCodec.encodeOut_of_decodeOut`:

- In `MiniRust`, a struct `#[repr(C)] struct Padded { a: u8, b: u16 }` occupies
  4 bytes where byte offset 1 is padding. Two distinct final memory states $o_2
  \neq o_2'$ (one with byte 1 = `Uninit`, one with byte 1 = `Init 0xFF none`)
  both decode to the same logical struct value `Padded { a, b }`.
- Under `BehaviorCodec`'s partial-bijection law
  `decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`, `decodeOut` cannot map both
  $o_2$ and $o_2'$ to `some (Padded { a, b })`!
- Therefore, `L_mir`'s `SmallStepMachine` terminal step (`.terminated term`) must
  project the return value through the return type's layout decoding before
  constructing `EventualOut Obs Val` (stripping unobservable padding bytes and
  dead stack slots at the machine return boundary), so `decodeOut` operates on
  canonicalized return values.

Basis: **source** — `minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`,
`rems-project/cerberus@c8c085d4714ae17095b2e1202fa33c5545d98df1`,
`AbsInt/CompCert@f9573fb9b8ba4b4cecebe1ef3cb8b2ef9ce1fc03`, and
`Trusted/Refinement.lean`; **derived** — return-value canonicalization
requirement for `encodeOut_of_decodeOut`.

---

### 5. Category D: Type systems, typestates, and effect checkers (`UC-4.1`–`UC-4.4`)

#### 5.1 `UC-4.1`: Liquid and index-refinement type checkers (`Flux`, `Liquid Haskell`, `Stainless`)

##### Goals, problem domain, and target users

Most runtime panics and unsafe precondition failures in systems Rust (`slice[i]`,
`get_unchecked(i)`, `NonZeroUsize::new_unchecked(x)`, `Vec` capacity bounds,
matrix stride invariants) reduce to linear integer or bitvector predicates over
scalar values and struct fields. Refinement type systems attach logical
predicates $\{v : B \mid p(v)\}$ to base types so subtyping checks reduce to
decidable SMT Horn clauses without user-written loop invariants or proof
scripts.

##### Development history, lineage, and evolution

- **`Liquid Haskell` (`ucsd-progsys/liquidhaskell@c0cca0b9f92d8cdaae7f8fc604f78c32b534b69d`,
  Vazou, Seidel, Jhala, Vytiniotis, Peyton Jones, ICFP 2014, DOI
  `10.1145/2628136.2628161`):** Combined Rondon, Kawaguchi, and Jhala's Logically
  Qualified Data Types (Liquid Types, predicate abstraction over a finite set of
  qualifiers $\mathbb{Q}$) with GHC Core typing and SMT-backed Refinement
  Reflection (`ple`, Proof by Logical Evaluation).
- **`Stainless` (`EPFL-LARA/stainless@399c34a06df8e88679f0985131e8a59a28ab9b3f`,
  Hamza, Voirol, Kunčak, OOPSLA 2019):** Verifies Scala programs with refinement
  types, `require`/`ensuring` contracts, and termination measures by counterexample-guided
  unfolding of recursive functions (`Inox` solver).
- **`Flux` (`flux-rs/flux@6769bb9cbd1216380f542349494efafafd6104a3`, Lehmann,
  Geller, Vazou, Jhala, PLDI 2023, DOI `10.1145/3591283`):** Adapts Liquid Types
  to Rust MIR by separating pure mathematical **indices** (`int`, `bool`) from
  Rust's mutable locations: `i32[n]` denotes a 32-bit integer equal to index $n$,
  `&strg T` denotes a strong reference whose target index may change across a
  mutation (`fn incr(x: &strg i32[@n]) ensures x: i32[n + 1]`), and existential
  refinements `{v. i32[v] | v > 0}` are inferred at loop headers via
  `liquid-fixpoint` Horn-clause solving.

##### Design philosophy, architectural tradeoffs, and TCB comparisons

`Flux`, `Liquid Haskell`, and `Stainless` keep the refinement typechecker,
Horn-clause generator, and `Z3`/`cvc5` inside their TCB. A critical hazard in
refinement type systems is **precondition inconsistency**: if a function's input
refinement environment $\Gamma$ is unsatisfiable (e.g., `fn bad(x: usize{x > 10
&& x < 5})` or contradictory assumed Refinement Reflection axioms), every
subtyping Horn clause $\llbracket \Gamma \rrbracket \wedge \phi_1 \Rightarrow
\phi_2$ becomes vacuously valid (`False → φ₂`), allowing the function to pass
`unsafe { unreachable_unchecked() }`.

##### Exact mapping onto Anneal's four `trusted/` primitives

In Anneal's `theory/`, `Flux` is realized as a **certifying refinement
typechecker** `checkFluxTypes : MirBody → FluxSig → FluxCert → List Obligation`:

1. **Certifying Horn-Solution Checking (Zero `liquid-fixpoint` in TCB):**
   `Flux` runs outside Lean to infer loop-header refinement environments
   $\Gamma_{\text{bb}}$ and emits them as `FluxCert`. `checkFluxTypes` in
   `theory/` generates one `Obligation` in `VerificationResult` per subtyping
   check $\Gamma \vdash \{v : T \mid \phi_1\} <: \{v : T \mid \phi_2\}$,
   discharged by Lean's `omega` or `bv_decide`.
2. **Blocking Contradictory Refinement Preconditions via `InhabitedPre`:**
   Anneal's mandatory `InhabitedPre pre_flux` (`∃ q, pre_flux q`) in
   `trusted/lean/` forces every function's entry refinement environment to be
   inhabited (or explicitly waived if the input type is `Infallible`),
   preventing inconsistent refinement preconditions from manufacturing vacuous
   UB proofs.
3. **Granular Waivers via `VerificationResult`:**
   If a single nonlinear subtyping obligation `ob_k` in a function is not yet
   proved, `VerificationResult policy waived obligations` allows waiving `ob_k.id`
   without losing verification of all remaining bounds checks in that function.

Basis: **source** — `flux-rs/flux@6769bb9cbd1216380f542349494efafafd6104a3`,
`ucsd-progsys/liquidhaskell@c0cca0b9f92d8cdaae7f8fc604f78c32b534b69d`,
`EPFL-LARA/stainless@399c34a06df8e88679f0985131e8a59a28ab9b3f`, and
`Trusted/Refinement.lean`; **derived** — `InhabitedPre` non-vacuity guard and
per-subtyping `VerificationResult` obligations.

---

#### 5.2 `UC-4.2`: Typestates and protocol state-machine verifiers (`embedded-hal`/`embassy`, `Verus tokenized_state_machine!`)

##### Goals, problem domain, and target users

Device drivers, DMA controllers, MMIO peripheral configurations, and
cryptographic state machines must obey temporal transition protocols (e.g., a
DMA buffer must transition `Allocated → Pinned → Submitted → Completed →
Unpinned` and must never be mutated or dropped by the CPU while `Submitted` to
hardware).

##### Development history, lineage, and evolution

- **`embedded-hal` (`rust-embedded/embedded-hal@41f29f6bfced1cae0cbe712ba96ee32c075b3125`)
  and `embassy` (`embassy-rs/embassy@14cf6a68ec0bfd0ecf873f7e3dbb2eb69013fa29`):**
  Encode hardware peripheral typestates in safe Rust using phantom type
  parameters (`GpioPin<Input<PullUp>>` consumed by value in `into_push_pull_output(self) -> GpioPin<Output<PushPull>>`).
  While zero-cost, Rust's affine type system alone cannot verify the `unsafe`
  MMIO register writes inside the transition methods or prevent `mem::forget`
  of an in-flight DMA transfer guard.
- **`Verus tokenized_state_machine!`
  (`verus-lang/verus@0141ebc6f14410dfc87fef1da57408578002eb7c`,
  `source/state_machines_macros/`):** Compiles a declarative protocol state
  machine (with sharded field strategies `variable`, `map`, `multiset`,
  `storage_option`) into linear `tracked` token types and exchange lemmas,
  proving that local token transitions correspond to valid global state-machine
  steps.

##### Exact mapping onto Anneal's four `trusted/` primitives

In Anneal, a driver or protocol implementation `f_mir` is verified via
`Abstracts L_automaton L_mir codec auto_prog f_mir` using
`StepResult.externalCall boundaryInv branches` at every `read_volatile` /
`write_volatile` / DMA submission boundary:

- **Enforcing Safety on Diverging Reactive Loops without Coinductive Streams:**
  In `Trusted/StepResult.lean`, `EventualOut.terminated (trace : List Obs) term`
  carries `trace : List Obs`, whereas `EventualOut.diverges` carries no trace
  payload. How does Anneal verify that a non-terminating interrupt/polling loop
  (`loop { poll_mmio(); }`) never violates the DMA/MMIO typestate automaton?
- Because every MMIO/DMA call executes `StepResult.externalCall boundaryInv branches`
  where `boundaryInv : Bool` checks that the current typestate permits the
  hardware operation, any protocol violation at finite step $k$ immediately
  transitions to `.failed .ub`—falsifying `(L_mir.sem f_mir q).defined`! Thus,
  `StepResult.externalCall`'s `boundaryInv` enforces safety properties of
  infinite reactive traces online at every step without needing coinductive
  streams in `EventualOut.diverges`.

Basis: **source** — `rust-embedded/embedded-hal@41f29f6bfced1cae0cbe712ba96ee32c075b3125`,
`embassy-rs/embassy@14cf6a68ec0bfd0ecf873f7e3dbb2eb69013fa29`,
`verus-lang/verus@0141ebc6f14410dfc87fef1da57408578002eb7c`, and
`Trusted/StepResult.lean`; **derived** — `boundaryInv` trace-safety enforcement
on `.diverges` loops.

---

#### 5.3 `UC-4.3`: Strict linear, must-consume, and unwind drop-obligation verifiers (`Austral`, `Vale`)

##### Goals, problem domain, and target users

Rust's ownership system is **affine**, not **linear**: `core::mem::forget(x)`,
`ManuallyDrop::new(x)`, `Rc` cycles, or early panic unwinding while a container
is temporarily disassembled (`Vec::drain`, `BTreeMap` node splits, spinlock
guards, DMA in-flight guards) can skip cleanup and leak linear obligations or
leave broken invariants exposed.

##### Development history, lineage, and evolution

- **`Austral` (`austral/austral@0962d2a8a5d77f7daacd7f696819520733f4897d`,
  Borretti, 2022):** A systems language with a strict **linear type system**
  (`Linear` universe distinct from `Free`) where linear values cannot be
  implicitly dropped or forgotten along any control path, and capability-based
  borrowing (`&[R, W]`) is scoped lexically without lifetime inference.
- **`Vale` (`project-everest/vale@bbae0eb89143734363b14a77642dbf8dec36e288`,
  Bond et al., USENIX Security 2017):** Verified Assembly Language for Everest
  (F\* / Dafny), using linear ghost state and register/memory framing to ensure
  cryptographic secrets and stack capabilities are consumed and scrubbed along
  every exit path.

##### Exact mapping onto Anneal's four `trusted/` primitives

In `Runtime(PostCleanup)` MIR, `rustc` has already run drop elaboration,
lowering normal drops and stack-unwinding cleanup ladders into explicit CFG
edges terminating at `Return` (`TerminationKind.normal`) or `UnwindResume` /
`UnwindTerminate` (`TerminationKind.unwind`). A certifying linear dataflow
checker in `theory/` verifies `L_mir.sem f ≤ L_mir.SpecOn pre post_linear` where
`post_linear` inspects `EventualOut.terminated trace term` across **both**
`term = .normal v` and `term = .unwind`, proving that every linear resource
token acquired during execution is consumed before normal return or panic
unwind.

Basis: **source** — `austral/austral@0962d2a8a5d77f7daacd7f696819520733f4897d`,
`project-everest/vale@bbae0eb89143734363b14a77642dbf8dec36e288`, and
`Trusted/StepResult.lean:58-60`; **derived** — dual `.normal`/`.unwind` terminal
inspection in `SpecOn`.

---

#### 5.4 `UC-4.4`: Capability and algebraic effect checkers (`no-panic`, `rtsan`/`cargo-call-stack`, `F*`/`Low*`/`KaRaMeL`, `Koka`/`Effekt`)

##### Goals, problem domain, and target users

Kernel interrupt service routines (ISRs), real-time audio/control threads,
bare-metal firmware, and deterministic consensus/cryptography modules require
transitive effect absence guarantees: `#[no_panic]` (never unwinds or aborts),
`#[no_alloc]` (never calls heap allocator), `#[no_blocking]` (never sleeps),
bounded stack usage, and exact input-to-output determinism.

##### Development history, lineage, and evolution

- **`no-panic` (`dtolnay/no-panic@9a0b1097f77dfd5ee4352b6ff060f68d791730f7`),
  `cargo-call-stack` (`japaric/cargo-call-stack@49080d56b827573f1e19ff127401e312d08f138c`),
  and LLVM `rtsan` (`llvm/llvm-project@3623fe661ae35c6c80ac221f14d85be76aa870f1`,
  `compiler-rt/lib/rtsan`):** `no-panic` inserts a linker symbol call inside a
  drop guard on the unwind path and relies on LLVM `-O2`/`-O3` dead-code
  elimination to delete it—an optimization-dependent heuristic that breaks across
  compiler versions and gives no formal guarantee at the MIR level.
  `cargo-call-stack` analyzes LLVM call graphs and DWARF frame sizes; `rtsan`
  detects real-time violations (`malloc`, `pthread_mutex_lock`) dynamically or
  via clang `[[clang::nonblocking]]` effect attributes.
- **`F*`, `Low*`, and `KaRaMeL`
  (`FStarLang/FStar@e2b5042ffd8272ad6287e4ad8748d8e52dadd93d`,
  `FStarLang/karamel@9abbb865b10a0cd5c557da81c024c3965cb6ff53`, Protzenko et
  al., ICFP 2017, DOI `10.1145/3110261`):** `F*` indexes computations by an
  effect lattice (`Tot`, `GTot`, `DIV`, `ST`, `Exn`, `Stack` in `Low*`). `Low*`
  uses the `Stack` effect (`Stack a (requires h0 => ...) (ensures (h0, x, h1) => ...)`)
  to guarantee statically that a function performs zero heap allocations and
  never leaks stack frames, extracting to allocation-free C via `KaRaMeL`.
- **`Koka` (`koka-lang/koka@d23ee7cd73737c1da7a7a5fa837a2806facc3d6b`, Leijen,
  EPTCS 2014, DOI `10.4204/EPTCS.153.8`) and `Effekt`
  (`effekt-lang/effekt@91c540b1067721bdd1bb5d463e42827f8316a1da`, Brachthäuser
  et al., OOPSLA 2020, DOI `10.1145/3428194`):** Track algebraic effects via
  row-polymorphic effect types (`total`, `exn`, `div`, `st<h>`, `io`) or
  lexical capability passing (`Effekt`).

##### Exact mapping onto Anneal's four `trusted/` primitives

Every effect in the `F*`/`Low*`/`Koka` lattice corresponds directly to a subset
specification `L_mir.SpecOn` or `Abstracts` edge in Anneal:

- **`no_panic` (`Exn`-free):** `L_mir.sem f ≤ SpecNoPanic`, where `SpecNoPanic`
  assigns `False` to `EventualOut.terminated _ .unwind`. Unlike `dtolnay/no-panic`,
  this is proved over `L_mir` (and preserved down to assembly via `Compiles`)
  independent of LLVM dead-code heuristics.
- **`no_alloc` / `no_blocking` (`Stack` / capability restriction):**
  `L_mir.sem f ≤ SpecTraceFree isForbiddenEffect`, requiring every event `e ∈
  trace` emitted by `StepResult.externalCall` to satisfy `¬ isForbiddenEffect e`.
- **Exact Determinism (`Tot`):** Proving `Abstracts L_det L_mir codec f_det f_mir`
  (where `L_det` has singleton outcome sets `{f_det q}`) together with
  `L_mir.ProductiveOn pre f_mir` forces every execution of `f_mir` to produce
  the exact singleton outcome `{encodeOut (f_det (decodeQuery q))}`.

Basis: **source** — `dtolnay/no-panic@9a0b1097f77dfd5ee4352b6ff060f68d791730f7`,
`FStarLang/FStar@e2b5042ffd8272ad6287e4ad8748d8e52dadd93d`,
`FStarLang/karamel@9abbb865b10a0cd5c557da81c024c3965cb6ff53`,
`koka-lang/koka@d23ee7cd73737c1da7a7a5fa837a2806facc3d6b`,
`effekt-lang/effekt@91c540b1067721bdd1bb5d463e42827f8316a1da`, and
`Trusted/Refinement.lean`; **derived** — effect-lattice mapping onto `SpecOn`
and `ProductiveOn`.

---

### 6. Category E: Sound static analyzers and abstract interpreters (`UC-5.1`–`UC-5.4`)

#### 6.1 `UC-5.1`: Certifying numerical abstract interpreters (`Verasco`, `Astrée`, `Crab`/`SeaHorn`, `IKOS`, `MIRAI`)

##### Goals, problem domain, and target users

Routine arithmetic overflow, division/remainder by zero, and array/slice bounds
checks inside loops can often be discharged automatically without user-written
loop invariants by computing an inductive post-fixpoint in a numerical abstract
domain: **Intervals** ($a \le x \le b$), **Zones / Difference-Bound Matrices**
($x - y \le c$), **Octagons** ($\pm x \pm y \le c$), or **Convex Polyhedra**
($A\vec{x} \le \vec{b}$).

##### Development history, lineage, and evolution

- **`Astrée` (Cousot, Cousot, Feret, Mauborgne, Miné, Monniaux, Rival, ESOP
  2005, DOI `10.1007/978-3-540-31987-0_3`):** Proved absence of runtime errors in
  Airbus A340/A380 fly-by-wire C code by combining intervals, octagons, digital
  filter ellipsoid domains, and trace partitioning with widening ($\nabla$) and
  narrowing ($\Delta$).
- **`Verasco` (Jourdan, Laporte, Blazy, Leroy, Pichardie, POPL 2015, DOI
  `10.1145/2676726.2676966`):** Foundational static analyzer for CompCert `Csharpminor`
  verified in Rocq. `Verasco` decouples **untrusted fixpoint iteration** (using
  widening/narrowing to compute candidate loop invariants) from **verified
  post-fixpoint checking**, and uses **Farkas Lemma non-negative linear
  combination certificates** ($\vec{\lambda} \ge 0$ such that $\vec{\lambda}^T A =
  \vec{c}^T$ and $\vec{\lambda}^T \vec{b} \le d$) to verify polyhedral inclusion
  $P \sqsubseteq^{\#} Q$ inside Rocq without trusting an external simplex/PPL
  library.
- **`IKOS` (`NASA-SW-VnV/ikos@ac7f7c1738976cabc58c6a53413df6e458995c38`, Brat
  et al., NFM 2014), `Crab`, and `SeaHorn`
  (`seahorn/crab@b1eeb1a9402ab0664e962f26f89d923f8514284c`,
  `seahorn/seahorn@892780176731ec8e97bbb9f6b172fcacd77a8ff4`, Gurfinkel et
  al., CAV 2015):** LLVM-based C++/C abstract interpreters (`Crab` supplies
  Zones/Octagons invariants to `SeaHorn`'s `Spacer` CHC solver).
- **`MIRAI` (`endorlabs/MIRAI@aae0a56f91d9a0a62073bb86e7b2c9793cefc24b`):**
  Abstract interpreter over Rust MIR combining symbolic summaries with Z3 path
  queries and taint/tag propagation.

##### Exact mapping onto Anneal's four `trusted/` primitives

Anneal directly adopts `Verasco`'s **untrusted fixpoint finder + verified
post-fixpoint checker** architecture inside `theory/`:

1. An external analyzer (`Crab`-style Rust tool) computes a candidate invariant
   map `inv : BasicBlockId → AbstractVal` and Farkas multiplier certificates
   `NumFixpointCert`.
2. In `theory/`, `checkNumFixpoint : MirBody → NumFixpointCert → Bool` verifies
   $F^{\#}(\text{inv}[\text{bb}]) \sqsubseteq^{\#} \text{inv}[\text{bb}']$ on
   every CFG edge and checks that $\text{inv}[\text{bb}]$ implies safety of each
   arithmetic/bounds check in block $\text{bb}$.
3. A generic 1-step inductive invariant lemma `SmallStepMachine.invariant_defined`
   proved once in `theory/` lifts the 1-step concretization soundness
   ($s \in \gamma(a) \to \text{step}(s) \neq \text{.failed .ub} \wedge s' \in
   \gamma(F^{\#}(a))$) directly to `EventualBehaviorOf` (`(L_mir.sem f q).defined`),
   discharging the numerical obligations in `VerificationResult`.

Basis: **source** — Verasco POPL 2015 DOI `10.1145/2676726.2676966`, Astrée ESOP
2005 DOI `10.1007/978-3-540-31987-0_3`, `seahorn/crab@b1eeb1a9402ab0664e962f26f89d923f8514284c`,
`NASA-SW-VnV/ikos@ac7f7c1738976cabc58c6a53413df6e458995c38`,
`endorlabs/MIRAI@aae0a56f91d9a0a62073bb86e7b2c9793cefc24b`, and
`Trusted/StepResult.lean`; **derived** — 1-step `SmallStepMachine` to
`EventualBehaviorOf` lifting theorem.

---

#### 6.2 `UC-5.2`: Bitfield, alignment, and `tnum` / `KnownBits` abstract domains (`eBPF tnum`/`Agni`/`PREVAIL`, `LLVM KnownBits`)

##### Goals, problem domain, and target users

Low-level systems code masks pointer alignment bits (`addr & !(align - 1)`),
manipulates page-table flags, and extracts packet bitfields where interval
domains $[l, u]$ lose all precision across bitwise `&`, `|`, `^`, and shifts.
The **tristate / `tnum` (`KnownBits`)** domain represents each bit of a $w$-bit
word as $\{0, 1, ?\}$ via a pair of masks `(value, mask)` (in Linux eBPF `tnum`,
where `value & mask == 0`) or `(known_zeros, known_ones)` (in LLVM `KnownBits`,
where `known_zeros & known_ones == 0`).

##### Development history, lineage, and evolution

- **`Linux eBPF tnum` and `Agni` (Vishwanathan, Shachnai, Narayana, Nagarakatte,
  PLDI 2022 DOI `10.1145/3519939.3523440`; CAV 2023 DOI
  `10.1007/978-3-031-37709-9_12`):** Formalized the Linux kernel eBPF verifier's
  `tnum` bitwise transfer functions (`tnum_add`, `tnum_sub`, `tnum_mul`,
  `tnum_and`, `tnum_or`, `tnum_xor`, `tnum_rshift`) and reduced product with
  signed/unsigned 64-bit and 32-bit intervals (`reg_bounds_sync`), finding real
  soundness bugs in kernel range-synchronization logic.
- **`PREVAIL` (`vbpf/prevail@cefe6a799f8b8f37aa2560e196f223802717c1e7`, Gershuni
  et al., PLDI 2019, DOI `10.1145/3314221.3314590`):** Polynomial-time eBPF
  abstract interpreter using the Zone domain (`SplitDBM`) over register and
  stack-slot types/offsets.
- **`LLVM KnownBits`
  (`llvm/llvm-project@3623fe661ae35c6c80ac221f14d85be76aa870f1`,
  `llvm/include/llvm/Support/KnownBits.h`):** Core LLVM bit-tracking analysis
  whose optimality and soundness have been mechanized in Lean 4 via `bv_decide`
  (`opencompl/lean-mlir@b8c4a77131919c8e18cf8bc7fdde40ef3cf87924`).

##### Exact mapping onto Anneal's four `trusted/` primitives

In `theory/`, the soundness of every 64-bit `tnum` / `KnownBits` abstract
transfer operator (`and#`, `or#`, `xor#`, `add#`, `shl#`, `lshr#`) is proved
**once and for all using `bv_decide`**. A per-function fixpoint certificate
`KnownBitsCert` is then checked by `checkKnownBits : MirBody → KnownBitsCert →
Bool` in `theory/`, discharging pointer-alignment UB obligations (`addr & (align - 1) == 0`)
and shift-bound obligations in `VerificationResult` alongside `checkNumFixpoint`
(`UC-5.1`) on the same function.

Basis: **source** — Agni CAV 2023 DOI `10.1007/978-3-031-37709-9_12`,
`vbpf/prevail@cefe6a799f8b8f37aa2560e196f223802717c1e7`,
`llvm/llvm-project@3623fe661ae35c6c80ac221f14d85be76aa870f1`, and
`opencompl/lean-mlir@b8c4a77131919c8e18cf8bc7fdde40ef3cf87924`;
**derived** — multi-analyzer composition in `VerificationResult`.

---

#### 6.3 `UC-5.3`: Byte-level initialization (`MaybeUninit`) and stack-escape analyzers (`Frama-C Eva`, `Goblint`, `Mopsa`, `Rudra`/`SafeDrop`/`Lockbud`)

##### Goals, problem domain, and target users

Unsafe Rust uses `MaybeUninit<T>`, `[MaybeUninit<u8>; N]`, and manual `ptr::write`
loops to initialize buffers incrementally before calling `assume_init()`.
Reading uninitialized non-padding bytes at a typed load or allowing a pointer to
a stack local to escape past `StorageDead` causes immediate UB.

##### Development history, lineage, and evolution

- **`Frama-C Eva` (`git.frama-c.com/pub/frama-c@ce0648c726122d4a7b5e8614a1a5b97777d9d226`,
  Bühler et al.; Kirchner et al., FAC 2015):** Evolved Value Analysis plug-in
  for Frama-C that tracks byte-level initialization bitmaps, escaping stack
  addresses (`\dangling`), and base-offset pointer maps (`cvalue`) across C
  code.
- **`Mopsa` (`mopsa/mopsa-analyzer@f168a9c025738d4940cfb6a281dde258c871da73`,
  Journault, Miné, Ouadjaout, NFM 2019) and `Goblint`
  (`goblint/analyzer@1463f411ce87edd49198033856b2946fc3366fb2`):** Modular
  abstract interpreters where cell-splitting memory domains (`Mopsa`) dynamically
  split and merge byte ranges upon type punning or partial initialization, while
  `Goblint` tracks multi-threaded points-to and escape sets.
- **`Rudra` (`sslab-gatech/Rudra@fc9add2c4721c77490680462c7f0ad791af7cec7`, Bae
  et al., SOSP 2021, DOI `10.1145/3477132.3483570`), `SafeDrop` (Cui et al.,
  TOSEM 2023), and `Lockbud`
  (`BurtonQin/lockbud@a1b5303cdbb1d4d0ad886359cc71418570e7c5fd`):** Rust MIR
  static bug finders targeting `unsafe` initialization bypasses (`Vec::set_len`
  before element writes, causing drop/read of uninitialized memory on panic),
  dangling pointers across drop glue, and double locks.

##### Exact mapping onto Anneal's four `trusted/` primitives

A certifying byte-initialization and escape checker `checkInitEscape : MirBody →
InitEscapeCert → Bool` in `theory/` tracks initialized byte ranges $[0, i)$ (for
example, coupled with loop induction variable $i$ from `UC-5.1`) and points-to sets
across `StorageLive` and `StorageDead`, discharging typed-load validity and
stack-escape UB obligations in `VerificationResult`. Across
`StepResult.externalCall` (such as an external I/O read initializing `0..ret`
bytes of a passed `MaybeUninit<u8>` slice), `branches` updates the
byte-initialization state of the slice according to the external function's
contract.

Basis: **source** — `git.frama-c.com/pub/frama-c@ce0648c726122d4a7b5e8614a1a5b97777d9d226`,
`mopsa/mopsa-analyzer@f168a9c025738d4940cfb6a281dde258c871da73`,
`goblint/analyzer@1463f411ce87edd49198033856b2946fc3366fb2`,
`sslab-gatech/Rudra@fc9add2c4721c77490680462c7f0ad791af7cec7`, and
`BurtonQin/lockbud@a1b5303cdbb1d4d0ad886359cc71418570e7c5fd`;
**derived** — byte-level `Uninit` + `StorageDead` requirement in `L_mir`.

---

#### 6.4 `UC-5.4`: Shape analysis and string/UTF-8 automaton domains (`TVLA`/`Forester`, `MemCAD`/`Xisa`)

##### Goals, problem domain, and target users

Pointer algorithms on lists/trees and byte-slice string routines calling
`core::str::from_utf8_unchecked` or `CStr::from_bytes_with_nul_unchecked`
require inductive shape invariants or regular-language (DFA) byte invariants.

##### Development history, lineage, and evolution

- **`TVLA` (Sagiv, Reps, Wilhelm, TOPLAS 2002, DOI `10.1145/514188.514190`) and
  `Forester` (Holík et al., CAV 2013):** `TVLA` abstracts unbounded heap graphs
  into finite 3-valued structures ($\{0, 1, 1/2\}$) using instrumentation
  predicates (reachability, cyclicity, sharing) and `Focus`/`Coerce` materialization.
  `Forester` represents heap shapes via forest automata.
- **`MemCAD` and `Xisa` (`Antique-team/memcad@d95caa514f2b66b8c43c015799084d281944f028`,
  Chang & Rival, POPL 2008, DOI `10.1145/1328438.1328469`):** Combine
  separation-logic inductive shape checkers (`Xisa`) with numerical abstract
  domains (`Apron`) to infer combined shape-and-data invariants automatically.

##### Exact mapping onto Anneal's four `trusted/` primitives

In Rust, violating the safety precondition of `core::str::from_utf8_unchecked(v)`
is **library UB** (producing an invalid `&str` that later causes safe UTF-8
iterators to execute out-of-bounds `get_unchecked`). In Anneal, `unsafe` library
contracts are modeled via `StepResult.externalCall (boundaryInv := isValidUtf8 v)
branches` (or a `SpecOn` precondition on the callee). A certifying UTF-8 DFA /
shape fixpoint checker in `theory/` proves `isValidUtf8 v = true` at the call
site, discharging `boundaryInv` and unifying language UB with library-contract
UB under a single `trusted/` primitive.

Basis: **source** — TVLA TOPLAS 2002 DOI `10.1145/514188.514190`,
`Antique-team/memcad@d95caa514f2b66b8c43c015799084d281944f028`, and
`Trusted/StepResult.lean`; **derived** — unifying library UB and language UB via
`StepResult.externalCall`.

---

### 7. Category F: VCGens, characteristic formulae, termination, and modular invariants (`UC-6.1`–`UC-6.4`)

#### 7.1 `UC-6.1`: Dijkstra monad and predicate-transformer weakest-precondition VCGens (`F*`/`DM4All`, `Why3`, `Boogie`, `Lean 4 MPL`/`Std.Do`)

##### Goals, problem domain, and target users

Deductive verification environments compile imperative or monadic programs into
backward **Weakest Precondition (`WP`)** predicate transformers
$\text{wp}(p, Q)(q)$ so that sequential composition becomes function composition
($\text{wp}(p_1 ; p_2, Q) = \text{wp}(p_1, \text{wp}(p_2, Q))$) and the resulting
verification conditions can be simplified by `simp`, `omega`, `grind`, or SMT
solvers.

##### Development history, lineage, and evolution

- **`Boogie` (`boogie-org/boogie@751228a2cf2c78177f9a0d040904022294aea1b2`,
  Barnett et al., FMCO 2005; Parthasarathy et al., CAV 2021, DOI
  `10.1007/978-3-030-81688-9_33`):** Passifies unstructured CFGs into acyclic
  SSA DAGs via `havoc` + `assume` statements and computes linear-size weakest
  preconditions (avoiding exponential path blowup via block-level auxiliary
  variables). Parthasarathy et al. (CAV 2021) mechanized a Rocq certificate
  checker that validates Boogie's CFG-to-DAG passification and WP generation per
  run.
- **`Why3` (`why3/why3@d0a8072e157935d0d80a7a2156ecf5a98a2aae3e`, Filliâtre &
  Paskevich, ESOP 2013):** ML-With-Regions intermediate verification platform
  using Fast WP over region-typed mutable values (`Creusot`'s original backend,
  now superseded by `Coma`).
- **`F*` and `Dijkstra Monads for All (DM4All)`
  (`FStarLang/FStar@e2b5042ffd8272ad6287e4ad8748d8e52dadd93d`, Swamy et al.,
  POPL 2016, DOI `10.1145/2837614.2837655`; Maillard et al., ICFP 2019, DOI
  `10.1145/3341708`):** Indexes a computational monad $M\,A$ by a specification
  monad $W\,A$ (a monotonic predicate transformer satisfying the Law of the
  Excluded Miracle) linked by a monad morphism $\theta : M \to W$.
- **`Lean 4 MPL` / `Std.Do` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`,
  v4.34.1, `src/Std/Do/`, Sebastian Graf et al.):** Provides `PredTrans ps α`,
  `WP m ps`, `WPMonad m ps`, and the `@[spec]`-driven `mvcgen` tactic inside
  Lean 4's standard library, automatically discharging monadic `do`-block
  verification conditions over `StateT`, `ExceptT`, and `forIn` loops.

##### Exact mapping onto Anneal's four `trusted/` primitives

As established in Section 1.2, Anneal's `Behavior Query Out := Query →
Partial (Out → Prop)` is order-isomorphic in `theory/` to a monotonic predicate
transformer `toWP(b)(Q)(q) := ∃ h : (b q).defined, ∀ o, (b q).val h o → Q o`.
In `theory/`, the **Dijkstra Monad Bridge Theorem** proves:

$$\bigl(L.\text{sem}\,p \le L.\text{SpecOn}\,\text{pre}\,\text{post} \;\wedge\; L.\text{ProductiveOn}\,\text{pre}\,p\bigr) \iff \forall q,\, \text{pre}(q) \to \text{toWP}(L.\text{sem}\,p)(\text{post}\,q)(q) \wedge \neg \text{toWP}(L.\text{sem}\,p)(\lambda \_.\,\text{False})(q)$$

Thus, `Lean 4`'s `Std.Do` / `mvcgen` tactic suite and `Boogie`-style linear-size
DAG WP generators sit entirely in `theory/` and discharge `SpecOn` +
`ProductiveOn` directly.

Basis: **source** — `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`
(`src/Std/Do/`), `boogie-org/boogie@751228a2cf2c78177f9a0d040904022294aea1b2`,
`why3/why3@d0a8072e157935d0d80a7a2156ecf5a98a2aae3e`, DM4All ICFP 2019 DOI
`10.1145/3341708`, and `Trusted/Refinement.lean`; **derived** — `toWP` bridge
theorem.

---

#### 7.2 `UC-6.2`: Characteristic formulae (`CF`) interactive verification engines (`CFML 2.0`/`SPLean`, `CakeML CF`)

##### Goals, problem domain, and target users

When verifying intricate pointer or array algorithms interactively (e.g.,
Tarjan's SCC, union-find, suffix arrays, or garbage collectors), users prefer
tactic proofs (`xapp`, `xlet`, `xif`, `xwhile`) that follow the program's AST
structure without unfolding small-step operational semantics or program
counters.

##### Development history, lineage, and evolution

- **`CFML` and `CFML 2.0` (Charguéraud, ICFP 2011; Guéneau, Jourdan,
  Charguéraud, Pottier, ESOP 2018) and `SPLean`
  (`verse-lab/splean@e24286f51bd9ee207197d47ec587d592cdfb0ddc`):** Generates a
  syntax-directed **Characteristic Formula** $\llbracket e \rrbracket_{\text{CF}} :
  \text{HProp} \to (\text{Val} \to \text{HProp}) \to \text{Prop}$ for each
  expression $e$ such that $\llbracket e \rrbracket_{\text{CF}}\,H\,Q \implies
  \{H\}\,e\,\{Q\}$. `SPLean` ports CFML's `HProp` and `x`-tactics (`XSimp`,
  `WP1`) to Lean 4.
- **`CakeML CF` (`CakeML/cakeml@f73189499bb295f0859dec7ee38c169c48da682c`,
  Guéneau, Myreen, Kumar, Norrish, ICFP 2017, DOI `10.1145/3110263`):** Replaces
  `CFML`'s external unverified OCaml formula generator with a **foundational,
  sound-by-construction characteristic formula combinator library** in HOL4,
  proved sound directly against CakeML's big-step operational semantics and I/O
  streams.

##### Exact mapping onto Anneal's four `trusted/` primitives

A characteristic formula has higher-order type `cf : Query → (Out → Prop) →
Prop`. Anneal embeds any monotonic characteristic formula `cf` into the
first-order `Behavior Query Out` in `trusted/` via the **principal-filter
(Dedekind-MacNeille) hull** in `theory/`:

```lean
def cfToBehavior (cf : Query → (Out → Prop) → Prop) : Behavior Query Out :=
  fun q =>
    { defined := cf q (fun _ => True)
      val := fun _ o => ∀ Φ : Out → Prop, cf q Φ → Φ o }
```

Proving `Abstracts L_cf L_mir idCodec cf_f f_mir` by syntax-directed induction
(matching `CakeML CF`) lets users verify Rust functions in Lean 4 using
`CFML`/`SPLean` tactics (`xlet`, `xapp`, `xif`) with zero small-step unfolding
and zero higher-order types in `trusted/lean/`.

Basis: **source** — `CakeML/cakeml@f73189499bb295f0859dec7ee38c169c48da682c`
(ICFP 2017 DOI `10.1145/3110263`),
`verse-lab/splean@e24286f51bd9ee207197d47ec587d592cdfb0ddc`, and
`Trusted/Refinement.lean`; **derived** — `cfToBehavior` principal-filter
embedding.

---

#### 7.3 `UC-6.3`: Lexicographic ranking-function and size-change termination (`SCT`) verifiers (`AProVE`/`Ultimate Automizer`, `CeTA`/`IsaFoR`, `Foetus`, `Terminator`/`RankFinder`)

##### Goals, problem domain, and target users

Total-correctness specifications for kernel routines, bootloaders, and parsers
must prove that no input can trigger an infinite loop or mutually recursive
divergence.

##### Development history, lineage, and evolution

- **`Foetus` and Size-Change Termination (`SCT`) (Abel, 1998; Lee, Jones,
  Ben-Amram, POPL 2001, DOI `10.1145/360204.360210`):** Proves termination of
  mutually recursive programs by tracking parameter decreases ($\xrightarrow{\downarrow}$,
  $\xrightarrow{\le}$) in bipartite size-change graphs $G_{f \to g}$ and checking
  that every idempotent composition $G ; G = G$ in the transitive closure
  contains a strictly decreasing thread $x \xrightarrow{\downarrow} x$.
- **`RankFinder` and `Terminator` (Podelski & Rybalchenko, VMCAI 2004, DOI
  `10.1007/978-3-540-24622-0_20`; Cook, Podelski, Rybalchenko, PLDI 2006, DOI
  `10.1145/1133981.1134029`):** `RankFinder` uses Farkas's Lemma to synthesize
  linear ranking functions completely for single-path loops; `Terminator` proves
  general transition invariants are included in a disjunctive union of
  well-founded relations $R^+ \subseteq T_1 \cup \dots \cup T_k$ by
  counterexample-guided abstraction refinement.
- **`AProVE` (Giesl et al., JAR 2017), `Ultimate Automizer`
  (`ultimate-pa/ultimate@82f536df1bea812c74d70a91d8e67c1770c3fefe`, Heizmann et
  al., CAV 2013, DOI `10.1007/978-3-642-39799-8_42`), and `CeTA`/`IsaFoR`
  (Thiemann & Sternagel, TPHOLs 2009, DOI `10.1007/978-3-642-03359-9_31`):**
  `AProVE` and `Ultimate Automizer` synthesize lexicographic ranking functions
  and Buchi automata decompositions; `CeTA` (`IsaFoR`) is an Isabelle/HOL
  verified certificate checker (`CPF`, Certification Problem Format) that
  validates termination proofs emitted by untrusted termination provers.

##### Exact mapping onto Anneal's four `trusted/` primitives

In Anneal, a certifying termination checker `checkTermination : CrateMir →
TermCert → Bool` in `theory/` (`CeTA`-style, checking either lexicographic
ranking Farkas witnesses or idempotent size-change graphs) proves
`L_mir.sem f ≤ SpecTerminatesOn pre`, where `SpecTerminatesOn` maps
`EventualOut.diverges` to `False`:

- **Critical Stress Test on `StepResult.externalCall` and Divergence:**
  In `Trusted/StepResult.lean`, `StepResult.externalCall boundaryInv branches`
  transitions in a single step $s \to s'$ (`s' ∈ branches`). If an external FFI
  callee or callback may itself **diverge** without returning, a 1-step
  `branches : State → Prop` transition to normal return states would falsely
  treat the external call as terminating in 1 step!
- Therefore, to keep total-correctness proofs (`SpecTerminatesOn`) sound across
  external calls, either (a) `L_mir.State` includes a designated diverging sink
  state `State.externalDiverged` (with a self-loop `step p .externalDiverged
  (.choice (· = .externalDiverged))`) that belongs to `branches` whenever the
  callee is not proved terminating, or (b) `VerificationResult` requires every
  callee invoked by a total-correctness function to carry its own
  `SpecTerminatesOn` obligation.

Basis: **source** — SCT POPL 2001 DOI `10.1145/360204.360210`, Terminator PLDI
2006 DOI `10.1145/1133981.1134029`, CeTA TPHOLs 2009 DOI
`10.1007/978-3-642-03359-9_31`, `ultimate-pa/ultimate@82f536df1bea812c74d70a91d8e67c1770c3fefe`,
and `Trusted/StepResult.lean`; **derived** — diverging-callee soundness
condition on `StepResult.externalCall`.

---

#### 7.4 `UC-6.4`: Modular `AdtInv` representation invariants and safe public boundaries (`Dafny`/`VCC` `pack`/`unpack`, `RustBelt` semantic soundness)

##### Goals, problem domain, and target users

Safe encapsulation of `unsafe` code is the foundational contract of Rust libraries
(`Vec<T>`, `String`, `RefCell<T>`, `zerocopy` wrappers): a module maintains a
private representation invariant `AdtInv(v, heap)` across all public safe
methods (`pub fn`), ensuring no external safe caller—even one passing malicious
re-entrant callbacks `f: impl FnMut(&T)`—can trigger UB.

##### Development history, lineage, and evolution

- **`Boogie`/`Spec#` and `VCC` Ownership Methodology (Barnett, DeLine,
  Fähndrich, Leino, Schulte, JOT 2004; Cohen et al., TPHOLs 2009, DOI
  `10.1007/978-3-642-03359-9_2`) and `Dafny`
  (`dafny-lang/dafny@5f717bf447b19d38cad1b69b1bf9a9f102feccfb`, Leino, LPAR
  2010):** Introduced a ghost boolean field `o.inv` (`closed` vs. `mutable`) on
  every object with explicit ghost statements `unpack o` (opening the invariant
  to permit field mutations) and `pack o` (proving `Inv(o)` holds and closing
  the object). Crucially, `Spec#`/`VCC` developed this methodology to defeat the
  **re-entrancy callback vulnerability**: if a method mutates `o`'s fields while
  `o` is unpacked and invokes an external method/callback that re-enters `o`,
  any method preconditioned only on `closed(o)` detects that `o` is unpacked!
- **`RustBelt` (`iris/lambda-rust@186900b2cf948835873281646ce20c7e8f084f17`,
  Jung et al., POPL 2018, DOI `10.1145/3158154`):** Formulated semantic type
  soundness for Rust ADTs where every safe `pub fn` must preserve the semantic
  interpretation $\llbracket \tau \rrbracket$ at function entry, function exit
  (normal and unwind), and across every call to an unknown closure or trait
  method.

##### Exact mapping onto Anneal's four `trusted/` primitives

`UC-6.4` exercises **all four of Anneal's `trusted/` primitives simultaneously**
and demonstrates why `StepResult.externalCall` is indispensable:

1. **Non-Vacuous Invariant (`InhabitedPre (AdtInv ty)`):** Proves that the
   module's representation invariant `AdtInv` is satisfiable (e.g., witnessed by
   `MyVec::new()`).
2. **Entry/Exit Preservation (`L_mir.SpecOn pre_AdtInv post_AdtInv` +
   `L_mir.ProductiveOn pre_AdtInv m`):** Every safe `pub fn m` assumes `AdtInv`
   on input arguments (`pre_AdtInv`) and re-establishes `AdtInv` on all
   surviving mutable borrows and return values (`post_AdtInv`).
3. **Defeating Re-Entrancy Exploits via `StepResult.externalCall`:**
   As mechanized in `anneal-structural-external-calls-and-tcb-mutation-testing-2026`
   (`naive_reentrancy_exploit_triggers_ub` vs. `canary_reentrant_callback_rejected`
   in `support/StructuralExternalCallAndCanaries.lean`), checking `AdtInv` only
   at function entry and return (`post_AdtInv`) is **unsound** when a method
   temporarily breaks `AdtInv` (corresponding to `VCC`'s `unpacked` state),
   invokes a caller-supplied closure `f(&elem)` (e.g., `Vec::retain` or
   `Vec::drain`), and plans to restore `AdtInv` after `f` returns: `f` can
   re-enter the module or panic while `AdtInv` is broken! Because
   `StepResult.externalCall (boundaryInv : Bool) (branches : State → Prop)`
   checks `boundaryInv := AdtInv(self, s.heap)` **at the exact call step to `f`**
   and immediately transitions to `.failed .ub` (`defined = False`) if
   `boundaryInv = false`, Anneal structurally forces `AdtInv` to be packed
   (`closed`) before any external callback is invoked.

Basis: **source** — VCC TPHOLs 2009 DOI `10.1007/978-3-642-03359-9_2`,
`dafny-lang/dafny@5f717bf447b19d38cad1b69b1bf9a9f102feccfb`,
`iris/lambda-rust@186900b2cf948835873281646ce20c7e8f084f17`, and
`anneal-structural-external-calls-and-tcb-mutation-testing-2026`;
**derived** — equivalence between `VCC` `pack` before callbacks and
`StepResult.externalCall` `boundaryInv`.

---

### 8. Master crosswalk across all 24 use cases (`UC-1.1`–`UC-6.4`)

| Use Case | Representative Real-World Tools | Primary `trusted/` Direction | `Query` / `Out` / `SemObs` Instantiation | Execution / Proof Mode in `theory/` | Key `trusted/` Invariant or Stress Test |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`UC-1.1`** | `Aeneas`, `Charon`, `RustHorn`, `RustHornBelt`, `Creusot`/`Coma`, `rocq-of-rust`, `Electrolysis`, `hax` | `Abstracts L_pure L_mir` + `ProductiveOn` | `L_pure.Query` = pure vals + layout; `decodeOut` checks backward/prophecy eqs | Certifying per-fn simulation / tactic | `ProductiveOn` blocks empty-prophecy miracles; partial `decodeOut` enforces framing |
| **`UC-1.2`** | `AutoCorres`/`AutoCorres2`, `Aeneas` `CCPO`/`loop` | `Abstracts L_loop L_mir` | `.diverges` mapped to `False` (total) or `True` (partial) | Constructive loop combinator + WTO cert | Fuel exhaustion in `Abstracts` must be demonic choice, never `.stuck` |
| **`UC-1.3`** | `Interaction Trees`/`Vellvm`, `FreeSpec`/`DimSum` | `Abstracts L_itree L_mir` + `externalCall` | `SemObs = EventualOut Obs Unit` aligns `ITree` `Vis` events with `L_mir` | Constructive trace handler in `theory/` | `EventualBehaviorOf` gives tau-insensitivity (`eutt`) without coinduction |
| **`UC-1.4`** | `Lean 4 bv_decide`, `SAW`/`Crucible`/`crux-mir`, `Kani`, `Rosette`/`Serval`, `HolBA`/`Islaris`/`Sail` | `L_mir.sem ≤ SpecOn` + `VerificationResult` | Symbolic path tree leaves emitted as `BitVec` obligations | Constructive `symEval` + kernel `LRAT` (`decide`) | Fine-grained per-check `Obligation` reporting in `VerificationResult` |
| **`UC-2.1`** | `Iris`/`MoSeL`, `iris-lean`, `RustBelt`, `RefinedC`/`Caesium`, `RefinedRust`, `VST` | Adequacy $\to$ `SpecOn` + `ProductiveOn` | All `CMRA`/`iProp`/step-indices erased by `iris_adequacy` in `theory/` | Constructive adequacy meta-theorem + tactics | `EventualBehaviorOf` separates finite-prefix `.failed .ub` from `.diverges` |
| **`UC-2.2`** | `CN`/`Fulminate`, `VeriFast`, `Viper`/`Prusti`, `Gillian`/`Gillian-Rust`, `Smallfoot`/`Infer`/`Pulse` | Certifying `checkSymHeapCert` $\to$ `SpecOn` | `SymHeap` interpreted over disjoint `MirState` sub-heaps | Certifying (`decide` over fold/unfold hints) | `StepResult.externalCall` `branches` must preserve unescaped caller heap frames |
| **`UC-2.3`** | `VerCors`, `Steel`/`Pulse` (F\*), fractional permissions | `Abstracts L_frac L_mir` (with `initPerm`) | `L_frac.Query := MirState`; ghost `Addr → Rat` initialized inside `sem` | Certifying rational conservation checker | `decodeQuery (encodeQuery q) = q` forbids adding ghost state to `L_v.Query` |
| **`UC-2.4`** | `GhostCell`/`qcell`, `Verus` `Tracked<PointsTo<T>>` & `PCell` | `Abstracts L_arena L_mir` + `ProductiveOn` | Erased 0-byte ZST `GhostToken<'brand>` reified as pure `ArenaMap` | Constructive API proofs + `UC-1.1` lens | Verifying erased ZST tokens and `'brand` lifetimes over `Runtime(PostCleanup)` MIR |
| **`UC-3.1`** | `Miri`, `Stacked Borrows`, `Tree Borrows`, `BorrowSanitizer` | `Abstracts L_untagged L_mir_tb` & `Compiles L_sb L_tb` | Strips `BorrowTree` shadow state after proving tag safety | Constructive for safe MIR; certifying for `unsafe` | Tree Borrows `Protector` survival across `StepResult.externalCall` |
| **`UC-3.2`** | `Polonius`, `Oxide`/`Patina`, `Aquascope` | Certifying `checkPolonius` $\to$ `VerificationResult` | Datalog Horn closure over `(Origin, Loan, Point)` | Certifying $O(|E|\cdot|O|^2)$ relation check (`decide`) | Decouples Datalog fixpoint search from fast kernel post-fixpoint checking |
| **`UC-3.3`** | `Strict/Exposed Provenance`, `VIP`, `CompCertS`/`Quasi-Concrete`, `CHERI`/`Morello` | `Abstracts L_tagged L_mir` | `TaggedPtr T k := ValidPtr T × BitVec k` packed via `map_addr` | Constructive lens + `bv_decide` | `with_exposed_provenance` cannot be demonic choice over all exposed `AllocId`s |
| **`UC-3.4`** | `MiniRust`, `Cerberus`, `CompCert Memdata` | Bilateral `Compiles` $\wedge$ `Abstracts` | Bridges `AbstractByte` arrays to structured `MirVal` via `SemObs` | Constructive bisimulation in `theory/` | `encodeOut_of_decodeOut` requires projecting out uninit struct padding at return |
| **`UC-4.1`** | `Flux`, `Liquid Haskell`, `Stainless` | Certifying `checkFluxTypes` $\to$ `VerificationResult` + `InhabitedPre` | Emits per-subtyping Horn VCs into `VerificationResult` | Certifying typechecker + `omega`/`bv_decide` | `InhabitedPre` blocks contradictory refinement preconditions (`x > 10 ∧ x < 5`) |
| **`UC-4.2`** | `embedded-hal`/`embassy`, `Verus tokenized_state_machine!` | `Abstracts L_automaton L_mir` + `externalCall` | Protocol transitions checked via `boundaryInv` and `trace : List Obs` | Certifying typestate checker in `theory/` | `StepResult.externalCall` `boundaryInv` enforces trace safety on `.diverges` loops |
| **`UC-4.3`** | `Austral`, `Vale` | `L_mir.sem ≤ SpecOn pre post_linear` | Inspects both `TerminationKind.normal` and `TerminationKind.unwind` | Certifying CFG dataflow checker | Verifies linear obligation consumption across `Runtime(PostCleanup)` unwind paths |
| **`UC-4.4`** | `no-panic`, `rtsan`/`cargo-call-stack`, `F*`/`Low*`/`KaRaMeL`, `Koka`/`Effekt` | `SpecOn` + `Abstracts L_det L_mir` + `ProductiveOn` | Singleton outcome in `L_det` + `ProductiveOn` proves determinism | Certifying call-graph & trace effect checker | Demonic `Abstracts` + `ProductiveOn` yields exact determinism for free |
| **`UC-5.1`** | `Verasco`, `Astrée`, `Crab`/`SeaHorn`, `IKOS`, `MIRAI` | Certifying `checkNumFixpoint` + Farkas witnesses $\to$ `VerificationResult` | 1-step `SmallStepMachine` inductive invariant lifts to `EventualBehaviorOf` | Certifying (`decide` over Farkas multipliers) | Generic 1-step invariant lifting from `SmallStepMachine` to `EventualBehaviorOf` |
| **`UC-5.2`** | `eBPF tnum`/`Agni`/`PREVAIL`, `LLVM KnownBits` | Certifying `checkKnownBits` $\to$ `VerificationResult` | Abstract `(known_zeros, known_ones, align)` proved sound via `bv_decide` | Constructive domain (`bv_decide`) + certifying CFG | Composing multiple analyzers on disjoint `Obligation` IDs in `VerificationResult` |
| **`UC-5.3`** | `Frama-C Eva`, `Goblint`, `Mopsa`, `Rudra`/`SafeDrop`/`Lockbud` | Certifying `checkInitEscape` $\to$ `VerificationResult` | Tracks byte-level `Init`/`Uninit` bitmaps and `StorageDead` escape sets | Certifying abstract interpreter in `theory/` | Requires byte-accurate `Uninit` and `StorageDead` semantics in `L_mir` |
| **`UC-5.4`** | `TVLA`/`Forester`, `MemCAD`/`Xisa` | Certifying DFA/shape checker $\to$ `externalCall boundaryInv` | Discharges `isValidUtf8` at `from_utf8_unchecked` boundaries | Certifying fixpoint checker in `theory/` | Unifies library-contract UB with language UB via `StepResult.externalCall` |
| **`UC-6.1`** | `F*`/`DM4All`, `Why3`, `Boogie`, `Lean 4 MPL`/`Std.Do` | `toWP` isomorphism $\leftrightarrow$ `SpecOn` + `ProductiveOn` | `Partial (Out → Prop)` $\cong$ monotonic predicate transformer | Constructive VCGen / `mvcgen` in `theory/` | Proves `ProductiveOn` is exactly Dijkstra's Law of the Excluded Miracle |
| **`UC-6.2`** | `CFML 2.0`/`SPLean`, `CakeML CF` | `Abstracts L_cf L_mir` | Principal-filter hull embeds higher-order `CF` into `Behavior` | Constructive `CF` generator + `x`-tactics | Embeds higher-order `(Out → Prop) → Prop` into first-order `trusted/` `Behavior` |
| **`UC-6.3`** | `AProVE`/`Ultimate Automizer`, `CeTA`/`IsaFoR`, `Foetus`/`SCT`, `Terminator`/`RankFinder` | `L_mir.sem ≤ SpecTerminatesOn pre` | Maps `EventualOut.diverges` to `False` via well-founded measure | Certifying (`RankCert` / `SctCert` via `decide`) | Requires `StepResult.externalCall` to model potentially diverging external callees |
| **`UC-6.4`** | `Dafny`/`VCC` (`pack`/`unpack`), `RustBelt` `AdtInv` | `SpecOn` + `ProductiveOn` + `InhabitedPre` + `externalCall` | Checks `AdtInv` at entry, exit, and `externalCall` callback boundaries | Modular deductive verification pattern | Catches re-entrancy soundness bugs (`Vec::drain` / `RefCell`) via `boundaryInv` |

### Phase-2 Long-Tail Ecosystem Additions and Primitive Mappings

Basis: documentation, derived — incorporates the Stage-2 exhaustive long-tail
tool discovery sweep (`agent_a_shard_*_tools.md`) into the package's tool
taxonomy and four-primitive `trusted/` mapping.

- **Loom, Velvet, and Veil (`verse-lab/loom`, Sergey et al. 2024-2026):** Multi-
  modal Lean 4 program verification framework using Monad Transformer Algebras
  for weakest-precondition generation over demonic/angelic nondeterminism; maps
  onto `Language.Behavior` and `ProductiveOn`.
- **Strata (`strata-org/strata`, AWS 2025-2026) and LNSym
  (`leanprover/LNSym`):** Lean 4 dialect/IR semantics and symbolic simulator
  (`sym_n` + `bv_decide`) for small-step operational models; maps onto
  `SmallStepMachine` and `Compiles`.
- **KMIR / KRust (`runtimeverification/kmir`) and CTrees (`vellvm/ctrees`, POPL
  2023):** Executable operational semantics for `rustc` MIR in K and Choice
  Trees in Rocq extending `ITree` with explicit stepping and demonic/angelic
  branching (`StepResult.externalCall`).
- **ArkLib (`Verified-zkEVM/ArkLib`), zkLean (`GaloisInc/zkLean`), and Clean
  (2024-2026):** Lean 4 verification libraries targeted by
  `Charon`/`Aeneas`/`hax` functional extraction pipelines.
- **Corten / CortenMM (Gaher et al. 2024-2025), Diaframe (`iris/diaframe`),
  Lithium (`iris/refinedc`), and Katamaran (`katamaran-project/katamaran`):**
  Foundational Rocq/Iris separation-logic and symbolic-heap frame-inference
  engines automating bi-abduction and contract checking.
- **`a-mir-formality` (`rust-lang/a-mir-formality`) and Flowistry
  (`willcrichton/flowistry`, OOPSLA 2022):** Authoritative executable
  specification of Rust's trait/Polonius borrow checker and MIR information-flow
  analyzer.
- **Vostd (`asterinas/vostd`), Atmosphere, VeriSMo, Anvil (OSDI/SOSP 2024-2025),
  and `klint` (`Darksonn/klint`):** Verified Rust OS kernels/controllers using
  Verus tokenized state machines and `rustc` atomic-context preemption tracking
  (`Partial.ub` on sleeping while atomic).
- **Pagai, Clam (`seahorn/clam`), Apron, ELINA (`eth-sri/elina`), and LiSA
  (`lisa-analyzer/lisa`):** Numerical (`Polyhedra`/`Zonotope`) and FSA string
  abstract-interpretation domains (`Abstracts`).
- **Lean 4 `Std.Do` / `mvcgen` (`sgraf812/mpl`, 2024-2026), Gospel/Cameleer
  (`ocaml-gospel/cameleer`), and Lean 4 `guessLex`:** Monadic weakest-
  precondition VCGens and size-change lexicographic termination synthesizers.

## Boundaries

- **Known not to apply (Ghost state in `Abstracts` `Query`):** Because
  `BehaviorCodec` requires `decodeQuery (encodeQuery q₁) = q₁`, an upward
  abstraction `Abstracts L_v L_mir codec v s` cannot define `L_v.Query :=
  MirState × GhostState` with `L_mir.Query := MirState` unless `GhostState` is a
  deterministic function of `MirState`. Any non-deterministic ghost state must
  be quantified inside `L_v.sem` or formulated horizontally via `Compiles L_mir L_ghost`.
- **Known not to apply (Many-to-one `decodeOut` over unprojected padding):**
  Because `BehaviorCodec` requires `decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`,
  a codec cannot map multiple concrete memory states differing in uninitialized
  struct padding bytes to the same `some o₁` unless `L_mir.Out` projects out
  unobservable padding at function return or `L_v.Out` retains the padding bits
  and erases them in `L_v.obs`.
- **Known not to apply (Demonic `with_exposed_provenance`):** Modeling
  `ptr::with_exposed_provenance(addr)` in `L_mir` as a `StepResult.choice` over
  all previously exposed `AllocId`s is unsound under demonic refinement (`≤`)
  whenever two or more allocations have been exposed.
- **Known not to apply (Fuel exhaustion as `.stuck` in `Abstracts`):** Mapping
  fuel exhaustion in an abstract loop evaluator `L_loop` to `.stuck` or `.failed`
  (`defined = False`) invalidates `Abstracts L_loop L_mir` whenever the concrete
  program runs beyond the fuel bound.
- **Not examined (Full `theory/` implementations of all 24 engines):** While the
  core refinement primitives (`Trusted/Refinement.lean`,
  `Trusted/StepResult.lean`) and representative Lean 4 probes (`Aeneas`/Lithium
  in `rust-verification-aeneas-lithium-tracked-funclang-and-loops-2026`, `bv_decide`
  and `Std.Do` in `lean4-core-tactics-kernel-bvdecide-stddo-and-containers-2026`,
  Tree Borrows in `anllvm-verified-llvm-lowering-tree-borrows-noalias-and-binary-tv-2026`,
  and `StepResult.externalCall` re-entrancy in
  `anneal-structural-external-calls-and-tcb-mutation-testing-2026`) have been
  mechanized, full production certificate checkers in `theory/` for `Polonius`
  (`UC-3.2`), `Flux` (`UC-4.1`), `Verasco` Farkas polyhedra (`UC-5.1`), and
  `CeTA` size-change termination (`UC-6.3`) remain future engineering work.
- **Unsupported (`native_decide` in Anneal's TCB):** Tools that rely on
  unverified native code execution in Lean (`Lean.ofReduceBool` via
  `native_decide`) are rejected by Anneal's `.olean` auditor; all reflective
  checkers (`bv_decide` `LRAT`, `checkSymHeapCert`, `checkPolonius`,
  `checkNumFixpoint`) must reduce inside the Lean kernel (`decide`).

## Evidence

1. **Anneal `trusted/lean/` Refinement and Small-Step Foundations (`source`):**
   - Repository: `joshlf/anneal`, workspace revision
     `24367bd1a8c784f2578535954f9915e24894a56f` and `.agent-worktrees/trusted-core`
     revision `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`.
   - `trusted/lean/Trusted/Refinement.lean:207-473`: `Preorder`, `Partial`,
     `Partial.pure`, `Partial.ub`, `instPreorderPartial`, `Monotone`, `Behavior`,
     `Language`, `Language.SpecOn`, `Language.WellFormedOn`, `Compiles`,
     `Abstracts`, `Compiler`, `VerificationResultOn`.
   - `trusted/lean/Trusted/StepResult.lean:58-200`: `TerminationKind`,
     `StepResult`, `PrefixOutcome`, `ReachesPrefix`, `BehaviorOf`,
     `SmallStepMachine.toLanguage`.
   - Cross-referenced corpus packages (`source` + `execution`):
     `anneal-partial-compile-and-conditioning-refinement-algebra-2026`,
     `anneal-polar-ctfe-admission-and-semantic-polarity-2026`,
     `anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026`,
     and `anneal-structural-external-calls-and-tcb-mutation-testing-2026`
     (mechanizing `Language SemObs`, `BehaviorCodec`, `ProductiveOn`,
     `InhabitedPre`, positive `VerificationResult`, `EventualBehaviorOf`, and
     `StepResult.externalCall`).

2. **Category A — Functional Translators and Symbolic Evaluators (`source` + `documentation`):**
   - `Aeneas` (`AeneasVerif/aeneas@70683bd4ab876179a23e5f994d02947b3e5c4f0d`,
     `backends/lean/Aeneas/Std/Primitives.lean`, `Std/WP.lean`, `Tactic/Step/`,
     ICFP 2022 DOI `10.1145/3547647`, ICFP 2024 DOI `10.1145/3674640`) and
     `Charon` (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`,
     v0.1.210).
   - `RustHorn` (TOPLAS 2021 DOI `10.1145/3462205`) and `RustHornBelt` (PLDI 2022
     DOI `10.1145/3519939.3523704`, Zenodo `6417462`).
   - `Creusot` (`creusot-rs/creusot@c4e9770ac1371ac4274bfe02145266d315c2fb86`,
     `creusot/src/backend/place.rs`) and `Coma` (ESOP 2025, sha256
     `a52ad7b745fb8a1d0b54bf52b54f0cfaec18e59f587eda551a54702cf61a8d8e`).
   - `coq-of-rust` / `rocq-of-rust`
     (`formal-land/rocq-of-rust@ca1374ae2fdeb28b069fe77ba412db5604525261`),
     `Electrolysis` (`Kha/electrolysis`, blob
     `670746012e99efc7b239bc5cd41f9ee2d967997b`), and `hax`
     (`cryspen/hax@1ec88cdb2c8e546845e64eb2cd2321b4f58069c4`,
     `Hax/Tactic/HaxMvcgen.lean`).
   - `AutoCorres` (PLDI 2014 DOI `10.1145/2594291.2594296`), `Interaction Trees`
     (`DeepSpec/InteractionTrees@a2bc2c38ad998dccadb932559c922139dd957c4f`, POPL
     2020 DOI `10.1145/3371119`), `Vellvm`
     (`vellvm/vellvm@506f1eb0be542611521985719b971fbce8498dc9`), and `DimSum`
     (POPL 2023 DOI `10.1145/3571220`).
   - `Lean 4 bv_decide` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`,
     `src/Lean/Elab/Tactic/BVDecide/`), `SAW`
     (`GaloisInc/saw-script@27a7ae98256544b55a7a3ce4ce620c1a7889713b`),
     `Crucible` / `crux-mir`
     (`GaloisInc/crucible@7f49dac06c656f7b92c8b6cc054f47c63b60abe4`), `Kani`
     (`model-checking/kani@9461e07af7ec929f050aa4192f29363c9be07779`),
     `Rosette` (`emina/rosette@373c8c35e4a7667f38fce10cf0b74ae17de07f1d`, PLDI
     2014 DOI `10.1145/2594291.2594340`), `Serval`
     (`uw-unsat/serval@72adc4952a1e62330aea527214a26bd0c09cbd05`, SOSP 2019 DOI
     `10.1145/3341301.3359641`), `Sail`
     (`rems-project/sail@0f51056900af85d0b18928d6ea2d2271d18184e8`), `Islaris`
     (`rems-project/islaris@c978e10f50db5c40f0fdf113f5f76a779782c6f9`, PLDI 2022
     DOI `10.1145/3519939.3523434`), and `HolBA`
     (`kth-step/HolBA@ef22c1fd8da612c57f2e7f273cb14594a7e529d3`).

3. **Category B — Separation Logics and Spatial Resource Engines (`source` + `documentation`):**
   - `Iris` (`rocq-iris/iris@8e4909593a3a84f850d224a344cbd3a380672088`, JFP
     2018 DOI `10.1017/S0956796818000151`), `MoSeL` (ICFP 2018 DOI
     `10.1145/3236772`), and `iris-lean`
     (`leanprover-community/iris-lean@81bc35088ba67d465db008f5261a9b341eb6cf6c`).
   - `RustBelt` (`iris/lambda-rust@186900b2cf948835873281646ce20c7e8f084f17`,
     POPL 2018 DOI `10.1145/3158154`, POPL 2020 DOI `10.1145/3371102`),
     `RefinedC` (`iris/refinedc@d057583986651a28047164581f05fbee3a83ed9d`, PLDI
     2021 DOI `10.1145/3453483.3454036`), `RefinedRust`
     (`lgaeher/refinedrust-dev@8a07f4f2e6a499625b4b25e94f0b2ab78592cb52`, PLDI
     2024 DOI `10.1145/3656423`), and `VST`
     (`PrincetonUniversity/VST@3c37c2e2b574e23aee8fdd1684aa0ffed227491e`).
   - `CN` and `Fulminate`
     (`rems-project/cerberus@c8c085d4714ae17095b2e1202fa33c5545d98df1`, POPL 2023
     DOI `10.1145/3571194`, POPL 2025 DOI `10.1145/3704879`), `VeriFast`
     (`verifast/verifast@0a83dba42db7ce0b445034ece5298afe980e57dc`,
     `arXiv:2601.13727v1`), `Viper`
     (`viperproject/silver@da1c8993b66feb39976e3609e2580a4661137a0f`), `Prusti`
     (`prusti/prusti@0d4a8d497ac1e540d48ef50a031d53b4e3ae36e2`, OOPSLA 2019 DOI
     `10.1145/3360573`), `Gillian-Rust`
     (`GillianPlatform/gillian-rust@83d739e83034d71162fb66b569041cf301123df7`,
     PLDI 2025 DOI `10.1145/3729289`), `Infer`/`Pulse`
     (`facebook/infer@5aac32c06952a2f3a6b7043e91457920f065833b`), `VerCors`
     (`utwente-fmt/vercors@3300d5b007286225a33c17a233bda77db9471213`),
     `Steel`/`Pulse` (`FStarLang/FStar@e2b5042ffd8272ad6287e4ad8748d8e52dadd93d`),
     `GhostCell` (ICFP 2021 DOI `10.1145/3473597`), and `Verus`
     (`verus-lang/verus@0141ebc6f14410dfc87fef1da57408578002eb7c`, OOPSLA 2023
     DOI `10.1145/3586037`).

4. **Category C — Aliasing and Borrow Models (`source` + `normative` + `documentation`):**
   - `Miri` (`rust-lang/miri@0e1a23b0794bec7860df8c06a774f4316746795a`),
     `Stacked Borrows` (POPL 2020 DOI `10.1145/3371109`), `Tree Borrows` (PLDI
     2025 DOI `10.1145/3735592`), `BorrowSanitizer`
     (`BorrowSanitizer/bsan@a2fd46ab89fc97ba1cf548645dd70acbeaa17d64`),
     `Polonius` (`rust-lang/polonius@bfd4c945b7713d0e66a3cde80475d9a4494740df`),
     `Oxide` (`arXiv:1903.00982v4`), `Aquascope`
     (`cognitive-engineering-lab/aquascope@f2d0a06034b86765a91f10b7c8e40ec31ecb87a6`),
     `VIP` (PLDI 2022 DOI `10.1145/3519939.3523702`), `Quasi-Concrete` (POPL 2015
     DOI `10.1145/2676726.2676985`), `CHERI`/`Morello`
     (`CTSRD-CHERI/sail-morello@2305f656ff84619caf50107f49dae7be52aec72b`),
     `MiniRust` (`minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`),
     and `CompCert Memdata`
     (`AbsInt/CompCert@f9573fb9b8ba4b4cecebe1ef3cb8b2ef9ce1fc03`).

5. **Categories D, E, and F — Type Systems, Abstract Interpreters, and VCGens (`source` + `documentation`):**
   - `Flux` (`flux-rs/flux@6769bb9cbd1216380f542349494efafafd6104a3`, PLDI 2023
     DOI `10.1145/3591283`), `Liquid Haskell`
     (`ucsd-progsys/liquidhaskell@c0cca0b9f92d8cdaae7f8fc604f78c32b534b69d`,
     ICFP 2014 DOI `10.1145/2628136.2628161`), `Stainless`
     (`EPFL-LARA/stainless@399c34a06df8e88679f0985131e8a59a28ab9b3f`),
     `embedded-hal` (`rust-embedded/embedded-hal@41f29f6bfced1cae0cbe712ba96ee32c075b3125`),
     `embassy` (`embassy-rs/embassy@14cf6a68ec0bfd0ecf873f7e3dbb2eb69013fa29`),
     `Austral` (`austral/austral@0962d2a8a5d77f7daacd7f696819520733f4897d`),
     `Vale` (`project-everest/vale@bbae0eb89143734363b14a77642dbf8dec36e288`),
     `no-panic` (`dtolnay/no-panic@9a0b1097f77dfd5ee4352b6ff060f68d791730f7`),
     `KaRaMeL` (`FStarLang/karamel@9abbb865b10a0cd5c557da81c024c3965cb6ff53`),
     `Koka` (`koka-lang/koka@d23ee7cd73737c1da7a7a5fa837a2806facc3d6b`), and
     `Effekt` (`effekt-lang/effekt@91c540b1067721bdd1bb5d463e42827f8316a1da`).
   - `Verasco` (POPL 2015 DOI `10.1145/2676726.2676966`), `Astrée` (ESOP 2005 DOI
     `10.1007/978-3-540-31987-0_3`), `Crab`
     (`seahorn/crab@b1eeb1a9402ab0664e962f26f89d923f8514284c`), `SeaHorn`
     (`seahorn/seahorn@892780176731ec8e97bbb9f6b172fcacd77a8ff4`), `IKOS`
     (`NASA-SW-VnV/ikos@ac7f7c1738976cabc58c6a53413df6e458995c38`), `MIRAI`
     (`endorlabs/MIRAI@aae0a56f91d9a0a62073bb86e7b2c9793cefc24b`), `Agni` (CAV
     2023 DOI `10.1007/978-3-031-37709-9_12`), `PREVAIL`
     (`vbpf/prevail@cefe6a799f8b8f37aa2560e196f223802717c1e7`, PLDI 2019 DOI
     `10.1145/3314221.3314590`), `LLVM KnownBits`
     (`llvm/llvm-project@3623fe661ae35c6c80ac221f14d85be76aa870f1`), `Frama-C Eva`
     (`git.frama-c.com/pub/frama-c@ce0648c726122d4a7b5e8614a1a5b97777d9d226`),
     `Goblint` (`goblint/analyzer@1463f411ce87edd49198033856b2946fc3366fb2`),
     `Mopsa` (`mopsa/mopsa-analyzer@f168a9c025738d4940cfb6a281dde258c871da73`),
     `Rudra` (`sslab-gatech/Rudra@fc9add2c4721c77490680462c7f0ad791af7cec7`, SOSP
     2021 DOI `10.1145/3477132.3483570`), `Lockbud`
     (`BurtonQin/lockbud@a1b5303cdbb1d4d0ad886359cc71418570e7c5fd`), `TVLA`
     (TOPLAS 2002 DOI `10.1145/514188.514190`), and `MemCAD`
     (`Antique-team/memcad@d95caa514f2b66b8c43c015799084d281944f028`, POPL 2008
     DOI `10.1145/1328438.1328469`).
   - `DM4All` (ICFP 2019 DOI `10.1145/3341708`), `Why3`
     (`why3/why3@d0a8072e157935d0d80a7a2156ecf5a98a2aae3e`), `Boogie`
     (`boogie-org/boogie@751228a2cf2c78177f9a0d040904022294aea1b2`, CAV 2021 DOI
     `10.1007/978-3-030-81688-9_33`), `SPLean`
     (`verse-lab/splean@e24286f51bd9ee207197d47ec587d592cdfb0ddc`), `CakeML CF`
     (`CakeML/cakeml@f73189499bb295f0859dec7ee38c169c48da682c`, ICFP 2017 DOI
     `10.1145/3110263`), `Ultimate Automizer`
     (`ultimate-pa/ultimate@82f536df1bea812c74d70a91d8e67c1770c3fefe`, CAV 2013
     DOI `10.1007/978-3-642-39799-8_42`), `CeTA` (TPHOLs 2009 DOI
     `10.1007/978-3-642-03359-9_31`), `SCT` (POPL 2001 DOI
     `10.1145/360204.360210`), `Terminator` (PLDI 2006 DOI
     `10.1145/1133981.1134029`), `Dafny`
     (`dafny-lang/dafny@5f717bf447b19d38cad1b69b1bf9a9f102feccfb`), and `VCC`
     (TPHOLs 2009 DOI `10.1007/978-3-642-03359-9_2`).

## Revalidation

To revalidate the architectural mappings in this report when `trusted/lean/`
evolves:

1. **Check the four `trusted/lean/` primitives:** Diff `Trusted/Refinement.lean`
   and `Trusted/StepResult.lean` against the four-primitive equations in
   Section 1:
   - Verify `BehaviorCodec` retains `decodeQuery_encodeQuery`,
     `decodeOut_encodeOut`, `encodeOut_of_decodeOut`, and `obs_decodeOut`.
   - Verify `Language.ProductiveOn` requires both `(L.sem prog q).defined` and
     `∃ o, (L.sem prog q).val h o`, paired with `InhabitedPre pre`.
   - Verify `VerificationResult` uses positive disjunction
     `ob.id ∈ waived ∨ ob.prop` without antecedent implication `→`.
   - Verify `EventualBehaviorOf` defines `defined` via finite-prefix safety and
     places `.diverges` inside `EventualOut`, and that
     `StepResult.externalCall boundaryInv branches` steps to `.failed .ub` when
     `boundaryInv = false`.
2. **Discriminating probes for each category (`UC-1.1`–`UC-6.4`):**
   - For functional translators (`UC-1.1`), test an unsatisfiable prophecy
     equation and confirm `ProductiveOn` rejects it.
   - For `BehaviorCodec` (`UC-2.3`, `UC-3.4`), confirm `encodeOut_of_decodeOut`
     rejects non-injective `decodeOut` over unprojected padding bytes.
   - For `StepResult.externalCall` (`UC-4.2`, `UC-6.3`, `UC-6.4`), run the
     re-entrant callback canary (`canary_reentrant_callback_rejected` in
     `anneal-structural-external-calls-and-tcb-mutation-testing-2026`) and
     verify that breaking `AdtInv` before an external call falsifies `defined`.
