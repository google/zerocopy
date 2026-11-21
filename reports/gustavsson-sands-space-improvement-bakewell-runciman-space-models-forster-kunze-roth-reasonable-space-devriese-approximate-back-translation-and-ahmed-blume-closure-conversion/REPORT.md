# Space-sensitive equivalence and back-translation under resource bounds: call-by-need space improvement, cost-model invariance, step-indexed and approximate back-translation, and why a fixed observable budget defeats preservation

## Summary

- **A fixed, observable resource bound turns the target's space overhead into something a context can observe.** If target contexts can hold `k` units live around the hole, then two components whose peak target demands differ are distinguished at some budget.
  - Example: a context that pre-allocates `B − peak(P)` units lets `P` complete and makes `Q` exhaust.
  - A translation therefore preserves fixed-budget contextual equivalence only if source-equivalent components always have equal target peak demand in every context.
  - When the source charges less than the target, so that the overhead depends on program structure rather than on source-observable behaviour, preservation is *false*, not merely unproved. No back-translation can repair it, because the distinguishing target context exists while no source context distinguishes the components.
  - (Basis: derived, with proof sketch below; confirmed on bounded instances by a toy model that is not any published system: 142 of the source-equivalent pairs in a 58-program toy language are separated by target contexts when the source charges 0 for a construct the target charges 1; 0 are separated when both charge 1.)
- **Published back-translation techniques absorb step mismatch only because steps are not observable.**
  - Ahmed–Blume's step-indexed relations and Devriese–Patrignani–Piessens' approximate back-translation index only one side's steps in each half of the relation. Their observation is termination alone.
  - Devriese et al.'s relations decrease the index by `min(i, j)` when the two sides take `i` and `j` steps (technical appendix, Lemma 4). The budget `n` is chosen *after* observing the target run.
  - Neither work states a constant-factor bound between source and target step counts.
  - If fuel or space exhaustion were an observable outcome, the emulation overhead of the back-translated context would itself become observable. (Basis: documentation of the papers + derived.)
- **Call-by-need space improvement measures what a bounded heap would observe, only up to a constant factor, and the authors do not claim it carries over to real implementations.** Gustavsson–Sands (HOOTS 1999 draft):
  - *Weak* space improvement allows a context-independent linear blow-up. That slack is what makes it a precongruence: linear functions compose.
  - *Strong* improvement (`C[M]⇓_{h,s} ⇒ C[N]⇓_{h,s}` for every context, heap and stack measured separately, garbage collection chosen optimally at every step) is exactly refinement of "completes within budget `(h,s)`", but it is used only as a proof vehicle.
  - Any transformation that adds a free variable is never a weak space improvement (Thm 5.2), and `x+y → y+x` and used-once inlining are not space-safe.
  - The authors state there is "no hope" of a space theory that applies to all implementations.
  - Moran–Sands time improvement and the Hackett–Hutton line are time-only. (Basis: documentation, read as preprint and draft versions.)
- **Cost-model invariance results are whole-program and asymptotic, so they do not fix exhaustion points.**
  - Forster–Kunze–Roth (POPL 2020): weak call-by-value λ with β-step time and maximum-term-size space simulates Turing machines, and is simulated by them, with polynomial time and *constant-factor* space overhead. This holds for decision functions, closed terms, and `T, S ∈ Ω(n)`.
  - Only the abstract-machine lemmas are mechanised in their Coq repository. The constants match the paper exactly: 3k+1 steps and `m ≤ m′ ≤ 2m` for the substitution machine (`AbstractSubstMachine.v:62–64`, `:169–171`); 4k+2 steps and size `≤ (i+1)(3i+4‖s‖)` for the heap machine (`AbstractHeapMachine.v:252–256`, `:438–439`). The Turing-machine parts are paper-only.
  - Accattoli–Dal Lago–Vanoni (LICS 2022 / LMCS 2024) obtain logarithmic-space reasonableness with a specific machine (Space KAM: eager naive GC, flat environments). They show natural β-time is not reasonable for it: an `Ω(2^n)` blow-up.
  - (Basis: documentation + source.)
- **No security paper examined lets a target context observe stack or heap exhaustion and then proves a weakened full-abstraction criterion.**
  - Exhaustion is assumed away in several papers: infinite memory (Juglaret et al. CSF 2016; Abate et al. CCS 2018), infinite address space (StkTokens), or "no overflow" as a premise of the back-translation theorem (Patrignani et al. TOPLAS 2015, Thm 5.9).
  - It is named as an out-of-model side channel by Fournet et al. (POPL 2013).
  - Juglaret et al. say handling it "will require slightly weakening the security property".
  - Exhaustion appears as a theorem-level outcome only in compiler *correctness* work, where it is one-sided: CakeML's `extend_with_resource_limit`, and Carbonneaux et al.'s finite-stack refinement. (Basis: documentation + source.)

## Applicability

- **What this report covers.** Published theories and proofs about equivalence, improvement, and compilation when a resource is metered: Moran–Sands; Gustavsson–Sands; Sands–Gustavsson–Moran; Hackett–Hutton; Forster–Kunze–Roth and its Coq artifact; Accattoli–Dal Lago–Vanoni; Abadi; Ahmed–Blume; Devriese–Patrignani–Piessens (POPL 2016 and the technical appendix of the LMCS 2017 version); the Patrignani–Ahmed–Clarke survey; Paraskevopoulou–Appel; and the secure-compilation papers listed in Evidence. The question throughout is what transfers when **exhausting a bounded resource is itself an observable outcome**.
- **How the subjects relate.**
  - The literature subjects are *read and compared*. None was re-executed.
  - The Coq repository `uds-psl/cbv-lambda-calculus-reasonable` at `4f12b7c8ce2816cdd771d22d04943e0fa81c63fd` was inspected and its lemma statements quoted. It was **not built**.
  - CakeML (`CakeML/cakeml` at `2874b664e10939a3ee462215b2e068c89c1f70eb`) is cited only for the exact definition of its resource-limit escape.
  - The author-hosted repository `squera/squera.github.io` at `ec5c7909a6b5245aabf9c1caabb79b0b7b07d543` is cited for two author documents: the technical appendix of the LMCS version of Devriese et al., and the pre-publication full version of the survey with appendices.
- **Versions read.** Several papers were read as author preprints, extended versions, technical reports, or drafts, so page and theorem numbers may differ from the published versions. These are: Moran–Sands extended version; Gustavsson–Sands HOOTS draft of 2 July 1999; Abadi as SRC Research Report 154; Devriese et al. POPL author version; TOPLAS 2015 author preprint; CakeML JFP preprint. Each is named in Evidence. Formulas whose glyphs were lost in PDF text extraction are marked *reconstructed*.
- **Toy model.** The derived argument in Findings §5 is a general claim. The toy model in `support/` checks it exhaustively only within stated size and budget bounds, on a five-construct language written for this report.
  - It is **not** a model of any published calculus, compiler, or runtime.
  - Its verdicts are bounded-search results: "distinguished" verdicts have concrete witnesses; "equivalent" verdicts are bounded only.
- **Out of scope.** Time-only side channels, except as an analogy for fuel; amortised resource analyses; heap-space separation logics.

## Findings

### 1. Improvement theories: what is measured, what composes, and what is shown unsafe

Basis: documentation. Moran–Sands was read in its extended version. Gustavsson–Sands HOOTS 1999 was read as the 2 July 1999 draft. Gustavsson–Sands ICFP 2001 and Hackett–Hutton 2014 and 2018 were read at abstract strength only. Hackett–Hutton 2019 was read in its published layout.

| Theory | Resource | Unit and GC model | Relation | Compositional? | Stated limits |
|---|---|---|---|---|---|
| Moran–Sands 1999, time improvement | time | every Sestoft mark-1 machine transition ("Our unit of cost is the abstract machine reduction step"); no space | `M ⊵ N` iff ∀C. `C[M]⇓ⁿ ⇒ C[N]⇓^{≤n}`; cost equivalence when it holds both ways; improvement within a constant factor `⊵≈` (Def. 4.1, reconstructed) | yes: contextual by definition; `⊵≈` "is a precongruence" with a constant "independent of the context of use" | (β-expand) is an unproved conjecture, so general let-floating and CSE are conditional; the call-by-need calculus "cannot improve (or worsen) a program by more than a constant factor" (Cor. 4.4) |
| Gustavsson–Sands 1999, weak space improvement | heap and stack, measured separately | heap = number of bindings plus update markers; stack = number of stack elements; GC = "removal of any number of bindings and update markers … providing that the configuration remains closed", existentially chosen at every step; space = peak over the run | `M ⊵ N` iff ∃ linear `f` ∀C. `C[M]⇓_{h,s} ⇒ C[N]⇓_{f(h,s)}` (Def. 5.1, reconstructed) | yes: Prop. 5.1 precongruence, "the composition of any two linear functions is linear" | Thm 5.2: `M ⊵ N ⇒ FV(N) ⊆ FV(M)`; not a recursively enumerable relation; "no hope" of a theory covering all implementations |
| Gustavsson–Sands 1999, strong space improvement | same | same | `M ⊵ₛ N` iff ∀C. `C[M]⇓_{h,s} ⇒ C[N]⇓_{h,s}` (Def. 6.1, reconstructed) | closed under contexts by definition (an inference; the draft does not state it) | used "merely as a vehicle"; its context lemma needs `FV(M) ⊇ FV(N)`; the ICFP 2001 abstract adds a fixed-point induction theorem for strong improvement and calls the asymptotic relation "semantically badly behaved" |
| Hackett–Hutton 2014, 2018, 2019 | time | Moran–Sands-style ticks or derivation size | worker/wrapper and fusion as time improvements | as Moran–Sands | 2019 §9: the clairvoyance technique does not apply to space, because "it doesn't matter when we evaluate subterms, and this assumption is no longer valid for space" |

- **Transformations shown not space-safe** (Gustavsson–Sands draft):
  - `x+y → y+x`: Θ(n) space against constant space, so "there is no constant which bounds the potential worsening in space when this law is applied in an arbitrary context";
  - general inlining of a non-value into a non-reduction context;
  - inlining a binding that is used at most once: "work-safe but not space safe … the left hand side can run in constant space but the right hand side requires heap space proportional to k".
- **Shown space-safe:** value-β; floating out of shallow reduction contexts; `let {x = M} in x ≅ M`; garbage collection of bindings; let-flattening; and inlining of *affine-linear* bindings evaluated without update markers (Thm 7.2), which is a strong time and space improvement.
- **Space "ticks".** Strong-improvement proofs use stack and heap "spikes" and "ballast" annotations. Ballast is suspected not to be a conservative extension.
- **Derived reading.**
  - Strong space improvement is precisely refinement of the observation "completes within budget `(h,s)`" at every budget, with garbage collection chosen optimally at every step. It is therefore the natural source-level relation for a language in which exhaustion is observable.
  - Weak improvement deliberately forgets constant factors. Under a fixed observable budget those factors are observable (§5), so weak space improvement does **not** imply budget-observational refinement.
  - Separately, a transformation that captures an extra variable in a closure environment cannot be a weak improvement in the same language (Thm 5.2). The theorem is stated for one language; applying it across a representation change is not established.

### 2. Space semantics of evaluators and of the CPS transformation

Basis: documentation, at partial strength.

- **Bakewell–Runciman, PPDP 2000.** Neither the full text nor an abstract was obtained, so nothing about its relation is established here.
  - Their companion "A Space Semantics for Core Haskell" (preprint, ENTCS 41(1)) defines space as peak graph cardinality, `space(G) = max{#G′ | G →* G′}`, "intended for asymptotic analysis".
  - It says compliance of an implementation "really require[s] a proof showing that its abstract machine has the same asymptotic space behaviour as the semantics", reporting "some progress in comparing term-graph evaluators" (the PPDP paper).
- **Minamide, HOOTS 1999** (abstract only). The abstract claims the CPS transformation "preserves space required for execution of a program within a constant factor". The space-profiling semantics revises Blelloch–Greiner's NESL profiling semantics, which had "some inconsistency between the treatments of stack space and heap space".
  - Paraskevopoulou–Appel (2019, §1 and §10) describe the proof as a forward simulation on the maximum *reachable* heap.
  - Whether the constant is purely multiplicative or includes an additive term is **unknown** here.
- **Paraskevopoulou–Appel, ICFP 2019** (published layout). Closure conversion in CertiCoq is safe for space. Corollary 8.2 bounds time by `c₁ ≤ c₂ ≤ 7·c₁` and space by `m₂ ≤ m₁ + cost^space_exp(e) + 1`. Corollary 8.3 gives the same space bound for diverging programs.
  - The source measure is the maximum reachable heap.
  - The target measure is the actual heap with a collector run at every function entry.
  - Their Theorem 5.1, a semispace collector running in memory `4A`, is **not** proved in Coq.
  - Composition "applies only to whole-program compilation".
- **Derived reading.**
  - In this literature the only space relationships proved between a source and a transformed program are multiplicative constants (Minamide, by the abstract) or additive program-size-dependent shifts (Paraskevopoulou–Appel). They are whole-program statements.
  - An additive shift `m₂ ≤ m₁ + c(e)` is the shape needed for a one-sided budget statement: "if the source completes within `B`, the target completes within `B + c(e)`".
  - It does not make source-equivalent components target-equivalent at a fixed budget, because `c(e)` depends on the program.

### 3. Cost-model invariance: what the theorems and their mechanisation actually state

Basis: documentation (Forster–Kunze–Roth published version; Accattoli–Dal Lago–Vanoni LICS and LMCS versions) + source (`uds-psl/cbv-lambda-calculus-reasonable` at `4f12b7c8ce2816cdd771d22d04943e0fa81c63fd`).

- **Forster–Kunze–Roth measures** (Def. 1.1).
  - Time `‖s‖_T` = number of β-steps.
  - Space `‖s‖_S` = maximum size of a term over the reduction, using de Bruijn indices of *unary* size: `‖n‖ = 1+n`, `‖λs‖ = 1+‖s‖`, `‖st‖ = 1+‖s‖+‖t‖`.
  - The input counts toward space, so "our result does not cover sublinear time or space".
- **Theorem 1.2 (L is reasonable).** For `f : Σ* → {true,false}` and `T, S ∈ Ω(n)`, L-computability in time `T` and space `S` and Turing-machine computability in time `O(poly(T))` and space `O(S)` are inter-simulable in both directions.
  - L→TM (Thm 4.3) interleaves a substitution machine with a heap machine and switches when term size could accommodate pointer explosion. It relies on Lemma 4.1, `log ‖s‖_T ∈ O(‖s‖_S)`.
  - TM→L (Thm 5.1) is linear in time and space, "easily verified by checking all intermediate terms" of Dal Lago–Accattoli 2017.
- **Mechanised versus paper-only.**
  - The repository description reads "The formalized part of the POPL 2020 Paper …". The paper says it mechanises "all results for the abstract machines in Section 3".
  - Verbatim statements at the pinned revision:
    ```text
    AbstractSubstMachine.v:62-64   Lemma correctTime s t k: timeBS k s t -> exists p, reprP p t /\ pow step (3*k+1) (init s) ([],[p]).
    AbstractSubstMachine.v:169-171 Lemma correctSpace s t m: spaceBS m s t -> exists m' P, reprP P t /\ redWithMaxSizeS m' (init s) ([],[P]) /\ m <= m' <= 2*m.
    AbstractHeapMachine.v:252-256  Lemma correctTime s t k: timeBS k s t -> closed s -> exists g H, reprC H g t /\ pow step (4*k+2) (init s) ([],[g],H).
    AbstractHeapMachine.v:438-439  Lemma correctSpace: sizeSt (T,V,H) <= (i + 1) * (3*i+4*size s).
    ```
  - Space is the maximum state size along a run (`ARS.v:104–108`, `redWithMaxSize`, where `m = max (size s) m'`).
  - The heap machine's size measure counts a closure's address by its numeric value: `sizeC (P!a) = sizeP P + a`. Its bound is polynomial in the step count `i`, so it is a time-dependent bound, not a bound in L-space. That is why the paper needs the interleaving.
  - No Turing-machine definition, interleaving, or invariance statement exists in the repository; `grep -i 'turing|polynom|invarian|log'` hits only a comment.
  - **Discrepancy.** The paper's Lemma B.7 prints `‖P‖ ≤ ‖s‖`, while the Coq `size_clos` (`AbstractHeapMachine.v:308–309`) proves `sizeP P <= 2*size s`. The cause is not resolved.
- **Accattoli–Dal Lago–Vanoni.**
  - Space is the *work* space of the Space KAM: the maximum number of closures, each weighted by its sub-term pointer size. Eager GC is implemented "naively and repeatedly checking whether variables occur, and not via pointers or counters". Environments are flat, and the input is not counted.
  - LICS Thm 7.3 / LMCS Thm 10.4: closed call-by-name evaluation with Space KAM space is a reasonable space cost model, including logarithmic space.
  - LICS Prop. 7.4 / LMCS Prop. 10.7: a family of terms whose Space KAM runs take space and time `Ω(2^n)` against `n` β-steps, so natural time is not reasonable for this machine.
  - Call-by-need implementations "inevitably rely on a heap and on data pointers … Therefore, they are space unreasonable" by this criterion.
- **Derived reading.**
  - Both invariance results quantify over closed whole programs and allow linear (constant-factor) overhead with additive `log` terms.
  - Neither yields a compositional space measure; Forster–Kunze–Roth list compositional measures as future work.
  - Neither fixes the exhaustion point of a given program across machines. They establish that space *classes* are model-independent, not that a budget observed on one model is observed identically on another.

### 4. Back-translation: how step and resource mismatch is absorbed

Basis: documentation.

| Work | Back-translation | Observation | How mismatch is absorbed | Resources observable? |
|---|---|---|---|---|
| Abadi 1998 (SRC RR 154) | informal; full abstraction as protection, with condition (1) as "no information leaks" | contextual equivalence | n/a; lists target-only observations that break full abstraction: traffic, a denial of service that leaves a process "stuck", replay, message equality, forward secrecy | denial of service: "such attacks can sometimes be ignored by focusing on process equivalences that capture only safety properties, and not liveness properties" |
| Ahmed–Blume 2008 | wrappers `W±⟦τ⟧` in a single language (System F with ∃ and µ); back-translated context `Ĉ[W−⟦Γ⟧[W+⟦τ⟧([·])]]` | equi-termination (Def. 4.1) | `C⟦τ⟧ρ = {(k,e₁,e₂) \| ∀j<k. ∀v₁. e₁ −→ʲ v₁ ⇒ ∃v₂. e₂ −→* v₂ ∧ (k−j,v₁,v₂) ∈ V⟦τ⟧ρ}`: the index counts only the left side's steps; wrapper termination (Lemma 6.1) has no step bound; the cross-language variant (Fig. 10) is a sketch | no: no occurrences of "space", "resource" or "memory" |
| Devriese–Patrignani–Piessens 2016/2017 | `⟨⟨C⟩⟩τ;n = emulate_{n+1}(C)[inject_{τ;n} ·]` with `UVal_{n+1} = Unit ⊎ Unit ⊎ Bool ⊎ (UVal_n × UVal_n) ⊎ (UVal_n → UVal_n) ⊎ (UVal_n ⊎ UVal_n)`; target `wrong` is emulated by source divergence | equi-termination | `O(W)≲` budgets source steps and `O(W)≳` budgets target steps; antireduction decreases the index by `min(i, j)` (appendix Lemma 4); Thm 13 takes `n` larger than the target's step count, then `n₀` = source steps of the back-translated context | no: the appendix has 0 hits for "resource", "timing", "exhaust" or "memory" |
| Patrignani–Ahmed–Clarke 2019 survey | catalogue: partial evaluation (including trace-based) vs embedding (precise, over-approximating, under-approximating) | varies | under-approximation works "since for any particular program and context observing termination only takes a finite number of steps" | finite memory size is presented as a target attack (Ex. 2.3), but the formal treatment assumes "unbounded memory size"; "no criteria currently encompasses side channels" |

- **Derived consequence for observable fuel.** Both techniques let the back-translated source context take arbitrarily many more steps than the target context: wrappers in Ahmed–Blume, emulation and `UVal` tagging in Devriese et al.
  - With a source-level fuel budget whose exhaustion is observable, a context could spin for `k` steps before the hole and detect the emulation overhead.
  - So neither proof transfers unchanged to step-observable semantics.
  - The `min(i, j)` antireduction rule and the after-the-fact choice of `n` rely on termination being the only observable.

### 5. Fixed observable budgets: a preservation obstruction, and what padding or stuttering would have to preserve

Basis: derived (argument below) + execution (toy model of the argument, not of any published system).

**Setting.**
- Source `S` and target `T` each have a budget semantics: `Obs^B(P) ∈ {done(o), oom(o′)}`, with `oom` produced when live cost would exceed `B`.
- A translation `t` is given. Fixed-budget contextual equivalence is `P ≅^B Q ⇔ ∀C. Obs^B(C[P]) = Obs^B(C[Q])`, and `≅` means `≅^B` for every `B`.

**Fill lemma (derived).** Suppose `T` has, for every `k ≤ B`, a context `F_k` that holds `k` units live while running the hole and is otherwise inert. Suppose also that, run inside `F_k` at budget `B`, the hole behaves exactly as it does alone at budget `B − k` (a frame property). Then, for components with the same outputs:
- if the peak demands satisfy `peak(P) < peak(Q) ≤ B`, `F_{B−peak(P)}[P]` completes and `F_{B−peak(P)}[Q]` exhausts;
- hence `P ≅_T Q` implies `peak(C[P]) = peak(C[Q])` in every context where both fit.

**Corollary (derived).**
- `t` preserves `≅` only if `p ≅_S q ⇒ peak_T(C[t p]) = peak_T(C[t q])` for all `C`.
- Suppose `S` charges a construct less than `T` charges its translation, so that `peak_T(t p) − peak_S(p)` depends on how many such constructs `p` contains. Then there are `p ≅_S q`, for example components differing only in such constructs, that `t` separates.
- **No back-translation can rescue preservation**: the separating target context exists, and source equivalence says no source context separates `p` and `q`.
- Reflection can fail as well when `t` identifies source behaviours that differ in source cost.

**Toy confirmation.**
- Basis: execution, toy model `support/budget_fa_toy.py`, Python 3.13 on x86-64 Linux.
- Toy language:
  - constructs: `skip | out(1) | seq(p,p) | cell(p) | val(p)`;
  - `cell` and `val` hold one unit for the dynamic extent of their body;
  - the target has no `val`, and `t(val p) = cell(t p)`;
  - "arena" policy: the source charges `val` 0; "combined" policy: it charges 1; the target charges `cell` 1;
  - contexts are generated up to a size bound, and budgets range over `0..BMAX`.

| bounds (BMAX, program size, context size) | policy | programs | source / target contexts | source-equivalent pairs separated by target contexts | target-equivalent pairs separated in source | wall / max RSS |
|---|---|---|---|---|---|---|
| 4, 3, 3 | arena | 18 | 43 / 20 | 16 | 12 | 0.05 s / 11,024 kB |
| 4, 3, 3 | combined | 18 | 43 / 20 | 0 | 0 | (same run) |
| 5, 4, 4 | arena | 58 | 179 / 69 | 142 | 112 | 0.64 s / 13,332 kB |
| 5, 4, 4 | combined | 58 | 179 / 69 | 0 | 0 | (same run) |
| 6, 5, 4 | arena | 202 | 179 / 69 | 1,472 | 1,045 | 5.26 s / 15,648 kB |
| 6, 5, 4 | combined | 202 | 179 / 69 | 0 | 0 | (same run) |

- The witness reported for bounds (5, 4, 4) is exactly a fill context: `p = skip`, `q = val(val(skip))` (source-equivalent under arena), target context `cell(cell(cell(cell(□))))`, budget 5. Then `t(p)` gives `((), done)` and `t(q)` gives `((), oom)`.
- "Equivalent" verdicts are bounded-search verdicts. "Separated" verdicts have concrete witnesses.

**What a padded or stuttering back-translation would have to discharge** (derived). Consider a target in which exhaustion is observable and the source charges less for the same program.
1. **Padding must be component-independent.**
   - A back-translated context `⟨⟨C⟩⟩` may pre-allocate `π` extra source units to emulate target charges.
   - For `Obs_S^{B}(⟨⟨C⟩⟩[p]) = Obs_T^{B}(C[t p])` to hold for all `p` in an equivalence class, `π` may depend on `C` but not on `p`.
   - That is possible iff `peak_T(t p) − peak_S(p)` is constant on source-equivalence classes in every context: the corollary's condition again.
   - A compositional static shift, a per-construct fold `δ(C[p]) = δ_C(δ(p))`, is not enough by itself unless `δ(p)` is determined by source-observable behaviour.
2. **Stuttering addresses the wrong mismatch.** A stuttering simulation absorbs differing *step counts* between related states. Under a space budget, what must be absorbed is differing *live-cost profiles*. A stuttering argument helps only if the simulation relation also equates the remaining-budget component of related states.
3. **Routes that do restore a full-abstraction-like statement.**
   - (a) *Charge in the source what the target charges*: the "combined" toy policy, where both directions hold on the bounded instances. This gives up the source's cheaper construct.
     - A published compiler-correctness instance is CompCertS (Besson, Blazy, Wilke, JAR, 10.1007/s10817-018-9496-y; author PDF, §6.2.1). Its finite memory makes allocation failure observable. Because the Stacking pass increases stack use, it parameterises "the semantics of all intermediate languages, from C to Linear, with an oracle ns which specifies, for each function f, the additional space that is needed", reserved at function entry.
     - The padding is per-function, so it is component-dependent. It is legitimate because it lives in the *source semantics*, which makes source equivalence itself sensitive to it.
   - (b) *Hide the overhead behind a component-independent reservation*. Patrignani et al. TOPLAS 2015 reserve "a constant amount of memory … for each protected module, independent of the actual memory space required" so that modules cannot be distinguished by size. Their back-translation theorem still assumes no stack or heap overflow (Thm 5.9).
   - (c) *Weaken the criterion one-sidedly*, as in compiler correctness. CakeML allows the target an extra `Terminate Resource_limit_hit` after any I/O prefix (`semantics/proofs/semanticsPropsScript.sml:219–226`). The JFP preprint concedes that "A trivial compiler that always produces code that runs out of memory would satisfy this kind of theorem". No published security criterion of this shape was found.
   - (d) *Bound the trace length or resources inside the back-translation*. SECOMP (CCS 2024) assumes "as an axiom that the result of our back-translation, on any trace prefix below a certain length, can be successfully compiled", to "account for machine words being finite and other such finite resources".

### 6. Performance and resource footprint (L1–L6)

| Level | Evidence | Value |
|---|---|---|
| L1 authoring | Forster–Kunze–Roth Coq repository at pinned revision | 34 `.v` files, 7,124 lines; 26 built by `_CoqProject`, 4,186 lines; project-specific files (ARS, L, Prelims, Programs, two machines) 1,408 lines; one `Admitted` (`Base/FiniteTypes/Arbitrary.v:30–31`) outside the main lemmas' import cone (static `Require` analysis only) [measured: `wc -l` on fetched files]. Person-months, token budgets, and the size of the Paraskevopoulou–Appel or Devriese et al. Coq developments: not measured |
| L2 toolchain build | README: "tested to compile with The Coq Proof Assistant, version 8.8.2" | build time and memory: not measured (not built) |
| L3 elaboration | — | not measured |
| L4 generated code | Paraskevopoulou–Appel Cor. 8.2 | time ×7 (`ktime = 7`), space `+ cost^space_exp(e) + 1` [cited] |
| L4 machine overhead | Forster–Kunze–Roth Lemmas 3.1–3.4 (= Coq lines above) | substitution machine 3k+1 steps, space `m ≤ m′ ≤ 2m`; heap machine 4k+2 steps, size `≤ (i+1)(3i+4‖s‖)` [cited + source] |
| L4 explosion | Accattoli–Dal Lago–Vanoni Prop. 7.4 / 10.7 | Space KAM space and time `Ω(2^n)` for `n` β-steps on a term family [cited] |
| L5 checking | — | not measured (no Coq build, no `Print Assumptions`) |
| L6 footprint | repository docs | 36 `docs/` files, 1,622,165 bytes of coqdoc HTML; 34 `.v` files, 207,533 bytes [measured: GitHub tree API sizes] |
| L6 toy | `budget_fa_toy.py` | 13,332 kB max RSS, 0.64 s at bounds (5, 4, 4); 15,648 kB, 5.26 s at (6, 5, 4) [measured: `/usr/bin/time -f "%e %M"`, x86-64 Linux host] |

### 7. Comprehensibility and conceptual simplicity (C1–C2)

- **C1, human legibility.**
  - Fixed-budget equivalence has an unusually concrete counterexample shape: one fill context and one budget. That makes failures easy for humans to audit.
  - Step-indexed proofs are much less legible. They need two asymmetric relations (`≲`, `≳`), a world/later modality, and an after-the-fact choice of `n` and `n₀`, and the Devriese et al. appendix runs to 88 pages.
  - Space improvement adds four kinds of "tick" (spikes and ballast) and a free-variable side condition. These are nonlocal facts a reviewer must track.
- **C2, simplicity and orthogonality.**
  - The literature uses three mechanisms for one invariant ("no context sees more cost than it should"): constant-factor slack (weak improvement, invariance theses), additive program-dependent shifts (safe-for-space), and one-sided escapes (CakeML).
  - The fill lemma shows these are not interchangeable once the bound is observable: only exact cost agreement, or a component-independent reservation, preserves fixed-budget equivalence.
  - A minimal universal abstraction would make the *remaining budget* part of the observable state of contexts, so that exhaustion is an ordinary outcome. Then "charge in the source what the target charges" stops being a special case: it is the only way the observation can agree.
  - The cost of that choice is moved into the source language's cost model rather than eliminated.

### 8. Validation of the claims and techniques (V1–V4)

- **V1, specification adequacy.**
  - Gustavsson–Sands validate their measure against implementations only informally: the same program runs in constant space under HUGS'98 and GHC 4.01 but exhausts the stack in hbc 0.9999.5a.
  - Forster–Kunze–Roth's mechanised lemmas reproduce the paper's constants exactly, which is a non-vacuity check on the printed statements, but the Lemma B.7 factor-2 difference remains.
  - The toy model is a non-vacuity check of the fill lemma's hypotheses on bounded instances: the "combined" policy yields 0 separations, so the probe can return a negative result.
- **V2, compiler and checker fuzzing.**
  - No differential or metamorphic testing of space behaviour against these theories was found.
  - The Patrignani–Ahmed–Clarke survey notes that side channels are "often not expressible in the target language", which is exactly why exhaustion escapes language-level testing.
- **V3 and V4** (concurrency, crash, physical leakage, plant, and human-model validation): not examined for this topic.

## Boundaries

- **Not examined (full text unavailable):**
  - Gustavsson–Sands ICFP 2001: abstract only. Which classical transformations it classifies, and its limitation theorems, are unknown.
  - Bakewell–Runciman PPDP 2000: neither text nor abstract. Its space semantics, the evaluators compared, the form of the relation, and compositionality are all unknown.
  - Minamide 1999: abstract and secondary description only. Whether the CPS space constant is multiplicative only is unknown.
  - Hackett–Hutton 2014 and 2018: abstracts only, so no exclusion of space can be quoted.
  - Kennedy (TCS 2006): abstract only.
  - Barthe–Grégoire–Laporte (CSF 2018): slides and earlier abstract only.
  - Jagadeesan et al. (CSF 2011): not examined, so how it formally treats finite memory size is unknown.
  - The body of the LMCS 2017 Devriese et al. article: its technical appendix was read instead.
- **Version caveats.** The Gustavsson–Sands definitions come from a draft whose glyphs were reconstructed. The exact form of the linear function in Def. 5.1 is not confirmed against the ENTCS final version.
- **Not built.** The Coq repository was not compiled with Coq 8.8.2, so the claim that the lemmas are proved rests on the repository's own statement and a static `Admitted` search, not on a kernel check.
- **Unknown.**
  - Whether any published secure-compilation work proves a criterion weakened to account for target-observable exhaustion, as Juglaret et al. anticipate. None was found among the papers searched.
  - Whether a budget-shifted equivalence (`∀B ∃B′`) can be made compositional without the component-independence condition of §5.
- **Known not to apply.**
  - Invariance theorems (Forster–Kunze–Roth; Accattoli–Dal Lago–Vanoni) do not establish that exhaustion points agree across machines. They are asymptotic and whole-program.
  - Step-indexed back-translations do not transfer to semantics where fuel exhaustion is observable without new arguments (§4).
- **Attractive but unsupported conclusions.**
  - "Weak space improvement is sound for bounded-memory equivalence." It is not: its constant factors are observable.
  - "A stuttering simulation closes the bounded-memory full-abstraction gap." It addresses step counts, not live-cost profiles.
  - "The toy's counts measure anything about real languages." They show only that the fill lemma's premises are satisfiable and its conclusion non-vacuous on a toy.
- **Fill-lemma hypotheses.** The lemma assumes the target has inert, live-holding contexts for every `k ≤ B` and a frame property for budgets. Targets lacking such contexts, for example those that cannot allocate, or those where budgets are per component, are outside the argument.

## Evidence

- **Observation dates.** All literature, repository reads, and executions took place on 2026-11-21 (UTC).
- **Repositories** (read-only; GitHub API plus raw files at the pinned commit):
  - `uds-psl/cbv-lambda-calculus-reasonable` at `4f12b7c8ce2816cdd771d22d04943e0fa81c63fd`, which is the tip of `master`, dated 2019-11-06:
    - `AbstractSubstMachine.v:62–64`, `:169–171`;
    - `AbstractHeapMachine.v:252–256`, `:308–309`, `:418–429`, `:438–439`;
    - `ARS.v:104–108`; `L.v:23–28`; `README.md` (Coq 8.8.2);
    - `Base/FiniteTypes/Arbitrary.v:30–31` (`admit.` / `Admitted.`).
  - `CakeML/cakeml` at `2874b664e10939a3ee462215b2e068c89c1f70eb`: `semantics/proofs/semanticsPropsScript.sml:219–237` (`extend_with_resource_limit`, `implements`).
  - `squera/squera.github.io` at `ec5c7909a6b5245aabf9c1caabb79b0b7b07d543`:
    - `pdf/lmcs-TR.pdf`, "Modular Fully-Abstract Compilation by Approximate Back-Translation: Technical Appendix": §3.5 p. 16 observation relations and Lemma 4; Lemmas 14–15 p. 21; §6.6 p. 76 Lemma 49; Thm 13 pp. 76–77;
    - `pdf/main-full.pdf`, the pre-publication full survey with Appendices A–B.
- **Literature** (DOIs verified against Crossref on 2026-11-21; the version read is given in brackets):
  - Moran, Sands, POPL 1999, pp. 43–56, 10.1145/292540.292547 [author extended version].
  - Gustavsson, Sands, ENTCS 26 (1999) pp. 69–86, 10.1016/S1571-0661(05)80284-1 [2 July 1999 draft].
  - Gustavsson, Sands, ICFP 2001, pp. 265–276, 10.1145/507635.507667 [abstract].
  - Sands, Gustavsson, Moran, "Lambda Calculi and Linear Speedups", LNCS (The Essence of Computation) 2002, pp. 60–82, 10.1007/3-540-36377-7_4 [published layout].
  - Hackett, Hutton:
    - ICFP 2014, pp. 95–107, 10.1145/2628136.2628142 [abstract];
    - PACMPL 2(ICFP) 2018, 10.1145/3236763 [abstract];
    - PACMPL 3(ICFP) 2019, article 114, 10.1145/3341718 [published layout].
  - Bakewell, Runciman, PPDP 2000, pp. 151–162, 10.1145/351268.351287 [not obtained].
  - Minamide, ENTCS 26 (1999) pp. 105–120, 10.1016/S1571-0661(05)80286-5 [abstract].
  - Forster, Kunze, Roth, PACMPL 4(POPL) 2020, article 27, 10.1145/3371095, arXiv:1902.07515 [published version].
  - Accattoli, Dal Lago, Vanoni:
    - LICS 2022, pp. 1–13, 10.1145/3531130.3533362 [published];
    - LMCS 20(4) 2024, 10.46298/lmcs-20(4:15)2024, arXiv:2203.00362 [arXiv v6 = LMCS].
  - Abadi, ICALP 1998, LNCS pp. 868–883, 10.1007/BFb0055109 [SRC Research Report 154, 17 April 1998].
  - Ahmed, Blume, ICFP 2008, pp. 157–168, 10.1145/1411204.1411227 [author copy with ACM block].
  - Devriese, Patrignani, Piessens:
    - POPL 2016, pp. 164–177, 10.1145/2837614.2837618 [author version];
    - with Keuchel, LMCS 13(4) 2017, 10.23638/lmcs-13(4:2)2017, arXiv:1703.09988 [technical appendix only].
  - Patrignani, Ahmed, Clarke, ACM Computing Surveys 51(6) 2019, article 125, 10.1145/3280984 [published version plus author full version].
  - Paraskevopoulou, Appel, PACMPL 3(ICFP) 2019, article 83, 10.1145/3341687 [published layout].
  - Patrignani, Agten, Strackx, Jacobs, Clarke, Piessens, TOPLAS 37(2) 2015, 10.1145/2699503 [author preprint].
  - Juglaret, Hriţcu, Azevedo de Amorim, Eng, Pierce, CSF 2016, pp. 45–60, 10.1109/CSF.2016.11, arXiv:1602.04503 [v6].
  - Fournet, Swamy, Chen, Dagand, Strub, Livshits, POPL 2013, pp. 371–384, 10.1145/2429069.2429114 [HAL author version].
  - Skorstengaard, Devriese, Birkedal, "StkTokens", PACMPL 3(POPL) 2019, 10.1145/3290332 [author copy].
  - Abate et al., "When Good Components Go Bad", CCS 2018, pp. 1351–1368, 10.1145/3243734.3243745, arXiv:1802.00588 [v5].
  - Thibault et al., "SECOMP", CCS 2024, pp. 1061–1075, 10.1145/3658644.3670288, arXiv:2401.16277 [v7].
  - Abate, Blanco, Garg, Hriţcu, Patrignani, Thibault, CSF 2019, 10.1109/CSF.2019.00025, arXiv:1807.04603 [v6].
  - Carbonneaux, Hoffmann, Ramananandro, Shao, PLDI 2014, pp. 270–281, 10.1145/2594291.2594301 [author copy].
  - Tan, Myreen, Kumar, Fox, Owens, Norrish, "The verified CakeML compiler backend", JFP 29 e2 (2019), 10.1017/S0956796818000229 [preprint dated 19 November 2018].
  - Besson, Blazy, Wilke, "CompCertS", JAR 63(2) 369–392, 10.1007/s10817-018-9496-y [author PDF, §6.2.1].
- **Execution.** `python3 support/budget_fa_toy.py BMAX PROG_SIZE CTX_SIZE` was run with arguments `4 3 3`, `5 4 4` and `6 5 4` under `/usr/bin/time` on an x86-64 Linux host with Python 3.13. Outputs are preserved in `support/budget_fa_toy_output.txt`.
- **Synthesis versus source facts.** The fill lemma, its corollary, and the padding and stuttering obligations in §5 are this report's synthesis. Every quoted definition, theorem, or limitation is a source fact.

## Revalidation

- **Coq artifact.** Diff the four lemma statements quoted in §3 at a newer revision of `uds-psl/cbv-lambda-calculus-reasonable`. Building it with Coq 8.8.2 (`make`) and running `Print Assumptions correctSpace` would upgrade the mechanisation claim from "stated" to "kernel-checked".
- **Toy model.** Rerun `python3 support/budget_fa_toy.py 5 4 4`. Expect `arena … separated by target contexts=142` and `combined … =0`. Any change in the counts means the probe changed, not the literature.
- **New secure-compilation results.** Search new papers for "resource exhaustion", "out of memory", "stack overflow", or "finite memory" in their attacker model, and check whether the criterion is one-sided (CakeML-style) or component-independent (reservation-style). Either would answer the open question in Boundaries.
- **Space-improvement texts.** If the ENTCS final version of Gustavsson–Sands or the ICFP 2001 full text becomes available, check Def. 5.1's linear function and the list of space-unsafe transformations against §1.
