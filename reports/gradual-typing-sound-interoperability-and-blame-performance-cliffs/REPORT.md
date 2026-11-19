# Gradual Typing, Sound Interoperability, and Blame Performance Cliffs

## Summary

Gradual typing combines statically typed and dynamically typed code within one language—or across a multi-language boundary—by replacing strict type equality with a non-transitive **type consistency** relation (`~`) and compiling implicit cross-boundary flows into runtime checks or casts. Two decades of formal metatheory, compiler engineering, and $2^N$-lattice benchmarking establish a fundamental **Soundness–Speed–Structural-Flexibility Design Triangle**: no single homogeneous runtime enforcement strategy simultaneously provides full higher-order behavioral soundness, zero-cliff performance across arbitrary partially typed configurations, and drop-in interoperability with legacy untyped structural code:

1. **Formal Guarantees Separate Three Independent Properties.** *Mixed-typed syntactic type soundness* (typed expressions evaluate to values matching their static type or a trapped cast error) is strictly weaker than **Complete Monitoring** (Greenman, Felleisen & Dimoulas 2019), which requires mediating *every* communication channel between typed and untyped code—including untyped callbacks routed through a typed API—so every violation admits a concise 2-party blame explanation. Independently, the **Blame Theorem** (Wadler & Findler 2009) guarantees that across a cast from a more-precise type $S$ to a less-precise type $T$ ($S <:^n T$), only the less-typed side can be blamed; and the **Gradual Guarantee** (Siek et al. 2015) requires that loosening type annotations never introduces new static or dynamic failures.
2. **Deep Higher-Order Soundness (`Natural`) Triggers $10\times$–$15{,}000\times$ Cliffs Across $2^N$ Lattices.** Enforcing higher-order functions and mutable containers via behavioral wrappers (Racket chaperones/impersonators, Strickland et al. 2012) satisfies Complete Monitoring and permits type-directed optimizations in typed code, yet causes catastrophic mixed-configuration slowdowns (Takikawa et al. 2016; Greenman et al. 2019; Greenman 2022). Five distinct mechanisms drive these cliffs: unbounded wrapper chains, $O(|\text{container}|)$ eager scans of immutable inductive data (lists), per-access proxy indirection and struct-adaptor boundaries, JIT/optimizer type-stability collapse across proxies, and asymmetric typed-to-untyped library calls.
3. **Space-Efficient Coercions Fix Wrapper Growth but Leave Constant-Factor and Eager-Scan Costs.** Herman, Tomb & Flanagan's (2010) normalized coercion calculus (`Grift` coercions, hyper-coercions, and coercion-passing style; Racket's lazy `COLLAPSIBLE-LIMIT = 10` collapsible contracts) bounds proxy depth to $O(1)$ and coercion AST size to $\le 5(2^{\text{height}(S)} - 1)$, eliminating $O(N)$ stack blowups and $O(N^2)$ traversal cliffs (`0.32x–87x` faster than type-based casts on `sieve` in `Grift`). However, mutable-array proxy checks still pull statically typed `Grift` down to `0.49x` of Static Grift, and eager list scans remain unaffected.
4. **Alternative Triangle Vertices Trade Complete Monitoring or Structural Flexibility for Predictable Cost:**
   - **Transient / Shallow (`Reticulated Python`, `typed/racket/shallow`)** eliminates proxies via $O(1)$ top-level shape checks at every typed entry and elimination site. It achieves open-world soundness on spartan hosts, preserves object identity, and bounds Reticulated Python to `2.5x` avg / `5.4x` worst-case without blame (`<= 18x` with collaborative blame maps), but loses Complete Monitoring and pays a ubiquitous linear tax even in fully typed code.
   - **Concrete / Nominal (`Nom`, `CinderX Static Python`)** attaches exact nominal runtime type tags at allocation and exposes dual static/dynamic entrypoints (`chklist_append` vs. `chklist_append_wrapper`). Typed reads pay zero proxy or element checks and throughput improves monotonically as types are added (`+3.7%` max-CPU requests/sec in Instagram's server monolith), at the cost of rejecting unannotated legacy untyped containers without explicit conversion or nonlocal refactoring.
   - **Erasure (`TypeScript`, `mypy`, `typed/racket/optional`)** adds zero runtime cost and preserves all dynamic idioms, but provides zero runtime soundness.
5. **Production Convergence Favors Multi-Enforcement Hybrids.** Mixing Deep and Shallow modules (`typed/racket/deep` + `typed/racket/shallow` + `typed/racket/optional`, Greenman 2022) cuts worst-case GTP cliffs dramatically (`dungeon`: `15,000x -> 3.16x`; `forth`: `5,800x -> 5.43x`; `fsmoo`: `420x -> 4.25x`), while staging Shallow $\to$ Concrete $\to$ Unboxed Primitives (Static Python, Lu et al. 2023) restricts nominal refactoring to hot paths.

## Applicability

This package synthesizes **sixteen primary peer-reviewed publications (2006–2023)**, **six pinned upstream open-source repositories** (`racket/typed-racket`, `racket/racket`, `mvitousek/reticulated`, `Gradual-Typing/Grift`, `facebookincubator/cinderx`, `bennn/gtp-benchmarks`), and one self-contained Python 3.10+ executable probe (`support/verify_gradual_semantics_and_cliffs.py`).

### Relationships Among Examined Subjects

- **Formal Calculi & Metatheory (`normative`):** `Siek & Taha (2006)`, `Matthews & Findler (2007)`, `Wadler & Findler (2009)`, `Herman, Tomb & Flanagan (2010)`, `Strickland et al. (2012)`, `Siek et al. (2015)`, and `Greenman, Felleisen & Dimoulas (2019)` define consistency, multi-language boundaries, blame factoring, coercion space bounds, chaperones/impersonators, the gradual guarantee, and complete monitoring.
- **Compiler & Runtime Implementations (`source` + `documentation`):**
  - `racket/typed-racket` (`7fe7e11fae2b04e04525d63b01b33efe5ffad075`) & `racket/racket` (`8ed38e11307b13f25ca67224c66438b83340ae68`): macro-level Deep, Shallow, and Optional enforcement over Racket's chaperone/impersonator and collapsible-contract runtime (`Feltey et al. 2018`; `Greenman 2022`).
  - `mvitousek/reticulated` (`5cd2d10e0f92505a9db2bc573d8c23360ef6548b`): fine-grained gradual Python implementing `transient`, blame-tracked transient, archived `guarded`, and archived `monotonic` semantics on unmodified CPython (`Vitousek, Swords & Siek 2017`).
  - `Gradual-Typing/Grift` (`5fa76f837a0d6189332343d7aa899892b3c49583`): AOT gradual compiler targeting C with type-based casts, coercions, hyper-coercions, coercion-passing style, and monotonic heap cells (`Kuhlenschmidt, Almahallawi & Siek 2019`).
  - `facebookincubator/cinderx` (`8ff26422ae5657cbcc9bc976c0695ab54cf861c1`): Meta CPython extension implementing Static Python's shallow + concrete checked containers (`chklist`, `chkdict`) and dual static/dynamic entrypoints (`Lu et al. 2023`).
- **Empirical Lattice Evaluations (`execution` / `documentation`):** `Takikawa et al. (2016)`, `Vitousek et al. (2017)`, `Muehlboeck & Tate (2017)`, `Greenman & Felleisen (2018)`, `Greenman et al. (2019)`, `Greenman (2022)`, and `Lu et al. (2023)`, anchored to `bennn/gtp-benchmarks` (`f974dcba643880399df9fe643009e9f04dc58f19`).
- **Executable Model (`execution`):** `support/verify_gradual_semantics_and_cliffs.py` independently verifies the type-relation factorizations, blame polarities, HTF collapse bounds, Complete Monitoring separation, and $2^4$ scaling behavior across all five modeled semantics.

### Scope Boundaries & Cross-Corpus Relations

- **Macro-Level vs. Fine-Grained Granularity:** Typed Racket and Static Python enforce boundaries primarily at module granularity (migratory typing), whereas $\lambda^?_\to$, Reticulated Python, Grift, and Nom allow `Dyn` (`?`) at expression granularity. Underlying representation trade-offs (proxies, coercions, transient tag checks, concrete tags) govern both, though macro-level systems concentrate costs at inter-module edges and adaptor modules.
- **FFI & Static Verification Boundaries:** Every FFI boundary joining a richer static type system to a dynamic or weaker host exhibits the same multi-language wrapper-versus-trust trade-off (Matthews & Findler 2007). For ahead-of-time static verification of functional and heap specifications via SMT/VC generation—the static endpoint of the contract-to-proof spectrum—refer to `dafny-boogie-viper-fstar-why3-and-vc-obligation-architectures`; this report covers *dynamic and mixed static/dynamic runtime boundary enforcement*.

## Findings

### 1. Formal Foundations: Type Consistency, Multi-Language Boundaries, and the Gradual Guarantee

Basis: normative (Siek & Taha 2006; Matthews & Findler 2007; Siek et al. 2015) + execution (`support/verify_gradual_semantics_and_cliffs.py`).

#### Type Consistency (`~`) vs. Subtyping

Siek & Taha (2006) introduce the Gradually Typed Lambda Calculus ($\lambda^?_\to$) with unknown type `?` (later written `Dyn`), replacing strict type equality in application with **type consistency** ($\tau_1 \sim \tau_2$):

```text
(CREFL)  τ ~ τ            (CUNR)  τ ~ ?            (CUNL)  ? ~ τ

         σ1 ~ τ1   σ2 ~ τ2
(CFUN)   -------------------
         σ1 -> σ2 ~ τ1 -> τ2
```

Unlike subtyping (`<:`), **consistency is reflexive, symmetric, and non-transitive** (Proposition 1): `Int ~ ?` and `? ~ Bool`, yet `¬(Int ~ Bool)`. Non-transitivity prevents `?` from collapsing static checking across unrelated types. Elaboration translates $\lambda^?_\to$ via cast insertion into an explicit cast calculus $\lambda^{\langle\tau\rangle}_\to$ (Isabelle/Isar mechanized):
- **Static conservative extension (Theorem 1, Lemma 4):** Fully annotated programs typecheck identically to STLC and emit zero runtime casts.
- **Pay-as-you-go Canonical Forms (Lemma 5):** Statically typed values require no runtime tags unless injected into `?`.
- **Type safety (Theorem 2):** Well-typed $\lambda^?_\to$ programs diverge, yield a value of the predicted type, or halt with a trapped cast error—never an untrapped type error.

#### Multi-Language Operational Semantics

Matthews & Findler (2007) model typed/untyped interoperability directly via an ML-like static language ($M$) and Scheme-like dynamic language ($S$) joined by boundary operators `${}^{\tau}\mathcal{M}\mathcal{S}(e)` (dynamic $\to$ static) and `${}^{\tau}\mathcal{S}\mathcal{M}(e)` (static $\to$ dynamic):
- **Lump embedding:** Wraps foreign values as opaque tagged `Lump`s—$O(1)$ and sound, but prevents native foreign function calls or projections without explicit marshaling.
- **Natural embedding:** Checks base types eagerly and wraps higher-order functions (`σ -> τ`) so arguments cross the opposite boundary (`SM`/`MS` polarity swap) and results cross forward. This directly underlies Typed Racket and higher-order FFI monitors.

#### The Refined Criteria and the Gradual Guarantee

Siek, Vitousek, Cimini & Boyland (SNAPL 2015) distinguish true gradual typing from unsound or restricted hybrids via a structural **precision preorder** ($\sqsubseteq$, with $T \sqsubseteq ?$ covariant in all constructors) and **Theorem 5 (Gradual Guarantee)**:

> Suppose $e \sqsubseteq e'$ (loosening annotations toward `?`) and $\vdash e : T$. Then:
> 1. **Static:** $\vdash e' : T'$ with $T \sqsubseteq T'$.
> 2. **Dynamic Forward:** $e \Downarrow v \implies e' \Downarrow v'$ with $v \sqsubseteq v'$; $e \Uparrow \implies e' \Uparrow$.
> 3. **Dynamic Backward:** $e' \Downarrow v' \implies (e \Downarrow v \land v \sqsubseteq v') \lor e \Downarrow \text{blame}_T\ l$; $e' \Uparrow \implies e \Uparrow \lor e \Downarrow \text{blame}_T\ l$.

**Mutable-reference tension (Siek et al. 2015 §5.2):** Making `Ref T` invariant breaks the Static Gradual Guarantee: `(λy:Ref Int. y) ((λx:Ref ?. x) (ref 42))` is strictly less precise than `(λy:Ref Int. y) ((λx:Ref Int. x) (ref 42))` yet fails static typing under invariance. Supporting gradual `Ref` casts therefore forces runtime enforcement—guarded proxies, monotonic heap cells, or transient read/write checks.

---

### 2. Blame Polarity, Higher-Order Proxies, and Complete Monitoring

Basis: normative (Wadler & Findler 2009; Strickland et al. 2012; Greenman, Felleisen & Dimoulas 2019) + source (`racket/typed-racket`, `racket/racket`) + execution (`support/verify_gradual_semantics_and_cliffs.py`).

#### Subtyping Factorization and the Blame Theorem

Wadler & Findler (ESOP 2009) annotate casts $\langle T \Leftarrow S \rangle^p\ s$ with a positive blame label $p$ (producer $s$) and complementary negative label $\bar{p}$ (consumer context). They decompose both **ordinary subtyping** ($S <: T$: cast cannot fail) and **naive subtyping** ($S <:^n T$: $S$ is more precise than $T$, covariant in function domains) into **positive** ($<:+$) and **negative** ($<:^-$) subtyping:

| Relation | Base / `Dyn` Rules | Function Rule (`S -> T` vs `S' -> T'`) | Semantic Role (Wadler & Findler 2009) |
| --- | --- | --- | --- |
| Ordinary (`<:`) | `Dyn <: Dyn`, `B <: B` | `S' <: S` and `T <: T'` (contravariant dom) | Cast `S => T` cannot fail positively or negatively |
| Positive (`<:+`) | `S <:+ Dyn`, `B <:+ B` | `S' <:^- S` and `T <:+ T'` | Cast `S => T` with label `p` cannot fail with blame `p` |
| Negative (`<:^-`) | `Dyn <:^- T`, `B <:^- B` | `S' <:+ S` and `T <:^- T'` | Cast `S => T` with label `p` cannot fail with blame `p̄` |
| Naive (`<:^n`) | `S <:^n Dyn`, `B <:^n B` | `S <:^n S'` and `T <:^n T'` (covariant dom) | `S` is more precisely typed than `T` (safe upcast) |

- **Proposition 8:** $S <: T \iff S <:+ T \land S <:^- T$.
- **Proposition 9:** $S <:^n T \iff S <:+ T \land T <:^- S$.
- **Proposition 10 & Blame Theorem:** If every cast labeled $p$ satisfies $S <:+ T$ and every cast labeled $\bar{p}$ satisfies $S <:^- T$ (with valid positive refinements), evaluation cannot raise $\Uparrow p$. Hence across any cast between more-typed $S$ and less-typed $T$ ($S <:^n T$), the more-typed side cannot be blamed.

#### Higher-Order Contravariance and Mutable-Container Polarity Reversal

1. **Functions:** $(\langle S' \to T' \Leftarrow S \to T \rangle^p\ v)\ w \longrightarrow \langle T' \Leftarrow T \rangle^p\ (v\ (\langle S \Leftarrow S' \rangle^{\bar{p}}\ w))$. Domain application flips $p \mapsto \bar{p}$, so an untyped caller supplying a bad argument to a typed function receives negative blame; at order 2, a bad callback return undergoes a second flip back to blaming the untyped callback supplier.
2. **Mutable references/vectors:** Reads flow producer $\to$ consumer (polarity $p$), while writes reverse flow consumer $\to$ producer (polarity $\bar{p}$). Source audit of `racket/typed-racket@7fe7e11fae2b04e04525d63b01b33efe5ffad075`, `typed-racket-lib/typed-racket/private/type-contract.rkt` (L577–582), confirms this exact lowering:
   ```racket
   [(Immutable-HeterogeneousVector: ts) (apply immutable-vector/sc (map t->sc ts))]
   [(Immutable-Vector: t)               (immutable-vectorof/sc (t->sc t))]
   [(Mutable-HeterogeneousVector: ts)   (apply mutable-vector/sc (map t->sc/both ts))]
   [(Mutable-Vector: t)                 (mutable-vectorof/sc (t->sc/both t))]
   [(Box: t)                            (box/sc (t->sc/both t))]
   ```
   Mutable vectors and boxes force `t->sc/both` (positive + negative monitoring), whereas immutable vectors require only one-sided `t->sc`.

#### Chaperones vs. Impersonators (Strickland et al. 2012)

Plain closure wrappers break VM primitives (`vector?`, `equal?`, struct predicates, arity introspection). Strickland, Tobin-Hochstadt, Findler & Flatt (OOPSLA 2012) added VM-level proxies to Racket:
- **Chaperones** (`chaperone-procedure`, `chaperone-vector`, `chaperone-box`, `chaperone-struct`, `chaperone-hash`): interpose on calls, reads, and writes, but VM enforcement restricts interposition handlers to either raising a contract exception or returning a `chaperone-of?` value (preserving `equal?` and structural invariants).
- **Impersonators** (`impersonate-vector`, `impersonate-procedure`): relax `chaperone-of?` to allow value-substituting wrappers, tracked via `impersonator-of?`. Typed Racket orders contract kinds as `flat < chaperone < impersonator` (`type-contract.rkt` L271–289).

#### Complete Monitoring vs. Syntactic Type Soundness (Greenman, Felleisen & Dimoulas 2019)

Greenman, Felleisen & Dimoulas (OOPSLA 2019) demonstrate that classic mixed-typed syntactic type soundness cannot distinguish Deep (`Natural`) from Shallow (`Transient`). In their *Clickable Plot* example, an untyped client passes callback `h` (expecting `[Int, Int]`) through a typed API (`([Int, Int] -> Image)`) into an untyped library that invokes `h(MouseEvt)`. Because an untyped caller invokes an untyped callee, mixed-typed soundness permits `MouseEvt` to pass unchecked under `Transient`.

> **Complete Monitoring:** Enriching operational semantics with component ownership, a mixed-typed language satisfies Complete Monitoring iff for every well-formed $e$ and reduction $e \longrightarrow^* e'$, every subexpression of $e'$ has a unique owner—no value crosses a boundary without a monitor mediating ownership transfer.

Complete Monitoring separates debugging guarantees: Deep monitoring yields a **concise 2-party blame explanation** for every violation on any direct or derived channel, whereas semantics failing Complete Monitoring require up to $2N$-party blame sets (**blame soundness** and **blame completeness**).

---

### 3. Space-Efficient Coercions, Threesomes, and Collapsible Contracts

Basis: normative (Herman, Tomb & Flanagan 2010; Feltey et al. 2018; Kuhlenschmidt, Almahallawi & Siek 2019) + documentation (Siek & Wadler 2010) + source (`Gradual-Typing/Grift`, `racket/racket`) + execution (`support/verify_gradual_semantics_and_cliffs.py`).

#### Naive Proxy Space Leaks and the Coercion Space Bound

Herman, Tomb & Flanagan (HOSC 2010) showed two asymptotic failures in naive higher-order proxies:
1. **Tail-call destruction:** Mutually recursive typed/untyped calls (`odd : Int -> Bool` calling untyped `even`) wrap the tail call in a return cast `⟨Bool ⇐ Dyn⟩`, turning $O(1)$ tail stack space into $O(N)$ stack overflow.
2. **Proxy chain blowup:** Repeatedly passing a continuation `k` or mutable array across a loop boundary wraps it in $O(N)$ nested proxies, causing $O(N)$ per-access indirections and $O(N^2)$ cumulative work.

Their coercion calculus (`I`, `Fail`, `G!`, `G?`, `Fun c d`, `Ref c d`, `c ; d`) eagerly normalizes adjacent coercions:
- `G! ; G?` $\longrightarrow$ `I` (canceling matching ground tags and unwrapping identity proxies).
- `G1! ; G2?^l` $\longrightarrow$ `Fail l` when $G_1 \neq G_2$ (**early error detection**, §7: `(Int -> Int) => Dyn => (Bool -> Int)` collapses to `Fun Fail I` before invocation).
- `(Fun c1 d1) ; (Fun c2 d2)` $\longrightarrow$ `Fun (c2 ; c1) (d1 ; d2)` (contravariant domain order); `(Ref r1 w1) ; (Ref r2 w2)` $\longrightarrow$ `Ref (r1 ; r2) (w2 ; w1)`.

With $\text{height}(I)=\text{height}(\text{Fail})=\text{height}(G!)=\text{height}(G?)=1$, $\text{height}(\text{Fun}\ c\ d)=\text{height}(\text{Ref}\ c\ d)=1+\max(\text{height}(c),\text{height}(d))$, and $\text{height}(c;d)=\max(\text{height}(c),\text{height}(d))$, Herman et al. prove:
- **Lemma 2:** Every well-typed normalized coercion $c$ satisfies $\text{size}(c) \le 5(2^{\text{height}(c)} - 1)$ (at most `[G? ; Med ; G!]`).
- **Theorem 4:** Every coercion $c$ created during evaluation of $e_0$ satisfies $\text{height}(c) \le \text{height}(S)$ and $\text{size}(c) \le 5(2^{\text{height}(S)} - 1)$ for some type $S$ in the static derivation of $e_0$—strictly $O(1)$ in loop iterations $N$. Siek & Wadler (POPL 2010, *Threesomes, With and Without Blame*, DOI `10.1145/1707801.1706342`) showed how threesome casts carry full Wadler–Findler blame within equivalent $O(1)$ space.

#### Audited Implementations: Grift Hyper-Coercions vs. Racket Collapsible Contracts

1. **`Gradual-Typing/Grift` (`5fa76f837a0d6189332343d7aa899892b3c49583`):**
   - Eager coercion composition (`src/casts/interpret-casts-with-coercions.rkt`, `make-compose-coercions` L860–904), minimally bushy **hyper-coercions** (`src/casts/interpret-casts-with-hyper-coercions.rkt` L43–87, L220–265) flattening `[proj?; med; inj?]` for cache locality, and **coercion-passing style** (`src/casts/coercion-passing.rkt` L17–95) threading continuation coercions through tail calls to preserve $O(1)$ stack depth.
   - Implements both guarded proxy cells (`compile-pref-cast/coercions`, `compile-pvec-cast/coercions`, L234–244) and monotonic heap cells (`compile-mbox-cast/coercions`, `compile-mvec-cast/coercions`, L246–256; C queue `src/backend/runtime/suspended_cast.h` L6–9).
   - **PLDI 2019 empirical results (Kuhlenschmidt et al. 2019 §4.2–4.3):** Uncollapsed type-based casts on `sieve` reached proxy chains `> 2,000`; coercions eliminated those chains and ran **`0.32x–87x` faster** (`0.38x–39x` faster on `n-body`, chain depth `9`). Yet statically typed `Grift` still dipped to **`0.49x` of Static Grift** on array-heavy benchmarks due to per-access mutable-array proxy checks.
2. **`racket/racket` Collapsible Contracts (`8ed38e11307b13f25ca67224c66438b83340ae68`, Feltey et al. OOPSLA 2018):**
   - Because arbitrary Racket contracts cannot use pure type-coercion algebra, `racket/collects/racket/contract/private/collapsible-common.rkt` (L52, L66–113, L231–320) delays merging until wrapper depth reaches **`COLLAPSIBLE-LIMIT = 10`**, then switches via `make-enter-collapsible-mode/collapse` to `prop:collapsible-contract` (`try-merge`, `first-order-check-join`) while preserving exact blame order (`collapsible-ho/c`, `collapsible-leaf/c`). `vector.rkt` (L157–258) applies this to `vectorof`/`vector/c` via `impersonator-prop:collapsible`.
   - Even with collapsible contracts, Typed Racket still incurred far higher constant-factor boundary overhead than `Grift` on `sieve`, `ray`, and `n-body` (Kuhlenschmidt et al. 2019 §4.3.3), and eager immutable list traversals remain uncollapsed.

---

### 4. Anatomy of the Sound Gradual Typing Performance Cliff ($2^N$ Lattice Evidence)

Basis: execution/documentation (Takikawa et al. 2016; Greenman & Felleisen 2018; Greenman et al. 2019 JFP; Greenman 2022) + source (`bennn/gtp-benchmarks`) + derived.

#### The $2^N$ Lattice Methodology and Sampling Protocol

Takikawa et al. (POPL 2016 §2) replaced endpoint-only benchmarks (`0...0` vs. `1...1`) with exhaustive measurement of all $2^N$ module-conversion configurations of an $N$-module program, defining:
- **$D$-deliverable** ($N$-deliverable in POPL'16): slowdown $\le D\times$ over fully untyped.
- **$N/M$-usable**: slowdown in $(N\times, M\times]$ (usable for development/testing; POPL'16 used `3x` / `10x`).
- **$L$-step $N/M$-usable**: unacceptable configuration within $\le L$ module annotations of a usable or deliverable one.
- **Linear random sampling (Greenman et al. 2019 JFP §6.1):** For large lattices—verified in `bennn/gtp-benchmarks@f974dcba643880399df9fe643009e9f04dc58f19` across 21 suites, up to `gregor` (13 modules, $8{,}192$ configs) and `quadT`/`quadU` (14 modules, $16{,}384$ configs)—taking **five random samples of $10N$ configurations without replacement** produces tight 95% confidence intervals containing the true cumulative $D$-deliverable curves.

#### Empirical Slowdown Cliffs Across GTP Benchmarks

| Benchmark | Modules ($2^N$) | POPL'16 `%C` (Contract Time) | POPL'16 Dominant Contract Source | ICFP'18 Worst `TR-H` (vs. Erasure) | ICFP'18 Worst `TR-1` (vs. Erasure) | PLDI'22 Worst `Deep` (vs. Untyped) | PLDI'22 Worst `Shallow` | PLDI'22 Worst `D\|\|S` Mix |
| --- | ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| `sieve` | 2 (4) | 92% | 46% HO, 54% `(-> any/c T)` | `21.76x` | `1.69x` | `16x` | `4.36x` | `2.97x` |
| `forth` | 4 (16) | — | — | — | — | **`5,800x`** | `5.51x` | `5.43x` |
| `fsm` | 4 (16) | — | — | **`506.10x`** | `1.21x` | `2.24x` | `2.38x` | `1.91x` |
| `fsmoo` | 4 (16) | — | — | — | — | **`420x`** | `4.28x` | `4.25x` |
| `mbta` | 4 (16) | 39% | 65% library `(-> any/c T)` | — | — | `1.91x` | `1.74x` | `1.71x` |
| `morsecode` | 4 (16) | 29% | 100% `(-> any/c T)` | `2.01x` | **`3.48x`** | `1.57x` | **`2.77x`** | `1.30x` |
| `zombie` | 4 (16) | — | — | **`1,072.80x`** | `20.36x` | `46x` | `31x` | `31x` |
| `dungeon` | 5 (32) | — | — | — | — | **`15,000x`** | `4.97x` | `3.16x` |
| `jpeg` | 5 (32) | — | — | `2.81x` | `1.47x` | `23x` | `1.66x` | `1.56x` |
| `zordoz` | 5 (32) | 95% | 55% HO, 45% lib, 43% pred | — | — | `2.63x` | `2.75x` | `2.58x` |
| `lnm` | 6 (64) | 81% | 99% lib, 91% `(-> T any/c)` | — | — | `1.23x` | `1.21x` | `1.17x` |
| `suffixtree` | 6 (64) | 94% | 98% adaptor, 94% `(-> any/c T)` | `24.59x` | `7.10x` | `31x` | `5.80x` | `5.80x` |
| `kcfa` | 7 (128) | 91% | 100% adaptor, 31% pred | `5.57x` | `1.44x` | `4.33x` | `1.24x` | `1.24x` |
| `snake` | 8 (256) | 98% | 93% adaptor, 49% pred | `13.15x` | `6.72x` | `12x` | `7.67x` | `7.61x` |
| `take5` | 8 (256) | — | — | — | — | `44x` | `2.99x` | `2.97x` |
| `acquire` | 9 (512) | — | — | — | — | `4.22x` | `1.42x` | `1.42x` |
| `tetris` | 9 (512) | 96% | 89% adaptor, 44% pred | `13.93x` | `8.88x` | `13x` | `9.93x` | `5.44x` |
| `synth` | 10 (1,024) | 83% | 90% HO, 51% adaptor | `51.38x` | `2.49x` | `47x` | `4.20x` | `4.20x` |
| `gregor` | 13 (8,192) | 83% | 78% adaptor, 31% pred | — | — | `1.72x` | `1.59x` | `1.51x` |
| `quadT` / `quadU` | 14 (16,384) | 80% | 93% fixed-list validation | — | — | `26x` / `55x` | `7.39x` / `7.57x` | `7.23x` / `7.45x` |

In POPL 2016 (Racket 6.2), worst-case slowdowns spanned `1.25x` (`lnm`) to **`168x` (`tetris`)** (`suffixtree` hit **`105.3x`**; lattice averages spanned `0.6x` to **`68x`**). In JFP 2019 (Racket 6.2–6.4, 20 benchmarks), **14/20 benchmarks** had $\le 50\%$ `2-deliverable` configurations, **10/20** had $\le 50\%$ `10-deliverable`, and **9** exceeded `20x`.

#### Five Root Causes (Why Coercion Collapse Alone Is Insufficient)

1. **Layered Higher-Order Proxy Chains:** Repeated crossings accumulate nested wrappers (`dungeon` `15,000x`, `forth` `5,800x`, `zombie` `1,073x`, `fsm` `506x`, `sieve` `>2,000` depth). Fixed asymptotically by HTF coercions / collapsible contracts.
2. **Eager $O(|\text{container}|)$ Inductive Scans:** Immutable lists (`type-contract.rkt` L583–594 lowers nested `Pair` chains into `list/sc`/`cons/sc`) are re-traversed at every crossing, turning $O(n)$ loops into $O(n^2)$ (`quad` spent **93%** of contract time validating fixed-length lists).
3. **Adaptor-Module & Struct-Predicate Tax:** Splitting struct definitions from hot callers puts contracts on every field accessor and predicate: adaptor contracts drove **100% (`kcfa`), 98% (`suffixtree`), 93% (`snake`), 89% (`tetris`), and 78% (`gregor`)** of contract time, with trivial `(-> any/c boolean?)` predicates averaging **~20%** (up to `49%` in `snake`). Muehlboeck & Tate (2017 §9.3.2) rewrote `snake` to use lazy structs (`Racket*`) and still saw minimal speedup—proving per-call indirection dominated even without eager list scans.
4. **JIT / Optimizer Type-Stability Collapse:** Even depth-1 proxies defeat unboxing and monomorphic inline caches (Static Grift vs. Grift `0.49x` on arrays).
5. **Typed-Calling-Untyped Asymmetry:** In 9 of 12 POPL'16 benchmarks, hot contracts had shape `(-> any/c T)`—typed callers invoking untyped libraries/adaptors, paying wrapper dispatch and return validation on every call.

---

### 5. The Soundness vs. Speed vs. Structural-Flexibility Design Triangle

Basis: normative (Vitousek, Swords & Siek 2017; Muehlboeck & Tate 2017; Greenman & Felleisen 2018; Greenman 2022; Lu et al. 2023) + documentation (Wrigstad et al. 2010; Richards, Zappa Nardelli & Vitek 2015) + source (`racket/typed-racket`, `mvitousek/reticulated`, `Gradual-Typing/Grift`, `facebookincubator/cinderx`).

#### Architectural Comparison Matrix

| Strategy / System | Runtime Mechanism | Mixed Soundness | Complete Monitoring | Blame | Proxy Depth | Fully-Typed Speed | Worst Mixed Cliff | Structural Untyped Interop |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| **Erasure** (`TypeScript`, `mypy`, `typed/racket/optional`) | None (`any/sc`) | No | No | None | `0` | `1.0x` | `1.0x` | Full |
| **Natural (Uncollapsed)** (`Typed Racket` pre-collapse, `Guarded Reticulated`, `Grift` type-based) | Nested chaperone/impersonator proxies + eager inductive checks | Yes | Yes | Exact 2-party | $O(N)$ | Fast (`~0.6–0.9x` TR) | `100x`–`15,000x` | Full (breaks `is` on spartan hosts) |
| **Natural (Collapsed)** (`Grift` coercions/hyper-coercions, `Racket` collapsible) | Normalized coercion AST (`<= 5(2^h-1)`) or lazy merge (`limit=10`) | Yes | Yes | Exact 2-party | $O(1)$ (`<=1` HTF; `<=10` Racket) | OCaml-class (`Grift` `0.49x` on arrays) | `Grift` `0.32–87x` faster on `sieve`; Racket still hits list/adaptor cliffs | Full (needs VM/compiler support) |
| **Transient / Shallow** (`Reticulated Python`, `typed/racket/shallow`) | $O(1)$ top-level shape checks at every typed entry & read; no proxies | Yes (Open-World) | **No** | None or $2N$-party blame maps | `0` | **Linear tax persists** (`2.5x` avg Retic; `TR-1` `morsecode` `3.48x`) | `5.4x` (Retic no blame) / `18x` (blame); `TR Shallow` `1.21–31x` | Full (preserves `is` identity) |
| **Concrete / Nominal** (`Nom`, `Thorn`/`StrongScript`, `Static Python` `chklist`) | Immutable nominal runtime tag at allocation; dual static/dynamic entrypoints | Yes (Nominal) | Immediate accountability | Immediate at cast/write | `0` | **Monotonically faster** (`+3.7%` prod RPS in Static Python) | None (`Nom` flat/improving on `sieve`, `snake`) | **Restricted** (legacy raw lists rejected without conversion) |
| **Multi-Enforcement Hybrids** (`Typed Racket` 3-way; `Static Python` staged) | Per-module / per-type mode selection | Yes (where active) | Per Deep boundary | 2-party (Deep) / local (Shallow) | `0` or $O(1)$ | Best of both | `TR D\|\|S`: `dungeon` `3.16x`, `forth` `5.43x` (`37.5%` median fastest mixed) | Staged (local Shallow $\to$ nonlocal Concrete) |

#### Transient: Open-World Soundness on Spartan Hosts vs. Collaborative Blame

Vitousek, Swords & Siek (POPL 2017) proved that Guarded proxies fail **open-world soundness** on a **spartan host** (unmodified CPython lacking native chaperones): proxies break `isinstance`, C-API checks, and pointer identity (`is`), while arbitrary untyped code bypasses wrappers. Transient (`mvitousek/reticulated@5cd2d10e0f92505a9db2bc573d8c23360ef6548b`) solves this without proxies:
- `retic/transient.py` (L37–70, `__retic_check__`) checks only top-level tags (`callable(val)`, `isinstance(val, list)`). `retic/blame_inserter.py` (L8–34, `generateArgumentProtectors`) inserts argument guards at typed function entries and elimination sites—mirroring Typed Racket's Shallow pass (`typed-racket-lib/typed-racket/private/shallow-rewrite.rkt` L65–225, `protect-domain`, and `utils/shallow-contract.rkt` L65–71, `shallow-shape-check`).
- **Collaborative blame:** Because Transient has no wrappers, Vitousek et al. track cast history in a runtime blame map. Direct audit of `retic/opt_blame_transient.py` (L62–72, L83–135, L223–268) shows `add_cast` attaches `__retic_casts__` and `__retic_pointers__` directly onto objects and walks pointer edges in `collectblame()`, silently catching `AttributeError: pass` on CPython built-ins that forbid attribute assignment (earlier `archive/retic/mgd_transient.py` L72–90 used an external `castdata` map with `weakref.ref`, skipping primitives in `do_not_track`).
- **Measured cost (Vitousek et al. 2017 §6.2; Greenman & Felleisen 2018):** Across 13 Python 3.4 benchmarks, blame-free Transient averaged **`2.5x`** slowdown (best `1.0x`, worst **`5.4x`**—all `3/10-usable`); enabling collaborative blame added up to `4x` on top (worst **`18x`** over untyped Python). Because typed code never trusts incoming containers deeply, fully typed code keeps paying linear checks (`morsecode`: `TR-1` `3.48x` > `TR-H` `2.01x` in ICFP'18).

#### Concrete / Nominal Soundness: Zero Proxies at the Cost of Nonlocal Refactoring

Building on Thorn's like/concrete types (Wrigstad et al. POPL 2010, DOI `10.1145/1706299.1706343`) and StrongScript (Richards, Zappa Nardelli & Vitek ECOOP 2015, DOI `10.4230/LIPIcs.ECOOP.2015.76`), Muehlboeck & Tate (OOPSLA 2017) co-designed `Nom` so every heap value carries its exact nominal class/interface tag from creation:
- Crossing untyped $\to$ typed requires one **$O(1)$ nominal subtype test**—no proxy allocation, no container scan, and zero per-read field checks in typed code. On `sieve`, `snake`, and five Python benchmarks from Vitousek et al. (including `pystone`, `float`, `go`, and `spectralnorm`), `Nom` avoided mixed-configuration cliffs and sped up monotonically as types were added.
- **Production verification in `facebookincubator/cinderx@8ff26422ae5657cbcc9bc976c0695ab54cf861c1` (`Static Python`, Lu et al. 2023):** `cinderx/StaticPython/checked_list.c` implements nominal checked containers (`chklist[T]`) via **dual entrypoints**:
  - `chklist_append` (L3207–3223): statically typed callers execute the unchecked C fast path (`Ci_CheckedList_SET_ITEM(self, n, value)`).
  - `chklist_append_wrapper` (L3225–3234, exposed to Python in `chklist_methods` at L3551–3554): dynamic callers check the incoming element against the container's runtime type parameter via `_PyClassLoader_CheckOneArg((PyObject*)self, value, "append", 0, &Ci_Py_Sig_T0)` before delegating to `chklist_append`.
  - `Ci_CheckedList_TypeCheck` (L3315–3318) verifies nominal container identity in $O(1)$ via `_PyClassLoader_GetGenericTypeDefFromType(type)`.
- **Trade-off:** Migrating hundreds of modules (dozens using concrete containers and unboxed primitives) in Instagram's production server increased max-CPU throughput by **`+3.7%` requests/sec** (Lu et al. 2023 §1, §6), yet raw untyped Python `list` instances cannot enter `chklist[T]` parameters without explicit copying or nonlocal allocation-site changes.

#### Multi-Enforcement Hybrids: Deep + Shallow + Optional

Typed Racket (`racket/typed-racket@7fe7e11fae2b04e04525d63b01b33efe5ffad075`, `type-contract.rkt` L332–378; Greenman PLDI 2022) dispatches contract lowering per module across `deep`, `shallow`, and `optional` (`any/sc`):
```racket
(define (type->static-contract type init-fail
                               #:typed-side [typed-side #t]
                               #:enforcement-mode [te-mode (current-type-enforcement-mode)])
  (case te-mode
    [(shallow)  (type->static-contract/shallow type #:typed-side typed-side)]
    [(optional) any/sc]
    [else       (type->static-contract/deep type init-fail #:typed-side typed-side)]))
```
Deep modules still wrap values crossing to/from Shallow modules—preserving *Deep Label Consistency* (Complete Monitoring for Deep modules)—while Shallow $\leftrightarrow$ Untyped boundaries emit only flat checks (`kind = 'flat` at L343). Across 16 GTP benchmarks (Greenman 2022 Tables 1–2), a **median `37.5%`** of $2^N$ configurations ran fastest with a Deep+Shallow mix (`66%` in `lnm`, `64%` in `acquire`, `62%` in `tetris`); toggling one bridge module in `MsgPack.rkt` to Shallow cut test time by **`40%`** (`320s -> 204s`), and switching `synth`'s math library to Shallow cut untyped-client overhead from `14x` to `5x`.

---

### 6. Executable Verification Probe Results: Blame, Collapse, and $2^4$ Lattice Scaling

Basis: execution (`support/verify_gradual_semantics_and_cliffs.py`, Python 3.10+ stdlib only, exit `0`).

Running `python3 -B support/verify_gradual_semantics_and_cliffs.py --verbose` verifies all five modeled semantics over higher-order callbacks and mutable arrays:

1. **Type Relations & Factorizations (27 types up to depth 2, 729 ordered pairs):** Siek & Taha Prop 1 (reflexive, symmetric, non-transitive: `Int ~ Dyn`, `Dyn ~ Bool`, `¬(Int ~ Bool)`) and Wadler & Findler Props 8–9 ($S <: T \iff S <:+ T \land S <:^- T$; $S <:^n T \iff S <:+ T \land T <:^- S$) verified exhaustively.
2. **Blame Polarity (5 scenarios):** First-order downcast (`positive:untyped_provider`), contravariant 1st-order call (`untyped_caller`), double-contravariant 2nd-order callback (`untyped_caller`), mutable array write polarity reversal (`untyped_mutator`), and mutable array read (`untyped_owner`) all match Wadler–Findler and Strickland et al.
3. **Complete Monitoring, Early Error Detection & Concrete Restriction:** Clickable-Plot channel yields `CAUGHT(untyped_lib)` under `Natural` vs. `UNCHECKED_CHANNEL(received:str)` under `Transient`; `(Int -> Int) => Dyn => (Bool -> Int)` collapses to `CFn(dom=CFail(...), cod=CId())` before call (HTF §7); `Concrete` rejects raw untyped `RawArray` (`REJECTED_RAW_UNTYPED_LIST`).
4. **HTF $O(1)$ Collapse vs. Uncollapsed Natural ($N$ round-trips across `Int->Int <=> Dyn`, `Ref[Int] <=> Dyn`, and persistent `Dyn->Int <=> Dyn`):**

| Round-Trips ($N$) | `Natural-Uncollapsed` Depth | `Natural-Collapsed` Depth | `Natural-Uncollapsed` Post-Loop Hops | `Natural-Collapsed` Post-Loop Hops | HTF Max Coercion Size (Lemma 2 Cap $h=2$: `15`) |
| ---: | ---: | ---: | ---: | ---: | ---: |
| `10` | `20` | `1` | `80` | `1` | `3` |
| `50` | `100` | `1` | `400` | `1` | `3` |
| `200` | `400` | `1` | `1,600` | `1` | `3` |
| `1,000` | `2,000` | `1` | `8,000` | `1` | `3` |

*(Recursive `NaturalFnProxy.__call__` hits Python's `RecursionError` at $N=1{,}000$, reproducing HTF's stack-overflow leak; iterative chain unwinding isolates the exact $8N$ hop count.)*

5. **Full $2^4$ (16-Config) Mixed-Typed Lattice (`rounds=24`, `arr_len=8`, metric = `proxy_hops + tag_checks + boundary_casts`):**

| Semantics | `0000` (Untyped) | `1111` (Typed) | Max Mixed Ops (Worst Config) | Max Proxy Depth | Catches Injected Fault (`0111`)? |
| --- | ---: | ---: | ---: | ---: | --- |
| `Erasure` | `0` | `0` | `0` | `0` | **No** (`UNSOUND_CORRUPTED('BAD')`) |
| `Natural-Uncollapsed` | `0` | `0` | **`12,820`** (`0011`, `1100`) | **`97`** | Yes (`BlameError`) |
| `Natural-Collapsed` (HTF) | `0` | `0` | `472` (`0100`) | `1` | Yes (`BlameError`) |
| `Transient` | `0` | **`176`** | `224` (`1011`) | `0` | Yes (`RuntimeTagError`) |
| `Concrete` | `56` | **`8`** | `152` (`0100`, `1100`) | `0` | At allocation / dynamic write |

Toggling a single module from `0111` (`244` ops, depth `1`, boundary outside the loop) to `0011` (`12,820` ops, depth `97`, boundary inside the loop) triggers a **`52.5x`** cliff under `Natural-Uncollapsed`; `Natural-Collapsed` reduces `0011` by **`30.0x`** (`428` ops, depth `1`), `Transient` eliminates the cliff but pays `176` ops at `1111`, and `Concrete` drops monotonically from `56` (`0000`) to `8` (`1111`).

---

### 7. Engineering Design Rules for Interoperability Boundaries

Basis: derived (from primary papers, source audits, and probe execution).

1. **Co-Locate Data Definitions with Hot Accessors—Never Split Them Across a Deep Boundary:** Adaptor boundaries drove `89%–100%` of contract overhead in `tetris`, `snake`, `suffixtree`, and `kcfa` (and `52.5x` in our probe). Migrate data definitions together with core accessors, or place a Shallow bridge module in between during migration.
2. **Require Coercion Collapse and Coercion-Passing Tail Calls Whenever Proxies Are Used:** Any proxy-based gradual or FFI monitor must eagerly normalize stacked wrappers (HTF/hyper-coercions or collapsible merging) and pass continuation coercions through tail calls to preserve $O(1)$ stack and heap bounds.
3. **Eliminate Eager $O(|\text{container}|)$ Scans on Hot Immutable Collections:** Re-traversing immutable lists across boundaries turns $O(n)$ loops into $O(n^2)$ (`quad`: `93%` of contract time). Use nominal validated containers (`chklist` or owned FFI buffers validated once), lazy shallow element checks, or coarse batch boundaries.
4. **Select Enforcement Mode by Host Capability and Assurance Need:** On **spartan hosts** (CPython, JS VMs, C ABI), avoid transparent proxies; choose **Transient** for drop-in structural migration or **Concrete nominal types** for monotonic speedups where allocation sites can be updated. Where **Complete Monitoring** and 2-party blame are required (untrusted callbacks across verified APIs), enforce **Deep** contracts at coarse boundaries.
5. **Align Runtime Contracts with Static Verification Specifications:** When migrating foreign code from runtime checks toward formal proof (connecting to static VC architectures in `dafny-boogie-viper-fstar-why3-and-vc-obligation-architectures`), keep boundary invariants in a decidable first-order/nominal subset so the verified side discharges them statically via SMT/WP while the unverified boundary executes the exact same predicate as an $O(1)$ runtime guard.

## Boundaries

- **not examined:**
  - **Gradual Dependent Types (GCIC / "Fire Triangle"):** Tension among dependent types, strong normalization, type safety, and the gradual guarantee was not examined.
  - **Polymorphic Blame & Gradual Parametricity:** Dynamic sealing protocols for enforcing relational parametricity across polymorphic boundaries were not examined.
  - **Gradual Verification & Separation-Logic Ownership:** Runtime ownership tracking for imprecise separation-logic formulas (e.g., Gradual C0 / Gradual Viper) was not examined directly; consult `dafny-boogie-viper-fstar-why3-and-vc-obligation-architectures` for static VC-obligation architectures.
  - **Tracing-JIT Contract Elimination:** Meta-tracing JIT systems (`Pycket`, `Graal`/`Grace`, `HiggsCheck`) were noted only from secondary commentary in Lu et al. (2023 §7); their source code and benchmarks were not audited.
- **unknown:**
  - **Eliminability of Residual Mutable-Array Proxy Checks Under Structural Deep Soundness:** Whether compiler/JIT specialization can eliminate the `0.49x` array-proxy slowdown observed in statically typed `Grift` (Kuhlenschmidt et al. 2019 §4.3.1) without adopting monotonic or nominal heap representations remains unresolved.
  - **Mixed-Configuration Cliffs in Production Static Python:** Lu et al. (2023 §6.4 Threat to Validity) did not evaluate mixed typed/untyped $2^N$ lattices; whether pathological mixed-typed cliffs exist outside Instagram's migrated modules is unknown.
- **known not to apply:**
  - **Erasure** (`TypeScript`, `mypy`, `typed/racket/optional`) does not provide mixed-typed soundness, Blame Theorem guarantees, or Complete Monitoring.
  - **Transient / Shallow** (`Reticulated Python`, `typed/racket/shallow`) does not satisfy Complete Monitoring (`Greenman et al. 2019`; verified by `support/verify_gradual_semantics_and_cliffs.py`).
  - **Concrete / Nominal** (`Nom`, `CinderX Static Python` `chklist`) does not satisfy the full structural Gradual Guarantee over unmodified untyped collections without nonlocal refactoring or copying.
  - **Space-Efficient Coercions / Collapsible Contracts** do not eliminate $O(|\text{container}|)$ eager scans over immutable lists or flat struct-predicate adaptor overhead.
- **unsupported:**
  - **`racket/typed-racket` (`7fe7e11fae2b04e04525d63b01b33efe5ffad075`):** `type-contract.rkt` explicitly rejects proposition contract generation for non-flat types in Deep (L407–412) and Shallow (L806–814) modes, and rejects negative-position `Self` contracts (L606–608).
  - **`mvitousek/reticulated` (`5cd2d10e0f92505a9db2bc573d8c23360ef6548b`):** `retic/opt_blame_transient.py` (L62–72, L83–135) silently skips `AttributeError` when attaching `__retic_casts__`/`__retic_pointers__`, leaving CPython immutable built-ins without `__dict__` unsupported for blame tracking in that module.
  - **`facebookincubator/cinderx` Static Python (`Lu et al. 2023 §8`):** Higher-order function types are omitted from Static Python's sound static subset.

## Evidence

### Primary Publications Examined (16 Subjects in `REPORT.json`, Observed `2026-11-19`)

| Subject | Role | Verified Coordinates & Extracted Basis |
| --- | --- | --- |
| Siek & Taha (2006) | `normative` | *Gradual Typing for Functional Languages*, Scheme Workshop 2006, pp. 81–92 (`https://jsiek.github.io/home/siek06gradual.pdf`). Prop 1 (`~`), Lemmas 3–5/8, Thms 1–2. |
| Matthews & Findler (2007) | `normative` | *Operational Semantics for Multi-Language Programs*, POPL '07, pp. 3–10, DOI `10.1145/1190216.1190220`. Natural vs. lump boundaries. |
| Wadler & Findler (2009) | `normative` | *Well-Typed Programs Can't Be Blamed*, ESOP '09, LNCS 5502, pp. 1–16, DOI `10.1007/978-3-642-00590-9_1`. Props 8–10, Blame Theorem. |
| Herman, Tomb & Flanagan (2010) | `normative` | *Space-Efficient Gradual Typing*, HOSC 23(2), pp. 167–189, DOI `10.1007/s10990-011-9066-z`. Lemma 2, Thms 3–4, §7 early error detection. |
| Strickland et al. (2012) | `normative` | *Chaperones and Impersonators: Run-Time Support for Reasonable Interposition*, OOPSLA '12, pp. 943–962, DOI `10.1145/2384616.2384685`. Chaperone invariant & mutable polarity. |
| Siek et al. (2015) | `normative` | *Refined Criteria for Gradual Typing*, SNAPL '15, LIPIcs 32, pp. 274–293, DOI `10.4230/LIPIcs.SNAPL.2015.274`. Thm 5 (Gradual Guarantee), §5.2 `Ref` invariance. |
| Takikawa et al. (2016) | `execution` | *Is Sound Gradual Typing Dead?*, POPL '16, pp. 456–468, DOI `10.1145/2837614.2837630`. $2^N$ lattice metrics, 12 benchmarks (`1.25x`–`168x`), Fig. 6 profiling. |
| Vitousek, Swords & Siek (2017) | `normative` / `execution` | *Big Types in Little Runtime*, POPL '17, pp. 762–774, DOI `10.1145/3009837.3009849`. Open-world soundness, blame maps, 13 Python benchmarks (`2.5x` avg / `5.4x` worst; `<=18x` blame). |
| Muehlboeck & Tate (2017) | `normative` / `execution` | *Sound Gradual Typing is Nominally Alive and Well*, PACMPL 1(OOPSLA), Art. 56, DOI `10.1145/3133880`. `Nom` nominal tags, `sieve`/`snake`/`Racket*`/Python benchmarks. |
| Greenman & Felleisen (2018) | `normative` / `execution` | *A Spectrum of Type Soundness and Performance*, PACMPL 2(ICFP), Art. 71, DOI `10.1145/3236766`. `TR-H`/`TR-1`/`TR-E` models, Fig. 11 worst-case table. |
| Feltey et al. (2018) | `documentation` | *Collapsible Contracts: Fixing a Pathology of Gradual Typing*, PACMPL 2(OOPSLA), Art. 133, DOI `10.1145/3276503`. Deferred merging preserving blame order. |
| Greenman et al. (2019) | `execution` | *How to Evaluate the Performance of Gradual Type Systems*, JFP 29, e4, DOI `10.1017/S0956796818000217`. 20 benchmarks (Racket 6.2–6.4), 5-sample $10N$ protocol, §8 taxonomy. |
| Greenman, Felleisen & Dimoulas (2019) | `normative` | *Complete Monitors for Gradual Types*, PACMPL 3(OOPSLA), Art. 122, DOI `10.1145/3360548` (and author extended abstract at `https://prl.khoury.northeastern.edu/blog/2019/10/31/complete-monitors-for-gradual-types/`). Unique ownership, Clickable Plot, 2-party vs. $2N$-party blame. |
| Kuhlenschmidt, Almahallawi & Siek (2019) | `execution` | *Toward Efficient Gradual Typing for Structural Types via Coercions*, PLDI '19, pp. 517–532, DOI `10.1145/3314221.3314627`. `Grift` coercions `0.32x–87x` faster on `sieve`, static `Grift` `0.49x` on arrays. |
| Greenman (2022) | `normative` / `execution` | *Deep and Shallow Types for Gradual Languages*, PLDI '22, pp. 580–593, DOI `10.1145/3519939.3523430`. 3-way Deep/Shallow/Untyped semantics, Tables 1–2 (`dungeon` `15,000x -> 3.16x`). |
| Lu et al. (2023) | `normative` / `execution` | *Gradual Soundness: Lessons from Static Python*, Programming 7(1), Art. 2, DOI `10.22152/programming-journal.org/2023/7/2`. Shallow $\to$ Concrete $\to$ Primitive staging, Instagram `+3.7%` RPS. |

*Secondary cited context (bibliographic coordinates verified via DOI lookup; full PDFs not extracted):* Wrigstad et al. (POPL 2010, DOI `10.1145/1706299.1706343`, Thorn like types); Siek & Wadler (POPL 2010, DOI `10.1145/1707801.1706342`, Threesomes); Richards, Zappa Nardelli & Vitek (ECOOP 2015, DOI `10.4230/LIPIcs.ECOOP.2015.76`, StrongScript).

### Upstream Git Source Inspections (6 Subjects in `REPORT.json`, Observed `2026-11-19`)

| Repository | Pinned Commit SHA | Inspected Paths, Symbols & Line Ranges |
| --- | --- | --- |
| `racket/typed-racket` | `7fe7e11fae2b04e04525d63b01b33efe5ffad075` | `typed-racket-lib/typed-racket/private/type-contract.rkt` L271–289, L332–378 (`type->contract`, `type->static-contract`), L404–418 & L798–837 (`type->static-contract/shallow`), L577–594 (`Mutable-Vector:` `t->sc/both`, `Pair:`), L603–609; `private/shallow-rewrite.rkt` L65–225 (`shallow-rewrite-top`, `protect-domain`); `utils/shallow-contract.rkt` L65–71 (`shallow-shape-check`). |
| `racket/racket` | `8ed38e11307b13f25ca67224c66438b83340ae68` | `racket/collects/racket/contract/private/collapsible-common.rkt` L52 (`COLLAPSIBLE-LIMIT = 10`), L66–113, L231–320 (`merge`, `first-order-check-join`, `make-enter-collapsible-mode/collapse`); `vector.rkt` L157–258 (`vectorof-collapsible-late-neg-ho-projection`). |
| `mvitousek/reticulated` | `5cd2d10e0f92505a9db2bc573d8c23360ef6548b` | `retic/transient.py` L37–70 (`__retic_check__`); `retic/blame_inserter.py` L8–34; `retic/opt_blame_transient.py` L8–135 & L220–268 (`add_cast`, `collectblame`); `archive/retic/guarded.py` L44–163; `archive/retic/monotonic.py` L25–171; `archive/retic/mgd_transient.py` L10–90. |
| `Gradual-Typing/Grift` | `5fa76f837a0d6189332343d7aa899892b3c49583` | `src/casts/interpret-casts-with-coercions.rkt` L57–164, L860–904 (`make-compose-coercions`); `interpret-casts-with-hyper-coercions.rkt` L43–87, L220–265; `coercion-passing.rkt` L17–95; `src/backend/runtime/suspended_cast.h` L6–9. |
| `facebookincubator/cinderx` | `8ff26422ae5657cbcc9bc976c0695ab54cf861c1` | `cinderx/StaticPython/checked_list.c` L3207–3234 (`chklist_append`, `chklist_append_wrapper`), L3315–3318 (`Ci_CheckedList_TypeCheck`), L3524–3554 (`Ci_PyTypedMethodDef`, `chklist_methods`). |
| `bennn/gtp-benchmarks` | `f974dcba643880399df9fe643009e9f04dc58f19` | `README.md` and `benchmarks/*/untyped/*.rkt` across all 21 suites (`sieve` 2 modules through `quadT`/`quadU` 14 modules). |

### Local Executable Probe (Observed `2026-11-19`)

- **Script:** `support/verify_gradual_semantics_and_cliffs.py` (Python 3.10+ stdlib only).
- **Command:** `python3 -B reports/gradual-typing-sound-interoperability-and-blame-performance-cliffs/support/verify_gradual_semantics_and_cliffs.py --verbose`
- **Result:** Exit `0` (`ALL ASSERTIONS PASSED`): verified 729 type-relation pairs, 5 blame-polarity scenarios, HTF $O(1)$ collapse (`depth=1`, `size=3` vs. `depth=2,000`, `hops=8,000` at $N=1{,}000$), Complete Monitoring separation, and all 16 configurations of the $2^4$ mixed-typed lattice.

## Revalidation

1. **Rerun the Executable Model Probe (seconds, stdlib-only):**
   ```console
   python3 -B reports/gradual-typing-sound-interoperability-and-blame-performance-cliffs/support/verify_gradual_semantics_and_cliffs.py --verbose
   ```
   Re-verifies formal type relations, blame polarities, HTF Lemma 2 bounds, Complete Monitoring separation, and $2^4$ scaling ratios; does not measure native JIT timings on upstream runtimes.
2. **Diff Targeted Upstream Files Against Pinned Commits:**
   - `racket/typed-racket` (`7fe7e11fae2b04e04525d63b01b33efe5ffad075`): diff `typed-racket-lib/typed-racket/private/{type-contract,shallow-rewrite}.rkt` for new enforcement modes, lazy list contracts, or relaxed non-flat proposition restrictions.
   - `racket/racket` (`8ed38e11307b13f25ca67224c66438b83340ae68`): diff `racket/collects/racket/contract/private/{collapsible-common,vector}.rkt` for `COLLAPSIBLE-LIMIT` or merge-rule changes.
   - `facebookincubator/cinderx` (`8ff26422ae5657cbcc9bc976c0695ab54cf861c1`): diff `cinderx/StaticPython/checked_list.c` and Static Python's type checker for higher-order callable types or automatic `list -> chklist` conversion.
3. **Full Empirical Lattice Check:** On newer Racket or gradual-compiler releases, execute `raco gtp-measure` against `bennn/gtp-benchmarks` (using the 5-sample $10N$ sampling protocol for $N \ge 10$) and inspect cumulative `D-deliverable` curves; endpoint-only (`0...0` vs. `1...1`) timings cannot detect mixed-configuration cliffs.
