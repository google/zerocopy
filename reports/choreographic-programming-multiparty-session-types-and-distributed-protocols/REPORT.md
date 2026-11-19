# Choreographic Programming, Multiparty Session Types, and Monotonic Distributed Protocols

## Summary

Static distributed-protocol verification spans three complementary paradigms, each delivering strong correctness guarantees only inside sharp theoretical and operational boundaries:

1. **Choreographic Programming (`Pirouette`, `Choral`, `HasChor`, `MultiChor`, `Kalas`)** synthesizes deadlock-free per-node implementations from one global program via Endpoint Projection (`EPP`), but guarantees deadlock-freedom **only inside a closed world** where all roles are projected from the same choreography and every role whose behavior diverges on a branch learns the decision (**Knowledge of Choice, `KoC`**). Compiler-based languages (`Pirouette`, `Choral`) enforce `KoC` via a partial merge operator ($\sqcup$) over incoming label selections (`allow`/`switch`), rejecting unnotified divergence at compile time (`Choral` also includes optional `MoveMeant` selection inference). Library embeddings avoid custom compilers by interpreting a freer monad: `HasChor` broadcasts every conditional scrutinee to all configured nodes (`Cond`), while `MultiChor` scopes broadcasts to a census-indexed `Conclave`.
2. **Multiparty Session Types (`MPST`)** suffered published soundness flaws when unconstrained full-merge global projection was combined with subtyping. **Scalas & Yoshida (POPL 2019)** proved that classical pairwise-consistency invariants break under reduction, replacing syntactic global projection and binary duality with direct behavioral verification of local-type contexts via modal $\mu$-calculus (`alcestes/mpstk` + mCRL2) along a strict 5-tier hierarchy (`safe` $\supsetneq$ `deadlock-free` $\supsetneq$ `live` $\supsetneq$ `live+` $\supsetneq$ `live++`). Independently, **Lange & Yoshida (FoSSaCS 2017)** and **Bravetti, Carbone & Zavattaro (2017)** proved that **asynchronous FIFO session subtyping is undecidable** even for two parties, whereas **synchronous** session subtyping remains decidable over regular trees.
3. **Partial Failure & Impossibility Boundaries:** Standard choreographies and classic MPST assume reliable, crash-free channels. Under asynchronous networks with unannounced crashes or partitions, **FLP (1985)** and **CAP (2002)** bar deterministic consensus and simultaneous linearizability/availability. **Crash-Stop Generalized MPST (Barwell et al., CONCUR 2022)** adds `stop`, reliable-role sets $\mathcal{R}$, and `crash` branches under a *crash-fail* model that circumvents FLP only by assuming an **accurate failure detector**, at steep verification cost (a 2-role DNS protocol expands from 10 states / 15 transitions to 101 states / 427 transitions with failover).
4. **Monotonic Dataflow & CRDTs (`CALM`, `Bloom`/`Dedalus`, `Hydro`):** By the **CALM Theorem (Ameloot et al. 2013; Hellerstein & Alvaro 2020)**, a program has a confluent, coordination-free distributed implementation **if and only if** it is logically monotonic. Join-semilattice CRDTs operationalize CALM via associative, commutative, idempotent (ACI) merges, though convergence does not preserve non-$\mathcal{I}$-confluent application invariants. In Rust, `hydro-project/hydro` statically types `Stream<T, L, B, O, R>` across location (`Tick`/`Atomic`), boundedness, ordering, and retries, pairing `NonDet<H>` guards with `ManualProof` or Verus-verified closure proofs (`VerusCommutativeProof`, `VerusIdempotentProof`)—subject to the critical operational boundary that `cargo build` erases `Verus*Proof` markers unless `cargo verus verify` runs, and Hydro's simulator does not inject retries.
5. **Open-World Rolling Upgrades:** Mixed-version clusters break closed-label session duality. Empirical analysis of 123 distributed upgrade failures (`DUPTester`, SOSP 2021) found 38% Blocker severity and over 800 cross-version format incompatibilities. Open wire encodings like Protocol Buffers survive mixed-version proxies through tag-value framing and unknown-field round-tripping (dropped in early proto3, restored in v3.5.0, still lost across JSON or manual field copying).

| Paradigm | Core Guarantee | Branching / Coordination | Failure & Upgrade Model | Decidability / Cost | Key Artifacts |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Choreographic Programming** | Deadlock-freedom & mismatch-freedom by construction | Explicit select + partial merge $\sqcup$ (`Pirouette`, `Choral`), global broadcast (`HasChor`), scoped `Conclave` (`MultiChor`) | Closed-world, crash-free reliable channels | EPP linear in AST; optional `MoveMeant` inference | `Pirouette` (Coq), `Choral`, `HasChor`, `MultiChor`, `Kalas` |
| **Generalized MPST** | Parametric typing: `safe`, `df`, `live`, `live+`, `live++` | Local-type context LTS + modal $\mu$-calculus (global types optional) | Reliable by default; Crash-Stop adds `stop`, $\mathcal{R}$, `crash` + accurate detector | Finite sync LTS decidable (exp. in roles/crashes); async subtyping **undecidable** | Scalas & Yoshida (2019), `alcestes/mpstk`, Barwell et al. (2022) |
| **Separation-Logic Protocols** | Functional correctness + heap ownership + protocol safety | Dependent separation protocols (`Actris`) in `Iris` | Async FIFO + higher-order mutable state & locks | Interactive mechanized Coq proofs | `Actris` (POPL 2020), `Iris` |
| **Monotonic Dataflow & CRDTs** | Coordination-free confluence (order/duplicate invariance) | Join-semilattice merges (ACI), `Ordering`/`Retries`/`Boundedness` types, `Tick`/`NonDet` barriers | Partition-tolerant, out-of-order, at-least-once; non-monotone invariants need barriers | Arbitrary host monotonicity **undecidable**; finite tests or Verus per closure | CALM, `Bloom`/`Dedalus`, `hydro-project/hydro` |

## Applicability

This report covers fourteen primary subjects recorded in `REPORT.json`, pairing foundational peer-reviewed specifications with pinned upstream implementations:

- **Choreographic languages & compilers:** *Pirouette* (POPL 2022, mechanized Coq semantics), *Choral* (TOPLAS 2024 + `choral-lang/choral` at `a644dbd4429f2d609b2ca280a064bab9d73fab34`), *HasChor* (ICFP 2023 + `gshen42/HasChor` at `e6bf3d5e771e309ba8db7f2e55822f6a11c1e237`), and *MultiChor* (`ShapeOfMatter/MultiChor` at `4b83cad1b2374dbf4907ccce48a65fa403936dab`). Comparing these four isolates the trade-off between standalone partial-merge compilers and freer-monad library embeddings.
- **MPST, subtyping undecidability, and crash-stop semantics:** Scalas & Yoshida (POPL 2019) paired with its reference toolkit (`alcestes/mpstk` at `5a056cc2193c2c588c1c7ddf130176c3aacdf38e`), the two simultaneous undecidability proofs of asynchronous session subtyping (Lange & Yoshida, FoSSaCS 2017; Bravetti, Carbone & Zavattaro, *Inf. & Comp.* 2017), and Crash-Stop Generalized MPST (Barwell et al., CONCUR 2022).
- **Monotonic dataflow, lattices, and open-wire evolution:** Hellerstein & Alvaro (CACM 2020) paired with Rust's Hydro stack (`hydro-project/hydro` at `fbaccddb35111327f96922259d60dc1607395545`: `lattices` and `hydro_lang`), and Protocol Buffers field presence/wire rules (`protocolbuffers/protobuf` at `caaf86620a4ea6363bb1cf43c50dc430725c39dd`, `docs/field_presence.md`) paired with empirical rolling-upgrade failure data (DUPTester, SOSP 2021).
- **Executable probe:** `support/verify_epp_mpst_and_calm.py` implements and mechanically executes finite-instance `EPP`/merge + FIFO simulation, sync/async/crash-stop MPST modal $\mu$-calculus checks, synchronous subtyping vs. send-anticipation, semilattice ACI tests, CALM delivery-order confluence, and Protobuf unknown-field round-tripping.
- **Adjacent corpus packages (cross-referenced, not duplicated here):** Consensus/distributed-system verifiers (`Verdi`, `IronFleet`, `Ivy`, `Aneris`, `Chapar`, `TLAPS`, `FoundationDB`, `Jepsen`/`Elle`) and incremental view maintenance (`DBSP`) are documented in `anneal-databases-networking-cloud-builds-and-tensor-survey`. Concurrent separation logic foundations (`Iris` 3.1, adequacy, transfinite liveness, and Lean 4 mechanization) underlying `Actris` are documented in `iris-adequacy-transfinite-liveness-simuliris-and-lean-separation-logic`.

## Findings

### 1. Choreographic Programming, Endpoint Projection (EPP), and Knowledge of Choice

Basis: normative (Pirouette POPL 2022, Choral TOPLAS 2024, HasChor ICFP 2023) + source (`choral-lang/choral`, `gshen42/HasChor`, `ShapeOfMatter/MultiChor`) + execution (`support/verify_epp_mpst_and_calm.py`)

Choreographic programming encodes an entire distributed protocol as a single global program with role-annotated values and communications (`Alice.x ~> Bob.y`). **Endpoint Projection (`EPP`)** compiles that program into one local endpoint per role so every `send` is structurally paired with a matching `recv`. Sound and complete `EPP` yields **deadlock-freedom by construction** and **communication-mismatch freedom** without manual session-type dualization.

#### 1.1 Knowledge of Choice (`KoC`) and Partial Merge ($\sqcup$)

Compositional `EPP` breaks down on local conditionals whenever an uninvolved role's continuation differs between branches:

```text
if Alice.cond then Bob.m1 ~> Carol.x else Bob.m2 ~> Carol.x
```

`Alice` evaluates `cond` locally, but `Bob` and `Carol` do not possess `Alice.cond` and therefore cannot locally choose between sending/receiving `m1` versus `m2`. Projection is **undefined** unless either (a) every uninformed role's projected branches merge identically up to the point of divergence, or (b) an informed role transmits an explicit **selection label** (`Alice[L] ~> Bob`) before behavior diverges.

To project conditionals compositionally while permitting shared prefixes before notification, compiler-based choreographies define a **partial merge operator** ($\sqcup$) over projected endpoints. In **Pirouette** (§5.2, Fig. 9), projecting `ℓ1 [L] ⇝ ℓ2; C` onto `ℓ2` yields a single-branch offer `allow ℓ1 choice | L ⇒ [C]_ℓ2`. Projecting `if ℓ1.e then C1 else C2` onto any role `ℓ ≠ ℓ1` computes `[C1]_ℓ ⊔ [C2]_ℓ`:

```text
allow ℓ choice | L ⇒ E1  ⊔  allow ℓ choice | L ⇒ E2        ≜  allow ℓ choice | L ⇒ (E1 ⊔ E2)
allow ℓ choice | L ⇒ E1  ⊔  allow ℓ choice | R ⇒ E2        ≜  allow ℓ choice | L ⇒ E1 | R ⇒ E2
allow ℓ choice | L ⇒ E1  ⊔  allow ℓ choice | L ⇒ E2,1 | R ⇒ E2,2
                                                           ≜  allow ℓ choice | L ⇒ (E1 ⊔ E2,1) | R ⇒ E2,2
```

Identical non-choice prefixes merge homomorphically—e.g., Pirouette §5.2's `if ℓ1.e then ℓ2.3 ⇝ ℓ1.x; ℓ1 [L] ⇝ ℓ2; ℓ2.0 else ℓ2.3 ⇝ ℓ1.x; ℓ1 [R] ⇝ ℓ2; ℓ2.1` projects `ℓ2` to `send 3 to ℓ1; allow ℓ1 choice | L ⇒ ret(0) | R ⇒ ret(1)`. Any incompatible divergence (distinct sends, send vs. termination, or offers from distinct senders) leaves `E1 ⊔ E2` undefined (`↑`), failing compilation with the offending role.

#### 1.2 Pirouette: Coq-Mechanized Higher-Order Functional Choreographies

Hirsch & Garg (POPL 2022) formalize **Pirouette** generically over an arbitrary local expression language (parameterized in Coq via de Bruijn indices and explicit substitution axioms for intensional type theory):

- **Lifted Type Soundness (Thms 1–3, Cor. 1):** Local Preservation lifts to choreographic Relative Preservation; local Progress + Boolean Invertability lift to Relative Progress. Choreography Equivalence ($\equiv$) respects types (Thm 3, requiring unique local expression types for `SwapSendIf`).
- **Out-of-Order Execution with Block Sets:** Transitions $C_1 \xRightarrow{R, B}_c C_2$ track redex $R$ and blocked locations $B$, permitting independent remote locations to step out of syntactic order while forbidding reductions across both branches of an unevaluated `if` (Thm 5 proves defining semantics purely modulo $\equiv$ is strictly weaker).
- **Synchronous Target & Less-Nondeterminism ($\le_{\text{nd}}$):** Pirouette's control language uses **synchronous** communication (Thm 9 explicitly relies on synchronous blocking). Because $\sqcup$ introduces extra `allow` branches unused on a given trace, Global Soundness (Thm 11) and Global Completeness (Thm 9) relate projected systems via a *less-nondeterminism* preorder $\Pi_1 \le_{\text{nd}} \Pi_2$ (Thm 7), yielding **Deadlock Freedom By Design (Thm 12)**: every reachable state $\Pi$ from a well-typed closed choreography either has all locations at values or can take a step. Pirouette lacks location polymorphism.

#### 1.3 Choral: Role-Parameterized Objects, Java Compilation, and `MoveMeant`

Giallorenzo, Montesi & Peressotti (TOPLAS 2024; `choral-lang/choral` at `a644dbd4...`) embed choreographies into an object-oriented language compiling to pure Java libraries:

- **Role-Parameterized Types (`T@(A, B)`):** Classes, interfaces, and values carry world parameter vectors; channels are ordinary interfaces rather than language primitives:
  - `DiDataChannel.chh` (lines 24–26): `public interface DiDataChannel@( A, B )< T@X > { < S@Y extends T@Y > S@B com( S@A m ); }`
  - `DiSelectChannel.chh` (lines 24–27): `public interface DiSelectChannel@( A, B ) { @SelectionMethod < T@X extends Enum@X< T > > T@B select( T@A m ); }`
  - `SymChannel.chh` (line 24): extends `BiChannel@(A, B)<T, T>` and `SymDataChannel@(A, B)<T>`.
- **Soloist Projection & Switch Merging (`StatementsProjector.java`, `StatementsMerger.java`):**
  - Projecting a `@SelectionMethod` call (`isSelectionMethodAtWorld`, lines 277–292, 319–326) or type-selection method (lines 224–249, 328–340) at the receiving world wraps the continuation via `selectionSwitchStatement` (lines 210–222) into a single-case `SwitchStatement` plus a compiler-synthesized `SwitchArgumentMergeDefault` dummy default (lowered by `JavaCompiler` into a `throw`).
  - Projecting `IfStatement` (lines 348–366) or `SwitchStatement` (lines 369–398) at an uninvolved world projects each branch and invokes `StatementsMerger.merge(cases)`. `StatementsMerger.merge(SwitchStatement, SwitchStatement)` (lines 132–165) verifies at most one default case (`checkSingleDefaultCase`), recursively merges overlapping labels, unions disjoint labels, and throws `MergeException` (line 57) on incompatible ASTs. `alwaysReturns` (lines 64–92, 387–388) prunes unreachable Java continuations after exhaustive returns.
- **Automated `KoC` Insertion (`MoveMeant`):** `choral/compiler/moveMeant/` (`InsertSelections.java`, `MiniZincSelectionMethod.java`) optionally infers missing selections, synthesizes a selection `Enum` (`InsertSelections.java` lines 90–91), and rewrites the immutable `CompilationUnit` prior to projection.

#### 1.4 Freer-Monad Libraries (`HasChor`, `MultiChor`) and Verified Compilation (`Kalas`)

**HasChor** (ICFP 2023; `gshen42/HasChor` at `e6bf3d5e...`) embeds choreographies as a Haskell **freer monad** (`type Choreo m = Freer (ChoreoSig m)`, `Choreo.hs` line 41):

- **Located Values & Rank-N Unwrapping:** `data a @ (l :: LocTy) = Wrap a | Empty` (`Location.hs` lines 24–38), with `type Unwrap l = forall a. a @ l -> a` (`Choreo.hs` line 18) scoped inside `locally`. `Choreography.hs` exports `type (@)` without constructors to prevent `unwrap Empty` (which throws a runtime error).
- **Dynamic `EPP` & Global Broadcast `KoC` (`Choreo.hs` lines 53–68):** `epp :: Choreo m a -> LocTm -> Network m a` interprets `Local`, `Comm`, and `Cond` into `NetworkSig` (`Run`, `Send`, `Recv`, `BCast`). Crucially, `Cond l a c` compiles to `broadcast (unwrap a) >> epp (c (unwrap a)) l'` at the decider and `recv (toLocTm l) >>= \x -> epp (c x) l'` at every other role—avoiding compile-time `KoC` rejections altogether.
- **Implementation Caveats Verified in Source:** (1) Every `cond` leaks and broadcasts the scrutinee (requiring `Show`/`Read`) to *all* nodes in `locs cfg`, even unaffected roles. (2) Commit `e6bf3d5e...` fixes broadcast self-sending (`filter (/= self)` in `Network/Http.hs` line 92 and `Network/Local.hs` line 45). (3) `Network/Http.hs` swallows HTTP `Send` errors via `Left err -> putStrLn $ "Error : " ++ show err` (lines 88–90) and uses a fixed `threadDelay 1000000` (line 77) before killing the Servant receive thread. (4) Dynamic interpretation requires shipping every role's choreography code to every node, though `runChoreo` (`Choreo.hs` lines 44–50) yields a convenient single-threaded testing oracle.

**MultiChor** (`ShapeOfMatter/MultiChor` at `4b83cad1...`; PLDI 2025) eliminates HasChor's global broadcast leak while retaining library embedding (`src/Choreography/Core.hs` lines 35–108): `Choreo (ps :: [LocTy]) m a` tracks the active participant **census** `ps`, values are multiply located (`Located (ls :: [LocTy]) a`) guarded by `Member`/`Subset` proofs, and `Conclave :: Subset ls ps -> Choreo ls m b -> ChoreoSig ps m (Located ls b)` confines `Broadcast` strictly to the subset `ls` while supporting **census polymorphism** (`fanOut`/`fanIn`/`Faceted`).

For end-to-end verified compilation to machine code, **Kalas** (Pohjola et al., ITP 2022) verifies choreographic `EPP` in HOL4 all the way to verified **CakeML**, closing the unverified compiler gap present in `Choral`, `HasChor`, and `MultiChor`.

| System | Realization | KoC Mechanism | Higher-Order / Polymorphism | Mechanized Proof | Transport / Faults |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Pirouette** (2022) | Standalone calculus | Explicit `ℓ1[L] ⇝ ℓ2` + merge $\sqcup$ | Higher-order; no loc-poly | Full Coq (Thms 1–12) | Synchronous reliable |
| **Choral** (2024) | Compiler $\to$ Java | `@SelectionMethod` switch + `StatementsMerger` (+ `MoveMeant`) | Higher-order & role-parameterized OO | Paper calculus; compiler unverified | Pluggable Java `SymChannel`; crash-free |
| **HasChor** (2023) | Haskell freer monad | `Cond` broadcasts to all `locs cfg` | Higher-order & loc-poly (`KnownSymbol`) | Paper sketch only | Local `Chan` / HTTP (swallows send errors, 1s teardown sleep) |
| **MultiChor** (2025) | Haskell freer monad | `Broadcast` scoped to `Conclave` census | Higher-order, loc-poly, **census-poly** | Type-level `Member`/`Subset` proofs | Pluggable; static census per `Conclave` |
| **Kalas** (2022) | Compiler $\to$ CakeML | Explicit selections + merge | First-order | End-to-end HOL4 $\to$ CakeML | Reliable messaging |

### 2. Multiparty Session Types (MPST): Published Proof Flaws, Generalized Behavioral Typing, and Liveness

Basis: normative (Honda-Yoshida-Carbone 2008/2016, Scalas & Yoshida POPL 2019, Actris POPL 2020) + source (`alcestes/mpstk`) + execution (`support/verify_epp_mpst_and_calm.py`)

#### 2.1 Classical Global-to-Local MPST and Unprojectable Protocols

Classical MPST (Honda, Yoshida & Carbone, POPL 2008 / JACM 2016) projects a global type $G$ onto local types $T_p = G \upharpoonright p$ and type-checks endpoints independently. Unlike linear-logic binary session types (Wadler 2012), whose cut-elimination prevents deadlocks only by forcing acyclic process trees (requiring priority annotations such as Kobayashi 2006 / Padovani 2014 / Dardha & Gay 2018 for cyclic graphs), global MPST captures cyclic multi-role exchanges directly.

Global-type projection (`alcestes/mpstk/src/main/scala/Ops.scala` lines 265–354) uses **full merge** ($\sqcap$) on uninvolved roles: `Branch` (external choice) unions disjoint incoming labels and recursively merges common labels with equal payload types (lines 298–313); `Select` (internal choice) requires identical recipient and identical label sets (lines 315–323). Honda et al.'s own Example 3.10 (*Instrument Control*, `examples-bad/instrument-control.global`) exposes the `KoC` trap:

```text
User→Op:privilege(int) .
Op→User:{
  ok . μ(t)(User→Instr { move . t, photo . t, quit . Instr→Op:status(string) . end }),
  no . end
}
```

Projecting onto `Instr` fails to merge `μ(t)User&{...}` with `end`; typing endpoints directly (`examples/instrument-control.ctx`) yields a **safe** context that **deadlocks** whenever `Op` sends `no`. Fixing projectability (`examples/instrument-control-fixed.global`) requires explicit `User→Instr:start`/`end` notifications and `Instr→Op:busy` loop synchronization.

#### 2.2 Scalas & Yoshida (POPL 2019): Classical Subject-Reduction Flaws and "Less is More"

Scalas & Yoshida (POPL 2019) uncovered a systemic soundness flaw spanning major published MPST papers (extensions of Honda-Yoshida-Carbone, Bettini et al., Deniélou et al., and Coppo et al.):

1. **Why Classical Proofs Broke:** Prior Subject Reduction proofs relied on syntactic coherence/consistency predicates (often pairwise binary duality of projected local types) assumed to be invariant under reduction. When **full-merge projection** interacts with **subtyping** (or recursion/delegation), a consistent typing context $\Gamma$ can step to a context $\Gamma'$ that violates syntactic consistency—breaking the inductive proof of Subject Reduction, and under unconstrained merge/subtyping rules admitting unsafe communications. Conversely, restricting to strict consistency rejects valid, live multiparty protocols.
2. **Generalized Behavioral MPST:** Scalas & Yoshida drop global types and binary duality as primitive prerequisites. Typing contexts $\Gamma = \{s[p_i]: T_i\}$ carry a direct LTS semantics, and session creation is parameterized by any behavioral predicate $\varphi(\Gamma) \subseteq \text{safe}(\Gamma)$, where **minimal safety** (`safe(Γ)`) is the weakest coinductive invariant guaranteeing Subject Reduction: in every reachable LTS state, whenever $p$ can send to $q$ and $q$ can receive from $p$, every output label and payload of $p$ is accepted by $q$. Global types become an optional frontend whose projections are verified against $\varphi(\Gamma)$.

#### 2.3 Modal $\mu$-Calculus Formulas and the 5-Tier Strict Behavioral Hierarchy

Inspecting `alcestes/mpstk/src/main/resources/mcrl2/*.mcf` yields the exact modal $\mu$-calculus properties verified via mCRL2 (`pbes2bool`) over output $o$, input $i$, and synchronization $t$ actions:

- **`safety.mcf`**: $\nu X.\;\forall s,r_1,r_2,m_1,m_2,p_1,p_2.\;((\langle o(s,r_1,r_2,m_1,p_1)\rangle\top \land \langle i(s,r_1,r_2,m_2,p_2)\rangle\top) \implies \langle t(s,r_1,r_2,m_1,p_1)\rangle\top) \land [t(\dots)]X$.
- **`deadlock-freedom.mcf`**: $\nu Z.\;((\forall\dots[t(\dots)]\bot) \implies (\forall\dots[i(\dots)]\bot \land [o(\dots)]\bot)) \land [\exists\dots t(\dots)]Z$.
- **`liveness.mcf` (weak):** Every enabled $i$/$o$ can synchronize along *some* finite path ($\mu Z_i.\;\langle t\rangle\top \lor \exists r_3,r_4.\langle t(r_3,r_4)\rangle Z_i$).
- **`liveness+.mcf` (fair-choice):** Some finite strategy advances via a role $r_3$ whose *every* enabled choice stays on track ($\mu Y.\;\langle t\rangle\top \lor \exists r_3.(\exists r_4.\langle t(r_3,r_4)\rangle\top \land \forall r_4.[t(r_3,r_4)]Y)$).
- **`liveness++.mcf` (unconditional):** *Every* maximal path fires every pending $i$/$o$ in finitely many steps ($\mu Y.\;\langle t\rangle\top \lor (\exists\langle t\rangle\top \land \forall[t]Y)$).

The strict inclusion $\text{live}^{++} \subsetneq \text{live}^{+} \subsetneq \text{live} \subsetneq \text{df} \subsetneq \text{safe}$ is witnessed by POPL 2019 contexts in `alcestes/mpstk/examples/` (and reproduced in `support/verify_epp_mpst_and_calm.py`):

| `mpstk` Witness | Context $\Gamma$ | Sync `safe` | Sync `df` | Sync `live` | Sync `live+` | Sync `live++` | Async FIFO `df` | Separation Demonstrated |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: | :---: | :--- |
| `popl19-sec2.3.ctx` | `p: q⊕foo`, `q: p&bar` | **No** | No | No | No | No | No | Label mismatch (unsafe) |
| `popl19-ex5.11-a.ctx` | `p: q&m1.r⊕m3`, `q: r&m2.p⊕m1`, `r: p&m3.q⊕m2` | Yes | **No** | No | No | No | **No** | Safe 3-role circular wait |
| `popl19-sec7-m3.ctx` | `p: q⊕m1.q&m2`, `q: p⊕m2.p&m1` | Yes | **No** | No | No | No | **Yes** (`live++`) | **Sync vs. Async split:** crossover sends deadlock synchronously, pass under FIFO |
| `popl19-ex5.11-b.ctx` | `p: μt.q⊕m1.t`, `q: μt.p&m1.t`, `r: q&m2` | Yes | Yes | **No** | No | No | Yes (not live) | Permanent starvation of `r` |
| `popl19-ex5.6.ctx` | `p: μt.q⊕{m1.t, m2}`, `q: μt.p&{m1.t, m2.r⊕m3}`, `r: q&m3` | Yes | Yes | Yes | **No** | No | Yes | Unfair role choice (`m1` loop) starves `r` |
| `popl19-ex5.7.ctx` | `p: q⊕m1.q2⊕m2`, `q: p&m1`, `q2: p&m2`, `r1↔r2` loop | Yes | Yes | Yes | Yes | **No** | Yes | Unfair scheduler favoring `r1↔r2` starves `p→q→q2` |
| `instrument-control.ctx` | Honda et al. JACM 2016 Ex. 3.10 | Yes | **No** | No | No | No | **No** | Safe, deadlocks when `Op→User:no` |

#### 2.4 Dependent Separation Protocols (`Actris`)

Standard MPST cannot verify value-dependent functional invariants or mutable heap ownership transfer across channels. **Actris** (Hinrichsen, Bengtson & Krebbers, POPL 2020) embeds asynchronous binary session types inside **Iris** (Coq) as dependent separation protocols (`!x. v⟨P⟩. prot` / `?x. v⟨P⟩. prot`) carrying arbitrary Iris separation-logic assertions $P$ and asynchronous subprotocol swapping (see `iris-adequacy-transfinite-liveness-simuliris-and-lean-separation-logic` for Iris foundations), trading automated type checking for interactive proof construction.

### 3. The Decidability Wall: Synchronous vs. Asynchronous Session Subtyping

Basis: normative (Lange & Yoshida FoSSaCS 2017, Bravetti-Carbone-Zavattaro 2017) + source (`alcestes/mpstk/src/main/scala/Subtyping.scala`) + execution (`support/verify_epp_mpst_and_calm.py`)

Under **synchronous** communication (Gay & Hole 2005), session subtyping is **decidable** via coinductive simulation over regular trees, as implemented in `alcestes/mpstk/src/main/scala/Subtyping.scala` (lines 19–43; using channel-oriented orientation where `Select` subtypes allow wider outgoing label sets and `Branch` subtypes allow narrower incoming label sets, isomorphic to reversed process orientation):

```scala
case (Branch(from1, c1), Branch(from2, c2)) =>
  (from1 == from2) && (c1.keySet subsetOf c2.keySet) &&
  c1.keys.forall { l => subtypes(c1(l).payload, c2(l).payload, asmp) &&
                        subtypes(c1(l).cont,    c2(l).cont,    asmp) }
case (Select(to1, c1), Select(to2, c2)) =>
  (to1 == to2) && (c2.keySet subsetOf c1.keySet) &&
  c2.keys.forall { l => subtypes(c2(l).payload, c1(l).payload, asmp) &&
                        subtypes(c1(l).cont,    c2(l).cont,    asmp) }
```

Under **asynchronous FIFO communication**, an endpoint may **anticipate outputs before inputs** because unbounded FIFO buffers absorb sends without blocking. For example, $T_{\text{opt}} = \mu t.\, q\oplus a.\, q\& b.\, t$ safely refines $T_{\text{spec}} = \mu t.\, q\& b.\, q\oplus a.\, t$ under FIFO channels despite failing synchronous subtyping and deadlocking synchronously against $\overline{T_{\text{spec}}}$ (verified in `support/verify_epp_mpst_and_calm.py` Suite B8). Because recursive anticipation turns the unbounded FIFO buffer into unbounded memory, two simultaneous 2017 papers proved **general asynchronous session subtyping is undecidable even for two parties**:

1. **Lange & Yoshida (FoSSaCS 2017):** Defined **Asynchronous Duplex (`AD`)** two-party CFSMs, proved Turing-completeness by reducing the **Turing-machine halting problem** to `AD` compatibility, and showed equivalence to orphan-message-free binary asynchronous subtyping (Chen et al.). Identified three decidable subclasses: **half-duplex**, **alternating**, and **single-choice / non-branching**.
2. **Bravetti, Carbone & Zavattaro (*Inf. & Comp.* 256, 2017, `arXiv:1611.05026`):** Reduced **queue-machine acceptance** directly to a minimal core relation $\ll$ (single-choice outputs on subtype, single-choice inputs on supertype, no consecutive infinite outputs), proving **all three published asynchronous subtyping definitions**—Mostrous & Yoshida (binary), Chen et al. (orphan-free binary), and Mostrous, Yoshida & Honda (ESOP 2009 multiparty)—are **undecidable**, and exhibiting an explicit input on which Mostrous et al. (2009)'s supposedly terminating algorithm diverges (§4.4). Restricting both types to single-choice inputs ($\ll_{\text{sin}}$) or both to single-choice outputs ($\ll_{\text{sout}}$) restores **decidability**.

| Subtyping Relation | Channel Model | Decidable? | Proof Technique | Reference |
| :--- | :--- | :---: | :--- | :--- |
| Binary / MPST synchronous subtyping | Synchronous | **Yes** | Coinductive regular-tree simulation | Gay & Hole 2005; `mpstk` `Subtyping.scala` |
| Orphan-free binary async subtyping | Unbounded FIFO (2-party) | **No** | Turing-machine halting $\to$ Asynchronous Duplex CFSMs | Lange & Yoshida (FoSSaCS 2017) |
| General binary & multiparty async subtyping | Unbounded FIFO (2- or $N$-party) | **No** | Queue-machine acceptance $\to$ core relation $\ll$ | Bravetti, Carbone & Zavattaro (2017) |
| Half-duplex, alternating, $\ll_{\text{sin}}$, $\ll_{\text{sout}}$ | Unbounded FIFO (restricted) | **Yes** | Bounded buffer / single-choice restriction | Lange & Yoshida 2017; Bravetti et al. 2017 |

*Compiler consequence:* No sound, complete, terminating decision procedure exists for unrestricted asynchronous subtyping; tools must choose synchronous subtyping, bounded/decidable-fragment approximations, or interactive proof (`Actris`).

### 4. Partial Failure, Crash-Stop Semantics, and Distributed Impossibility Boundaries (FLP, CAP)

Basis: normative (FLP JACM 1985, Gilbert & Lynch 2002, Barwell et al. CONCUR 2022) + source (`gshen42/HasChor`) + execution (`support/verify_epp_mpst_and_calm.py`) + derived

Standard choreographies (`Pirouette`, `Choral`, `HasChor`, `MultiChor`) and classic MPST assume crash-free, reliable delivery; under crashes, linear continuations block indefinitely (and `HasChor` §6 explicitly excludes faults, while `Network/Http.hs` silently ignores send errors). Fault-tolerant protocol systems immediately confront two impossibility walls:

- **FLP Impossibility (Fischer, Lynch & Paterson, JACM 1985):** In a purely asynchronous network with reliable delivery, **no deterministic consensus protocol** guarantees both safety and termination if even one process can crash-stop unannounced, because slow processes are indistinguishable from crashed ones.
- **CAP Theorem (Gilbert & Lynch, SIGACT News 2002):** Under asynchronous network partitions (**P**), no read/write service can simultaneously guarantee linearizability (**C**) and total availability (**A**).

**Crash-Stop Generalized MPST (Barwell, Scalas, Yoshida & Zhou, CONCUR 2022, `arXiv:2207.02015`)** extends Scalas & Yoshida's framework with `stop` types ($U ::= T \mid \text{stop}$), an optional set of **reliable roles** $\mathcal{R}$, and a `crash` branch label on external choices:

1. **Operational Semantics:** Any active role $p \notin \mathcal{R}$ may nondeterministically crash ($s[p]\lightning$) to `stop`. Sends to a crashed role drop silently without blocking the sender; receives from a crashed role $q$ trigger crash detection ($s[p]\lightning q$) and take the `crash` branch—or fault/deadlock if `crash` is omitted (verified in `support/verify_epp_mpst_and_calm.py` Suite B9).
2. **Reconciliation with FLP (Derived):** Barwell et al. (§1, p. 3) assume the **crash-fail model** (Cachin, Guerraoui & Rodrigues §2.6.2): crash-stop processes without recovery, reliable in-order links unless the recipient crashed, and an **accurate (perfect) failure detector**. Because a perfect failure detector $\mathcal{P}$ solves consensus, Crash-Stop MPST does not contradict FLP—but its deadlock-freedom and liveness theorems hold **only when the runtime failure detector produces zero false suspicions** (e.g., supervised local OS processes or lease-fenced RPCs, not unguarded WAN timeouts under partitions).
3. **State-Space Explosion:** Enumerating crash interleavings inflates LTS verification dramatically. In Barwell et al. Fig. 1, a 2-role DNS protocol has **10 states and 15 transitions** when reliable, expanding to **101 states and 427 transitions** (10.1$\times$ states, 28.5$\times$ transitions) when server `q` may crash and a reliable failover `r` is added.

### 5. Monotonic Distributed Dataflow: CALM Theorem, CRDTs, Invariant Confluence, and Hydro

Basis: normative (Ameloot et al. JACM 2013, Hellerstein & Alvaro CACM 2020, Shapiro et al. SSS 2011, Bailis et al. PVLDB 2014) + source (`hydro-project/hydro`) + execution (`support/verify_epp_mpst_and_calm.py`)

#### 5.1 CALM Theorem, Relational Transducers, and `Bloom`/`Dedalus`

Formalized via relational transducers by **Ameloot, Neven & Van den Bussche (JACM 2013)** and synthesized by **Hellerstein & Alvaro (CACM 2020)**, the **CALM Theorem (Consistency As Logical Monotonicity)** states:

> A program has a consistent (confluent), coordination-free distributed implementation **if and only if** it is logically monotonic.

Key formal distinctions:

- **Consistency = Confluence:** Output is uniquely determined by the input set regardless of asynchronous delivery order, batching, or delay.
- **Coordination vs. Communication:** A transducer network is *coordination-free* if, when all inputs reside on one machine, that machine produces the complete output without sending messages. Messages required under *every* data partitioning are **coordination**; messages merely routing partitioned tuples are communication.
- **Monotonic vs. Non-Monotonic Graph Reachability (Hellerstein & Alvaro §1.3, verified in Suite C3):** Distributed **deadlock detection** (cycle existence) is monotonic—every delivery permutation produces zero false positives without barriers. Distributed **garbage collection** (unreachability via negation) is non-monotonic—evaluating on a partial prefix before a delayed remote edge arrives falsely reclaims live objects (2/2 orders corrupted without a global barrier).
- **Static "Point-of-Order" Analysis:** **Dedalus** (Alvaro et al., Datalog 2010) adds logical time (`@next`) and asynchronous space (`@async`) to Datalog; **Bloom** (Alvaro et al., CIDR 2011) statically flags non-monotonic operators (`notin`, closing aggregates) as points of order requiring coordination. Eliminating unnecessary coordination in the Anna KVS yielded over two orders of magnitude higher throughput compared to systems spending up to 90% of CPU time waiting on coordination (Hellerstein & Alvaro §1.1).

#### 5.2 Semilattice CRDTs, Algebraic Bugs, and Invariant Confluence

State-based **CRDTs** (Shapiro et al., SSS 2011) achieve Strong Eventual Consistency (`SEC`) by constraining replica states to a bounded **join-semilattice** $(S, \sqcup, \bot)$ satisfying **Associativity**, **Commutativity**, and **Idempotence (ACI)**, inducing $x \le y \iff x \sqcup y = y$. Deletes become monotonic via tombstones (`2P-Set`) or unique add-tags (`OR-Set`, where `remove` tombstones only observed `(elem, uid)` tags so concurrent `add` wins).

Two structural hazards require verification beyond standard type checking:

1. **ACI Law Violations:** Unchecked merge functions silently break convergence—e.g., an `LWW` register favoring `self` on equal timestamps fails commutativity (`(0,'A') ⊔ (0,'B') ≠ (0,'B') ⊔ (0,'A')`), and integer midpoint averaging fails associativity (`(0 ⊔ 0) ⊔ 2 = 1 ≠ 0 = 0 ⊔ (0 ⊔ 2)`), both caught in Suite C2. Isabelle/HOL mechanization (**Gomes et al., OOPSLA 2017**) uncovered causality/delivery-precondition bugs in published CRDT specifications.
2. **Convergence $\neq$ Application Invariants ($\mathcal{I}$-Confluence):** **Bailis et al. (PVLDB 2014)** proved transactions preserve application invariant $\mathcal{I}$ without coordination iff merging any two reachable valid states preserves $\mathcal{I}$ ($\mathcal{I}(s_1) \land \mathcal{I}(s_2) \implies \mathcal{I}(s_1 \sqcup s_2)$). Uniqueness constraints and non-negative balance decrements fail $\mathcal{I}$-confluence and require coordination or escrow partitioning.

#### 5.3 Hydro (`hydro-project/hydro`): Rust Lattice Typing, `NonDet` Guards, and Verus Proofs

**Hydro** (*Keep CALM and CRDT On*, Laddad et al., PVLDB 2022; `hydro-project/hydro` at `fbaccddb...`) compiles Rust distributed dataflow (`hydro_lang`) to DFIR (`dfir_rs`, successor to Hydroflow):

1. **Composable Lattices (`lattices/src/lib.rs`, `map_union.rs`, `test.rs`):** `Merge::merge(&mut self, other) -> bool` (lines 105–124) mandates ACI laws and requires returning `true` iff `self` strictly advanced (in `map_union.rs` lines 88–100, bottom entries `val_other.is_bot()` are filtered so they never flip `changed`). `Lattice` composes `Merge`, `LatticeOrd`, `NaiveLatticeOrd`, `IsBot`, and `IsTop` (`lib.rs` lines 54–57). Because Rust traits cannot check ACI laws, `lattices/src/test.rs` (lines 14–150) provides finite exhaustive property testers (`check_all`, `check_lattice_properties`, `check_lattice_ord`).
2. **Four-Axis Stream Typing (`hydro_lang/src/live_collections/{stream/mod.rs,boundedness.rs,batch_atomic.rs}`, `location/tick.rs`):** `Stream<T, L, B, O, R>` statically tracks Location (`Process`, `Cluster`, `Tick<L>`, `Atomic<L>` with read-after-write `end_atomic()`/`BatchAtomic`), Boundedness (`Bounded` vs. `Unbounded`, where `Unbounded::PreserveOrderIfBounded<InO> = NoOrder` drops order on symmetric hash joins and `IsBounded` gates non-monotonic barriers), Ordering (`TotalOrder` vs. `NoOrder`, `stream/mod.rs` lines 45–98), and Retries (`ExactlyOnce` vs. `AtLeastOnce`, lines 101–140).
3. **`NonDet<H>` Guards & Verus Proofs (`nondet.rs`, `properties/mod.rs`):** Observing nondeterministic batching/timing requires an explicit `NonDet<H>` guard via `nondet!(/** reason */)` carrying optional simulator hooks (`BatchHook`, `SnapshotHook`). Unordered or at-least-once aggregations require `AggFuncAlgebra<T, B, C, I, M, S>` (lines 1443–1475) constrained by `ValidCommutativityFor<O>` (lines 1650–1654), `ValidIdempotenceFor<R>` (lines 1673–1677), and `ApplyMonotoneStream<P, B2>` (lines 1866–1872). Proof witnesses are either unchecked `ManualProof<H>` (untrusted by the simulator, which still explores reorderings via `OrderingHook`) or `VerusCommutativeProof` / `VerusIdempotentProof` (lines 125–210), whose macros (`verus_proof_commutative_fold!`, `verus_proof_idempotent_fold!`, etc.) symbolically verify the *actual closure body* in both orders or under duplication (also proving panic/overflow freedom).
4. **Observed Verification Trust Boundary (`properties/mod.rs` lines 138–142, 189–196):** Under standard `cargo build`, Verus obligations are **erased** to zero-sized marker structs—so soundness holds **only when `cargo verus verify` runs**. Moreover, `VerusIdempotentProof`'s documentation explicitly warns that *"the simulator does not inject retries, so (unlike commutativity) idempotence claims are not explored by simulation tests at all; a Verus proof is the only mechanical check."*

### 6. Rolling-Upgrade Protocol & Schema Evolution Across Open Wire Boundaries

Basis: normative (`protocolbuffers/protobuf` `docs/field_presence.md`, Zhang et al. SOSP 2021) + documentation (Protobuf v3.5.0 release behavior) + execution (`support/verify_epp_mpst_and_calm.py`) + derived

Choreographies and classical MPST assume a single protocol version across all nodes, whereas production services run mixed versions ($v_1$ and $v_2$) simultaneously during rolling upgrades and read persistent state written by prior versions:

1. **Empirical Upgrade Failure Profile (DUPTester / DUPChecker, Zhang et al., SOSP 2021):** Across **123 real upgrade failures** in 8 distributed systems (Cassandra, HBase, HDFS, etc.), **38%** were Blocker severity (vs. 10% for typical bugs) and **67%** affected all or most users. Static cross-version analysis (`DUPChecker`) found **>800 cross-version format incompatibilities**, and upgrade simulation (`DUPTester`) exposed 20 previously unknown bugs across 4 systems.
2. **Protocol Buffers Wire & Presence Mechanics (`protocolbuffers/protobuf` at `caaf8662...`, `docs/field_presence.md`):**
   - Messages serialize as self-delimiting `(field_number, wire_type, payload)` streams of *present* fields (never field names); renumbering or reusing a field number breaks wire compatibility immediately.
   - *Presence split (`docs/field_presence.md` lines 10–55):* `proto2` tracks *explicit presence*, whereas `proto3` used *no presence* for singular scalars (omitting default `0`/`""`/`false` on the wire, so an explicitly sent empty string can vanish on round-trip) until explicit `optional` presence returned by default in release **3.15** (later generalized via per-feature **Protobuf Editions**).
   - *Unknown-field preservation & the proto3 3.0–3.4 regression:* Forward compatibility through an older intermediary ($v_2 \to v_1\text{ proxy} \to v_2$) depends on retaining unknown `(tag, payload)` pairs and re-emitting them on serialization. Pre-3.5 `proto3` **dropped unknown fields at parse time**, causing silent data loss across $v_1$ proxies; **v3.5.0** restored preservation by default across core runtimes (reproduced in Suite C4). Unknown fields are still lost across **JSON transcoding** (`protojson`) and **manual field-by-field message reconstruction**.
   - *Enum evolution (`docs/field_presence.md` lines 65–68):* `proto2` closed enums shunt unrecognized numeric values into unknown fields; `proto3` open enums keep them in-band, risking unhandled switch branches in older endpoints.
3. **Tension with Session Duality (Derived):** Closed-label MPST rejects any unrecognized wire label as a safety error, requiring either receiver-side label contravariance (`Branch` superset) already deployed on older nodes or explicit version negotiation before branching. Conversely, Protobuf unknown fields preserve *payload data* forward-compatibly without checking *multi-step control-flow* safety or deadlock-freedom.

### 7. Executable Probe Verification Results (`support/verify_epp_mpst_and_calm.py`)

Basis: execution (`python3 -B support/verify_epp_mpst_and_calm.py`, exit code 0)

| Suite / Case | Assertion Verified | Observed Result |
| :--- | :--- | :--- |
| **A1** Two-Buyers (`EPP` + FIFO BFS) | Explicit `Select` merges cleanly; exhaustive FIFO sim over `accepts ∈ {True, False}` has 0 deadlocks, 0 orphans | **PASS** — 3 roles; 30 (`True`) / 20 (`False`) FIFO states |
| **A2** Pirouette §5.2 Merge | Shared `send(L1, 3)` prefix merges before `offer(L1){L => ..., R => ...}` at `L2` | **PASS** — `L2` merged; FIFO deadlock/orphan-free |
| **A3–A4** `KoC` Rejection | Unmerged 3-role `if` rejected at `Bob`/`Carol`; Instrument Control (Ex. 3.10) rejected at `Instr` | **PASS** — exact `MergeError` role counterexamples |
| **B1–B7** POPL 2019 MPST Contexts | Exact $\mu$-calculus fixed points separate `safe`/`df`/`live`/`live+`/`live++` and sync vs. async `sec7-m3` | **PASS** — all 7 `mpstk` contexts match table (`sec7-m3`: sync `df=False`, async `df=True, live++=True`) |
| **B8** Sync Subtyping vs. Anticipation | Sync subtyping rejects `μt. q⊕a. q&b. t ≤ μt. q&b. q⊕a. t`; async FIFO execution with dual is safe & deadlock-free | **PASS** — `sync_sub=False`, `async_fifo_df=True` |
| **B9** Crash-Stop DNS Failover | Unreliable `q` without `crash` branch fails safety; `crash` branch + reliable failover `r` passes `safe`, `df`, `live++` | **PASS** — reliable: 3 states; failover: 9 states, 9 transitions |
| **C1–C2** Semilattice ACI Checker | Verifies `GSet`, `GCounter`, `2P-Set`, `OR-Set`, total `LWW`; catches biased `LWW` and midpoint average | **PASS** — counterexamples `((0,'A'),(0,'B'))` & `(0,0,2)` caught |
| **C3** CALM Confluence | Monotonic deadlock detection: 0 false positives across 6 permutations; uncoordinated GC: 2/2 premature reclamations | **PASS** — `deadlock_fp=0`, `gc_corruptions=2/2` |
| **C4** Rolling-Upgrade Wire | `v2 -> v1 proxy -> v2` drops field #3 under pre-3.5 proto3, preserves intact under proto2 / proto3 $\ge$ 3.5 | **PASS** — `pre3.5_dropped_f3=True`, `preserve_roundtrip=True` |

## Boundaries

- **Known not to apply:**
  - *Choreographic deadlock-freedom outside closed worlds:* Theorems (`Pirouette` Thm 12, `Choral`, `HasChor`, `MultiChor`, `Kalas`) **do not apply** if any endpoint is hand-written, modified post-projection, running a mismatched version, or subject to crash/message-loss faults.
  - *Crash-Stop MPST under imperfect failure detectors:* Barwell et al.'s (CONCUR 2022) safety/liveness guarantees **do not apply** when network partitions cause false crash suspicions (breaking the crash-fail model's accurate-detector premise).
  - *General asynchronous session subtyping decidability:* No sound, complete, terminating algorithm exists for unrestricted binary or multiparty FIFO session subtyping (Lange & Yoshida 2017; Bravetti et al. 2017).
  - *Hydro Verus proofs under ordinary `cargo build`:* `VerusCommutativeProof` and `VerusIdempotentProof` erase to ZST markers without `cargo verus verify`, and Hydro's simulator does not inject retries to exercise idempotence (`hydro_lang/src/properties/mod.rs` lines 138–142, 189–196).
  - *CRDT convergence vs. application invariants:* ACI semilattices guarantee identical converged state, **not** non-$\mathcal{I}$-confluent invariants (uniqueness, non-negative balances; Bailis et al. 2014).
- **Unsupported:**
  - *Unbounded dynamic topologies in `Pirouette` and `alcestes/mpstk`:* `Pirouette` omits location polymorphism; `mpstk` and Barwell et al. model-check fixed finite role sets with finite-state local types.
  - *Automatic monotonicity verification for arbitrary host code:* Undecidable by Rice's theorem; `Hydro` relies on algebraic markers, `lattices` combinators, finite testing, or user-guided Verus proofs.
  - *Unknown-field preservation through JSON:* `protojson` cannot round-trip unknown numeric tags.
- **Not examined:**
  - *Choral bytecode codegen and socket runtime (`JavaCompiler`, `SymByteChannelImpl`):* Inspection focused on AST projection, merging, channel headers, and `MoveMeant` entry points.
  - *Building/running upstream toolchains (`cargo verus`, `mvn test`, `cabal test`, `mCRL2`):* Verification used primary source inspection and the standalone Python probe.
  - *Byzantine faults, omission/recovery choreographies, synchronous-reactive languages (`Lustre`/`Esterel`/`Vélus`), and language-specific Protobuf Editions runtimes beyond `docs/field_presence.md`.*
- **Unknown:**
  - *Worst-case scalability of `MoveMeant` MiniZinc selection inference (`MiniZincSelectionMethod.java`)* on deeply nested multi-role conditionals.
  - *Mechanized end-to-end soundness of combining projected choreographies with legacy/MPST endpoints under rolling upgrades and crash-recovery:* Open research problem not resolved in the examined sources.

## Evidence

All evidence was acquired and verified on `2026-11-19`.

### Pinned Source Repositories

1. **`choral-lang/choral`** @ `a644dbd4429f2d609b2ca280a064bab9d73fab34` (`2026-10-30`) — `choral/src/main/resources/headers/choral/channels/{DiDataChannel,DiSelectChannel,SymChannel}.chh`; `choral/src/main/java/choral/compiler/soloist/{SoloistProjector,StatementsProjector}.java` (lines 48–413); `choral/src/main/java/choral/compiler/merge/StatementsMerger.java` (lines 36–229); `choral/src/main/java/choral/compiler/moveMeant/InsertSelections.java` (lines 25–100).
2. **`gshen42/HasChor`** @ `e6bf3d5e771e309ba8db7f2e55822f6a11c1e237` (`2026-11-08`) — `src/Choreography.hs` (lines 1–43); `src/Choreography/Location.hs` (lines 1–45); `src/Choreography/Choreo.hs` (lines 18–113); `src/Choreography/Network.hs` (lines 14–59); `src/Choreography/Network/{Local,Http}.hs` (full files); `src/Control/Monad/Freer.hs` (lines 13–43).
3. **`ShapeOfMatter/MultiChor`** @ `4b83cad1b2374dbf4907ccce48a65fa403936dab` (`2025-12-02`) — `README.md` (lines 1–90); `src/Choreography.hs`; `src/Choreography/Core.hs` (lines 1–110).
4. **`alcestes/mpstk`** @ `5a056cc2193c2c588c1c7ddf130176c3aacdf38e` (`2019-01-16`) — `src/main/resources/mcrl2/{safety,deadlock-freedom,liveness,liveness+,liveness++}.mcf`; `src/main/scala/{GlobalType,Ops,Subtyping,Context}.scala` (`Ops.scala` lines 265–354, `Subtyping.scala` lines 6–44); `examples/popl19-{sec2.3,ex5.6,ex5.7,ex5.11-a,ex5.11-b,ex5.11-c,sec5,sec7-m3}.ctx`; `examples/{instrument-control.ctx,instrument-control-fixed.global,two-buyers.global}`; `examples-bad/{instrument-control,non-projectable-1,non-projectable-2,non-projectable-3}.global`.
5. **`hydro-project/hydro`** @ `fbaccddb35111327f96922259d60dc1607395545` (`2026-11-17`) — `lattices/src/{lib,set_union,map_union,test}.rs`; `hydro_lang/src/live_collections/{boundedness,stream/mod,batch_atomic}.rs`; `hydro_lang/src/location/tick.rs`; `hydro_lang/src/nondet.rs` (lines 1–90); `hydro_lang/src/properties/mod.rs` (lines 1–210, 1416–1475, 1650–1894).
6. **`protocolbuffers/protobuf`** @ `caaf86620a4ea6363bb1cf43c50dc430725c39dd` (`2026-11-19`) — `docs/field_presence.md` (lines 1–90).

### Peer-Reviewed Publications & Standards Verified

- Hirsch & Garg (2022), *Pirouette: Higher-Order Typed Functional Choreographies*, PACMPL 6(POPL), Art. 23, DOI `10.1145/3498684`, `arXiv:2111.03484`, Coq artifact DOI `10.5281/zenodo.5586354` (full PDF inspected).
- Giallorenzo, Montesi & Peressotti (2024), *Choral: Object-Oriented Choreographic Programming*, ACM TOPLAS 46(1), Art. 1, DOI `10.1145/3632398`, `arXiv:2005.09520`.
- Shen, Kashiwa & Kuper (2023), *HasChor: Functional Choreographic Programming for All (Functional Pearl)*, PACMPL 7(ICFP), Art. 207, DOI `10.1145/3607849`, `arXiv:2303.00924` (full PDF inspected).
- Bates, Kashiwa, Jafri, Shen, Kuper & Near (2025), *Efficient, Portable, Census-Polymorphic Choreographic Programming*, PLDI 2025, DOI `10.1145/3729296`, `arXiv:2412.02107`.
- Pohjola, Gómez-Londoño, Shaker & Norrish (2022), *Kalas: A Verified, End-To-End Compiler for a Choreographic Language*, ITP 2022, DOI `10.4230/LIPIcs.ITP.2022.27`.
- Honda, Yoshida & Carbone (2008 / 2016), *Multiparty Asynchronous Session Types*, POPL 2008 (DOI `10.1145/1328438.1328472`) and JACM 63(1), Art. 2 (DOI `10.1145/2827695`).
- Scalas & Yoshida (2019), *Less is More: Multiparty Session Types Revisited*, PACMPL 3(POPL), Art. 30, DOI `10.1145/3290343` (tech. report DTRS-18-6).
- Lange & Yoshida (2017), *On the Undecidability of Asynchronous Session Subtyping*, FoSSaCS 2017, LNCS 10203, pp. 441–457, DOI `10.1007/978-3-662-54458-7_26`.
- Bravetti, Carbone & Zavattaro (2017), *Undecidability of Asynchronous Session Subtyping*, *Information and Computation* 256, pp. 300–320, `arXiv:1611.05026` (full PDF inspected).
- Barwell, Scalas, Yoshida & Zhou (2022), *Generalised Multiparty Session Types with Crash-Stop Failures*, CONCUR 2022, DOI `10.4230/LIPIcs.CONCUR.2022.35`, `arXiv:2207.02015` (full PDF inspected).
- Hinrichsen, Bengtson & Krebbers (2020), *Actris: Session-Type Based Reasoning in Separation Logic*, PACMPL 4(POPL), Art. 6, DOI `10.1145/3371074`.
- Fischer, Lynch & Paterson (1985), *Impossibility of Distributed Consensus with One Faulty Process*, JACM 32(2), pp. 374–382, DOI `10.1145/3149.214121`.
- Gilbert & Lynch (2002), *Brewer's Conjecture and the Feasibility of Consistent, Available, Partition-Tolerant Web Services*, ACM SIGACT News 33(2), pp. 51–59, DOI `10.1145/564585.564601`.
- Ameloot, Neven & Van den Bussche (2013), *Relational Transducers for Declarative Networking*, JACM 60(2), Art. 15, DOI `10.1145/2450142.2450151` (PODS 2011, DOI `10.1145/1989284.1989321`).
- Hellerstein & Alvaro (2020), *Keeping CALM: When Distributed Consistency is Easy*, CACM 63(9), pp. 72–81, DOI `10.1145/3369736`, `arXiv:1901.01930` (full PDF inspected).
- Alvaro et al. (2010 / 2011), *Dedalus: Datalog in Time and Space*, Datalog 2010, LNCS 6702, DOI `10.1007/978-3-642-24206-9_16`; *Consistency Analysis in Bloom: a CALM and Collected Approach*, CIDR 2011.
- Shapiro, Preguiça, Baquero & Zawirski (2011), *Conflict-Free Replicated Data Types*, SSS 2011, LNCS 6976, pp. 386–400, DOI `10.1007/978-3-642-24550-3_29`.
- Bailis et al. (2014), *Coordination Avoidance in Database Systems*, PVLDB 8(3), pp. 185–196, DOI `10.14778/2735508.2735509`.
- Gomes, Kleppmann, Mulligan & Beresford (2017), *Verifying Strong Eventual Consistency in Distributed Systems*, PACMPL 1(OOPSLA), Art. 109, DOI `10.1145/3133933`.
- Laddad et al. (2022), *Keep CALM and CRDT On*, PVLDB 16(4), pp. 856–863, DOI `10.14778/3574245.3574268`.
- Zhang et al. (2021), *Understanding and Detecting Software Upgrade Failures in Distributed Systems*, SOSP 2021, DOI `10.1145/3477132.3483577`.

### Preserved Support Artifact

- `support/verify_epp_mpst_and_calm.py`: Executed on `2026-11-19` via `python3 -B support/verify_epp_mpst_and_calm.py` (Python 3.13, Linux x86_64, stdlib-only); exited `0` with all assertions passing across Suites A, B, and C.

## Revalidation

1. **Rerun the executable formal probe:**
   ```console
   python3 -B reports/choreographic-programming-multiparty-session-types-and-distributed-protocols/support/verify_epp_mpst_and_calm.py
   ```
   A passing run re-verifies `EPP` partial-merge diagnostics, async FIFO deadlock/orphan freedom, the 5-tier MPST behavioral hierarchy, sync vs. async crossover divergence, crash-stop failover safety, join-semilattice ACI laws, CALM delivery-order confluence, and Protobuf unknown-field preservation.
2. **Diff targeted upstream regions from the pinned SHAs:**
   - `choral-lang/choral` from `a644dbd4429f2d609b2ca280a064bab9d73fab34`: `StatementsProjector.java`, `StatementsMerger.java`, `choral/compiler/moveMeant/`.
   - `gshen42/HasChor` from `e6bf3d5e771e309ba8db7f2e55822f6a11c1e237` (`Choreo.hs`, `Network/Http.hs`) and `ShapeOfMatter/MultiChor` from `4b83cad1b2374dbf4907ccce48a65fa403936dab` (`Core.hs`): check for scoped `KoC`, transport error propagation, or `Conclave` census changes.
   - `hydro-project/hydro` from `fbaccddb35111327f96922259d60dc1607395545`: `hydro_lang/src/properties/mod.rs`, `hydro_lang/src/live_collections/{stream/mod.rs,boundedness.rs}`, `hydro_lang/src/nondet.rs`, `lattices/src/lib.rs` (check whether simulator retry injection or build-time Verus enforcement was added).
   - `alcestes/mpstk` from `5a056cc2193c2c588c1c7ddf130176c3aacdf38e` (`.mcf`, `Ops.scala`, `Subtyping.scala`) and `protocolbuffers/protobuf` from `caaf86620a4ea6363bb1cf43c50dc430725c39dd` (`docs/field_presence.md`).
3. **Full re-audit trigger:** Mathematical results (`Pirouette` Thms 1–12, Scalas & Yoshida 2019, Lange & Yoshida 2017, Bravetti et al. 2017, FLP 1985, CAP 2002, CALM 2013) are immutable; re-investigate only if a new formalism establishes mechanized open-world mixed-version choreographic soundness, crash-recovery without accurate failure detectors, or a new decidable fragment of asynchronous session subtyping.
