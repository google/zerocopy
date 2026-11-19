# Compositional Open Games, Algorithmic Mechanism Design, and Formal Incentive Verification

## Summary

Multi-principal systems—distributed schedulers, decentralized fee markets, combinatorial auctions, and autonomous agent economies—cannot be verified solely through memory safety or cryptographic honesty: rational agents obey every syntactic and cryptographic rule while strategically misreporting private inputs, shading bids, reordering messages, or colluding off-chain to maximize utility. Formalizing and verifying economic soundness rests on two complementary mathematical pillars examined here from primary sources and executable probes:

1. **Bidirectional Optics Make Game Equilibria Compositional (`Open Games`, Categorical Cybernetics):** Standard forward functions do not compose Nash equilibria, because an upstream player's optimal move depends contravariantly on counterfactual continuation payoffs from downstream subgames. Ghani, Hedges, Winschel, and Zahn (`LICS 2018`, `DOI: 10.1145/3209108.3209165`) and Capucci et al. (`EPTCS 372`, `DOI: 10.4204/EPTCS.372.17`) resolve this via **parametric bidirectional optics (`play` forward, `coplay` backward coutility)** coupled with a best-response / equilibrium evaluation function. In `CyberCat-Institute/open-games-hs@e14be50f7f`, sequential composition `(>>>)` transports evaluation contexts contravariantly across the downstream optic (`cmap identity (play h a') c`) and covariantly across the upstream optic (`cmap (play g a) identity c`), while parallel composition `(&&&)` slices joint contexts via `\\` and `//`—and generalizes to correlated Bayesian games via `StochasticStatefulOptic` and `StochasticStatefulContext`.
2. **Incentive Compatibility (`DSIC`/`BIC`) Is a Relational 2-Execution Hyperproperty Fragile Under Numerical & Protocol Approximations:** Proving Dominant-Strategy Incentive Compatibility ($\forall v_i, v'_i, v_{-i}: u_i(M(v_i, v_{-i}), v_i) \ge u_i(M(v'_i, v_{-i}), v_i)$) or Bayesian Incentive Compatibility (`BIC`) requires relating *two executions* of a mechanism differing only in agent $i$'s report—the exact structural domain of Probabilistic Relational Hoare Logic (`pRHL` in `EasyCrypt`, Barthe et al., `WINE 2016`, `arXiv:1502.04052`) and relational refinement proofs in Isabelle/HOL (`Caminati et al., EC 2015`, `mirror-afp-devel@7731745138`). Crucially, **numerical representation is load-bearing for economic soundness**: while Isabelle/HOL's verified VCG extractor (`CombinatorialAuctionCodeExtraction.thy`) strictly extracts arbitrary-precision `integer`/`nat` arithmetic, implementing the exact same combinatorial VCG mechanism in IEEE-754 `float64` **breaks DSIC**! Probe 3B constructs a concrete `float64` rounding/tie-breaking exploit (`1e16 + 1.0 == 1e16` vs. `1e16 + 1.5 == 10000000000000002.0`) where overbidding above true valuation flips allocation tie-breaking and yields strictly positive utility gain ($\Delta u_0 = +1.0 > 0$).
3. **Decentralized Protocol Incentives Hit Sharp Impossibility Frontiers (`EIP-1559`, Roughgarden 2021/2024, Chung & Shi 2023):** When the mechanism executor (block proposer / miner) is itself a strategic player rather than a trusted auctioneer, `DSIC` splits into three distinct criteria: **User Incentive Compatibility (`UIC`)**, **Miner/Proposer Incentive Compatibility (`MIC`/`MMIC`)**, and **Off-Chain Agreement / Side-Contract Proofness (`OCA` / `c-SCP`)**. Ethereum `EIP-1559` (`ethereum/EIPs@b055feec32`) achieves all three *only* when blocks are uncongested (effectively infinite block size); once finite block capacity binds, `EIP-1559` degrades into a first-price tip auction violating `UIC` (Probe 3C: `+19` utility gain from tip shading). Worse, Chung and Shi (`SODA 2023`, `DOI: 10.1137/1.9781611977554.ch150`) proved a fundamental **finite-block impossibility theorem**: no non-trivial single-parameter transaction fee mechanism (even randomized) can simultaneously satisfy `UIC` and `1-SCP` under finite block size—demonstrated concretely in Probe 3C where a miner censoring one competing bid steals the entire burned second-price payment (`+130` joint coalition gain).

## Applicability

These findings apply to formal modeling of multi-agent strategic interaction, verified auction/allocation implementations, smart-contract and decentralized fee mechanisms, and rational-agent incentive analysis across the following examined subjects:

- **Categorical Compositional Game Theory:**
  - `CyberCat-Institute/open-games-hs` at `e14be50f7f4cb250ac9a03d907996ee97ec48908` (`modules/engine/src/OpenGames/Engine/{Optics.hs,OpenGames.hs,Optics/StochasticStateful.hs,OpenGames/BayesianGames.hs}` and `modules/modelling/src/OpenGames/BayesianModelling/{AtomicGames.hs,Diagnostics.hs}`), implementing the categorical framework of Ghani, Hedges, Winschel, and Zahn (`LICS 2018`, `DOI: 10.1145/3209108.3209165`, `arXiv:1603.04641`) and Capucci, Gavranović, Hedges, and Rischel (`ACT 2021 / EPTCS 372`, `DOI: 10.4204/EPTCS.372.17`, `arXiv:2105.06332`).
- **Formal Mechanism Design Verification:**
  - `isabelle-prover/mirror-afp-devel` at `773174513872254f8efe1cb3a3ce64037f0b1da6` (`thys/Vickrey_Clarke_Groves/{CombinatorialAuction.thy,StrictCombinatorialAuction.thy,CombinatorialAuctionCodeExtraction.thy,UniformTieBreaking.thy}`), corresponding to Caminati, Kerber, Lange, and Rowat (`ACM EC 2015`, `DOI: 10.1145/2764468.2764511`).
  - `EasyCrypt/easycrypt` at `ce19cb6cbab4951e58553c36128e8a19f2f90c6a` paired with Barthe, Gaboardi, Gallego Arias, Hsu, Roth, and Strub (`WINE 2016`, `arXiv:1502.04052`) on `pRHL` verification of `VCG` and the Hartline–Kleinberg–Malekian (`HKM`) `BIC` reduction.
- **Blockchain / Untrusted-Auctioneer Mechanism Design:**
  - `ethereum/EIPs` at `b055feec322fbc37e9d77a393a50b3ff56b31c92` (`EIPS/eip-1559.md`), analyzed via Tim Roughgarden (`ACM EC 2021` `DOI: 10.1145/3465456.3467591` / `JACM 2024` `DOI: 10.1145/3651158`, `arXiv:2106.01340`) and Hao Chung & Elaine Shi (`SODA 2023`, `DOI: 10.1137/1.9781611977554.ch150`, `arXiv:2111.03151`).

**Relationship Among Subjects:** `Open Games` provides the compositional semantics and equilibrium-checking calculus for multi-stage strategic protocols; `EasyCrypt` (`pRHL`) and Isabelle/HOL (`Vickrey_Clarke_Groves`) provide mechanized proof techniques and verified code extraction for universal quantification over unbounded continuous/discrete valuation domains; and `EIP-1559` + Roughgarden / Chung–Shi delimit the exact boundary where classical trusted-auctioneer `DSIC` proofs break down when the mechanism executor can deviate or collude.

## Findings

### 1. Categorical Cybernetics and Compositional Open Games (`play` / `coplay` Optics)

Basis: normative/mathematical (Ghani et al., `LICS 2018`; Capucci et al., `EPTCS 372`) + source (`CyberCat-Institute/open-games-hs@e14be50f7f`) + execution (Probe 3A).

#### 1.1 Why Naive Forward Composition Fails for Game Equilibria

In a two-stage extensive-form game where Player 1 selects $y \in Y$ given state $x \in X$, and Player 2 observes $y$ to select $z \in Z$ yielding payoffs $(r_1, r_2)$, Player 1's best-response predicate cannot be decided from $G_1$'s forward play map alone: evaluating whether $y$ is optimal requires probing **counterfactual deviations** $y' \neq y$ through Player 2's strategy $\sigma_2(y')$ and propagating the resulting utility **backward** to Player 1.

Ghani et al. (`LICS 2018`) capture this bidirectional information flow by defining an **open game** $\mathcal{G} : (X, S) \to (Y, R)$ as a quadruple $(\Sigma_{\mathcal{G}}, \mathbf{P}_{\mathcal{G}}, \mathbf{C}_{\mathcal{G}}, \mathbf{E}_{\mathcal{G}})$:
- Strategy profile set $\Sigma_{\mathcal{G}}$;
- Forward **play** function $\mathbf{P}_{\mathcal{G}} : \Sigma_{\mathcal{G}} \times X \to Y$;
- Backward **coplay** (coutility) function $\mathbf{C}_{\mathcal{G}} : \Sigma_{\mathcal{G}} \times X \times R \to S$;
- **Best-response / equilibrium** relation $\mathbf{E}_{\mathcal{G}} : X \times (Y \to R) \to \mathcal{P}(\Sigma_{\mathcal{G}})$ (or diagnostic evaluation function returning deviation records per player given an environment context $(h, k)$ where $h$ provides initial state/history and $k : Y \to R$ is the continuation payoff function).

In Capucci, Gavranović, Hedges, and Rischel (`EPTCS 372`, 2022), open games instantiate a universal **parametric lens / $\mathbf{Para}(\mathbf{Optic})$** architecture shared with reverse-mode automatic differentiation (gradient descent learners) and bidirectional control systems: a system interacts bidirectionally with an *environment* along $(X, S) \leftrightarrow (Y, R)$ and with a *controller* (strategy profile / neural weights) along parameters $\Sigma$.

#### 1.2 Exact Haskell Type-Class Formulation (`open-games-hs@e14be50f7f`)

Inspection of `CyberCat-Institute/open-games-hs` (`Optics.hs` L22–50, `OpenGames.hs` L21–55) reveals the exact algebraic encoding of open games over abstract optics `o` and contexts `c`:

```haskell
-- modules/engine/src/OpenGames/Engine/Optics.hs (L22-39)
class Optic o where
  lens   :: (s -> a) -> (s -> b -> t) -> o s t a b
  (>>>>) :: o s t a b -> o a b p q -> o s t p q
  (&&&&) :: o s1 t1 a1 b1 -> o s2 t2 a2 b2 -> o (s1, s2) (t1, t2) (a1, a2) (b1, b2)
  (++++) :: o s1 t a1 b -> o s2 t a2 b -> o (Either s1 s2) t (Either a1 a2) b

class (Optic o, Precontext c) => Context c o where
  cmap :: o s1 t1 s2 t2 -> o a1 b1 a2 b2 -> c s1 t1 a2 b2 -> c s2 t2 a1 b1
  (//) :: (Show s1) => o s1 t1 a1 b1 -> c (s1, s2) (t1, t2) (a1, a2) (b1, b2) -> c s2 t2 a2 b2
  (\\) :: (Show s2) => o s2 t2 a2 b2 -> c (s1, s2) (t1, t2) (a1, a2) (b1, b2) -> c s1 t1 a1 b1
```

```haskell
-- modules/engine/src/OpenGames/Engine/OpenGames.hs (L21-55)
data OpenGame o c a b x s y r = OpenGame {
  play     :: List a -> o x s y r,
  evaluate :: List a -> c x s y r -> List b
}

(>>>) :: (Optic o, Context c o, Unappend a, Unappend b)
      => OpenGame o c a b x s y r -> OpenGame o c a' b' y r z q
      -> OpenGame o c (a +:+ a') (b +:+ b') x s z q
(>>>) g h = OpenGame {
  play     = \as -> case unappend as of (a, a') -> play g a >>>> play h a',
  evaluate = \as c -> case unappend as of
    (a, a') -> evaluate g a (cmap identity (play h a') c)
           +:+ evaluate h a' (cmap (play g a) identity c)
}

(&&&) :: (Optic o, Context c o, Unappend a, Unappend b, Show x, Show x')
      => OpenGame o c a b x s y r -> OpenGame o c a' b' x' s' y' r'
      -> OpenGame o c (a +:+ a') (b +:+ b') (x, x') (s, s') (y, y') (r, r')
(&&&) g h = OpenGame {
  play     = \as -> case unappend as of (a, a') -> play g a &&&& play h a',
  evaluate = \as c -> case unappend as of
    (a, a') -> evaluate g a (play h a' \\ c)
           +:+ evaluate h a' (play g a // c)
}
```

Key architectural properties observed directly in `open-games-hs`:
1. **Sequential Context Transport (`>>>`):** `g` receives `cmap identity (play h a') c`—prepending `h`'s forward-and-backward optic onto the continuation `c` so `g` evaluates counterfactual deviations through `h`'s play and coplay! Symmetrically, `h` receives `cmap (play g a) identity c`—pushing initial history forward through `g`'s play!
2. **Parallel Context Slicing (`&&&`):** `g` evaluates in `play h a' \\ c` (holding `h`'s strategy fixed while varying `g`'s action), and `h` evaluates in `play g a // c`—exact compositional encoding of unilateral Nash deviation checks!
3. **Bayesian Correlated Types (`Optics/StochasticStateful.hs` L43–71, `BayesianGames.hs` L61–120):** Pure deterministic lenses cannot represent incomplete-information auctions where bidders hold correlated private valuations drawn from a joint prior. `StochasticStatefulContext` carries an existential latent state `z` (`Stochastic (z, s)` plus continuation `z -> a -> StateT Vector Stochastic b`), enabling `dependentDecision` (`BayesianGames.hs` L97–120) to compute Bayesian conditional posterior updates (`bayes h x`) and check $\varepsilon$-equilibrium (`strategicPayoff >= optimalPayoff - epsilon`, L84) over `Double` expected payoffs (`DiagnosticInfoBayesian`, L61–68).
4. **Executable Verification via Probe 3A:** On a 2-stage market-entry deterrence game, bidirectional `seq_compose` immediately rejects the non-credible threat `(Out, Fight)` (`Incumbent@In: eq=False, u=-1, best_u=1, best_move=Accommodate`) while certifying the Subgame-Perfect Equilibrium `(In, Accommodate)` (`all_SPE=True`). Composing two parallel bidders with an auctioneer lens via `par_compose >>> auction_mechanism` confirms that truthful bidding `(7, 5)` fails equilibrium in a First-Price Auction (`Bidder1: eq=False, u=0, best_u=2, best_bid=5`) and satisfies exact equilibrium in a Second-Price (Vickrey) Auction (`eq=True, Bidder1 u=2, Bidder2 u=0`).

**Critical Limitation of `open-games-hs`:** Because `open-games-hs` evaluates `maximumBy (comparing snd) [(y, u y) | y <- ys]` (`BayesianGames.hs` L94) by finite enumeration over `[y]` in IEEE-754 `Double` (`Payoff`), it is an **executable finite-domain equilibrium checker / model finder**, *not* a universal formal proof over infinite continuous valuation spaces $\mathbb{R}_{\ge 0}^n$, and inherits floating-point precision hazards unless parameterized by exact rationals or backed by theorem proving.

---

### 2. Formal Verification of Mechanism Design (`DSIC` / `BIC`) via Relational Logic & Theorem Provers

Basis: normative/paper (Barthe et al., `WINE 2016`, `arXiv:1502.04052`; Caminati et al., `ACM EC 2015`, `DOI: 10.1145/2764468.2764511`) + source (`isabelle-prover/mirror-afp-devel@7731745138`, `EasyCrypt/easycrypt@ce19cb6cba`) + execution (Probe 3B).

#### 2.1 Incentive Compatibility as a Relational 2-Safety / Coupling Hyperproperty

Let a (possibly randomized) direct-revelation mechanism $M : \mathcal{B}_1 \times \dots \times \mathcal{B}_n \to \Delta(\mathcal{O} \times \mathbb{R}^n)$ map bid profile $\mathbf{b} = (b_i, b_{-i})$ to an allocation $o \in \mathcal{O}$ and payment vector $\mathbf{p} \in \mathbb{R}^n$, with quasilinear agent utility $u_i((o, \mathbf{p}), v_i) = v_i(o) - p_i$.

- **Dominant-Strategy Incentive Compatibility (`DSIC`):**
  $$\forall i \in N,\; \forall v_i, b'_i \in \mathcal{B}_i,\; \forall b_{-i} \in \mathcal{B}_{-i}: \quad \mathbb{E}_{(o, \mathbf{p}) \sim M(v_i, b_{-i})}[v_i(o) - p_i] \;\ge\; \mathbb{E}_{(o', \mathbf{p}') \sim M(b'_i, b_{-i})}[v_i(o') - p'_i]$$
- **Bayesian Incentive Compatibility (`BIC`):** Replaces universal quantification over $b_{-i}$ with expectation over rival types $v_{-i} \sim \mathcal{D}_{-i}$ assuming rivals report truthfully.
- **Structural Duality with Noninterference and Differential Privacy:** Notice that neither `DSIC` nor `BIC` is a single-trace safety property—both compare **two correlated executions** of the same program $M$ on neighboring inputs $(v_i, b_{-i})$ and $(b'_i, b_{-i})$ differing solely in coordinate $i$.

#### 2.2 Relational Hoare Logic (`EasyCrypt` `pRHL`, Barthe et al. `WINE 2016`)

Barthe, Gaboardi, Gallego Arias, Hsu, Roth, and Strub (`WINE 2016`, `arXiv:1502.04052`) exploit this exact relational structure inside `EasyCrypt`'s Probabilistic Relational Hoare Logic (`pRHL`):

1. **Judgment Shape:** A `pRHL` judgment $\vdash c_1 \sim c_2 : \Phi \Rightarrow \Psi$ asserts that for any pair of initial memories $(m_1, m_2) \models \Phi$, there exists a probabilistic **coupling** $\mu \in \Delta(\mathcal{M} \times \mathcal{M})$ whose marginals are $\llbracket c_1 \rrbracket(m_1)$ and $\llbracket c_2 \rrbracket(m_2)$ and whose support satisfies $\Psi$.
2. **Proving `DSIC` and `BIC` by Coupling:** To verify randomized `DSIC` (or `BIC` under both prior-type randomness and internal mechanism randomness), the proof aligns random coin flips between the truthful execution $M(v_i, b_{-i})$ and the deviating execution $M(b'_i, b_{-i})$ via `pRHL` coupling rules, reducing expected-utility inequalities to pointwise or expectation-lifting postconditions (`E[u1] >= E[u2]`).
3. **Verified Case Studies:** Barthe et al. (`arXiv:1502.04052`) mechanically verified both the classical **Vickrey–Clarke–Groves (`VCG`)** mechanism and the substantially harder **Hartline–Kleinberg–Malekian (`HKM`, 2011) generic black-box reduction** from `BIC` mechanism design to approximation algorithms—a proof requiring simultaneous reasoning over *two independent sources of randomness* (prior type distributions and randomized replica-surrogate matching). Parallel work by the same authors connects relational approximate couplings (`apRHL`) to the **Exponential Mechanism** (differential privacy implies approximate $\varepsilon$-DSIC, because changing one bidder's report alters the output distribution by at most $e^\varepsilon$!).

#### 2.3 Specification-to-Executable-Code Refinement (`Isabelle/HOL AFP Vickrey_Clarke_Groves`)

Whereas `EasyCrypt` excels at probabilistic couplings, Caminati, Kerber, Lange, and Rowat (`ACM EC 2015`, `DOI: 10.1145/2764468.2764511`; `isabelle-prover/mirror-afp-devel@7731745138`) address a different verification chasm: **bridging non-computable mathematical set-theoretic specifications of combinatorial VCG auctions down to executable code without losing soundness**:

1. **Two-Layer Specification vs. Algorithm Separation (`StrictCombinatorialAuction.thy` L55–107; `CombinatorialAuction.thy` L41–835):**
   - The abstract specification quantifies over set-theoretic partitions (`allAllocations N G`), `argmax (sum b)` (`winningAllocationsRel`), and Clarke pivot payments `paymentsRel N G t = alpha N G - remainingValueRel N G t` where `alpha N G b n = Max ((sum b) ' (allAllocations (N - {n}) G))` (`StrictCombinatorialAuction.thy` L75–103).
   - Because `Set` comprehensions and `argmax` over powersets cannot be executed directly, the formalization defines list-based computational counterparts (`allAllocationsAlg`, `winningAllocationAlg`, `vcgaAlg`, `vcgpAlg`, `paymentsAlg`) and proves exact **bridging equivalences** in Isabelle/HOL: `chosenAllocationEquivalence` (`CombinatorialAuction.thy` L751), `tiebidsBridgingLemma` (L757), `resolvingBidBridgingLemma` (L792), and `tiebreakingGivesSingleton` (L826, proving randomized/indexed tie-breaking deterministically yields a singleton winning allocation).
2. **Exact-Integer Code Extraction (`CombinatorialAuctionCodeExtraction.thy` L25–58):**
   - Importing `"HOL-Library.Code_Target_Nat"` and `"HOL-Library.Code_Target_Int"` (L25–26) and typing bids over arbitrary-precision `integer` (`Elsee (0::integer)`, L41), Isabelle exports `vcgaAlg` and `payments` to executable Scala (`export_code vcgaAlg payments allocationPrettyPrint in Scala`, L56–57)—completely avoiding IEEE-754 floating-point arithmetic!

#### 2.4 Why Exact Arithmetic Is Mandatory: Concrete IEEE-754 `float64` VCG DSIC Counterexample

Basis: execution (Probe 3B) + derived.

Many real-world ad-tech, cloud-spot, and financial auction engines implement textbook VCG allocation and Clarke pivot formulas in IEEE-754 `double` (`f64`). Probe 3B proves both directions empirically:

1. **Exact Rational Verification (`fractions.Fraction`):** On a 2-item `{A, B}` combinatorial VCG auction over discrete valuations `{0, 1, 2}^3`, checking all `729` `(true_valuation, misreport)` relational pairs finds **`0` DSIC violations**.
2. **Concrete IEEE-754 `float64` Counterexample (`ULP(1e16) = 2.0`):**
   Consider 2 goods `{A, B}` and 3 bidders with exact bids:
   - Bidder 0 (true valuation): $v_0(\{A\}) = 1.0$, $v_0(\{B\}) = 0$, $v_0(\{A,B\}) = 0$.
   - Bidder 1: $b_1(\{B\}) = 10^{16}$.
   - Bidder 2: $b_2(\{A,B\}) = 10^{16}$.
   - Deterministic tie-breaking prefers `whole` (`2 -> AB`) over `split` (`0 -> A, 1 -> B`) on equal reported welfare.
   - **Under Exact Arithmetic (`Fraction`):** Truthful reporting $b_0 = 1$ yields $W(\text{split}) = 10^{16} + 1 > 10^{16} = W(\text{whole})$, so Bidder 0 wins `{A}`, pays Clarke pivot $p_0 = 10^{16} - 10^{16} = 0$, and obtains utility $u_0 = 1.0$.
   - **Under IEEE-754 `float64`:** Because $\text{ULP}(10^{16}) = 2.0$ and IEEE-754 uses round-to-nearest-even:
     - **Truthful bid $b_0 = 1.0$:** `float(1e16) + float(1.0) == 10000000000000000.0 == W(whole)`. Tie-breaking awards `{A, B}` to Bidder 2; Bidder 0 loses and receives **`u_0(truth) = 0.0`**.
     - **Strategic overbid $b'_0 = 1.5 > v_0$:** `float(1e16) + float(1.5) == 10000000000000002.0 > W(whole)`. Bidder 0 now wins `{A}` with Clarke pivot payment $p_0 = 10^{16} - 10^{16} = 0.0$, obtaining true utility **`u_0(misreport = 1.5) = 1.0 - 0.0 = +1.0`**!
   - **Result:** $u_0(1.5, b_{-0}) - u_0(1.0, b_{-0}) = +1.0 > 0$, strictly violating `DSIC`! The exact same failure mode arises whenever non-associative `f64` summation (`0.1 + 0.2 = 0.30000000000000004 > 0.3`) perturbs argmax tie-breaking across multi-bidder bundles, or whenever approximate ILP/MIP winner-determination solvers fail to find the exact welfare maximum (since Clarke pivot truthfulness requires exact affine maximization—even a $10^{-6}$ suboptimality gap destroys `DSIC`!).

---

### 3. Decentralized Mechanism Design: Untrusted Auctioneers, `EIP-1559`, and Finite-Block Impossibility

Basis: normative (`ethereum/EIPs@b055feec32`, `EIPS/eip-1559.md`) + paper (Roughgarden `EC 2021`/`JACM 2024`; Chung & Shi `SODA 2023`) + execution (Probe 3C).

Classical mechanism design (including `VCG` and `HKM`) assumes a **trusted, non-strategic auctioneer** who faithfully executes allocation and payment rules. In decentralized protocols (blockchains, federated agent markets, decentralized sequencer networks), the mechanism executor is itself a strategic agent who can censor bids, inject fake shill bids (`sybil` transactions), or enter off-chain side contracts with bidders.

#### 3.1 Three-Axis Incentive Taxonomy and `EIP-1559` Mechanics

Roughgarden (`EC 2021`, `DOI: 10.1145/3465456.3467591`; `JACM 2024`, `DOI: 10.1145/3651158`) and Chung & Shi (`SODA 2023`, `DOI: 10.1137/1.9781611977554.ch150`) define three coupled requirements for a Transaction Fee Mechanism (`TFM`):

1. **`UIC` (User Incentive Compatibility):** Bidding true valuation is a dominant strategy for every user, holding block-proposer strategy and other bids fixed.
2. **`MIC` / `MMIC` (Myopic Miner/Proposer Incentive Compatibility):** Faithfully executing the prescribed inclusion rule without censoring eligible bids or injecting fake transactions maximizes proposer revenue.
3. **`OCA`-proofness / `c-SCP` (Off-Chain Agreement / $c$-Side-Contract Proofness):** No coalition of the proposer and up to $c$ users (weakest non-trivial case: `1-SCP`, proposer + 1 user) can strictly increase their **joint utility** by deviating on-chain and splitting surplus off-chain.

In Ethereum `EIP-1559` (`ethereum/EIPs@b055feec32`, `EIPS/eip-1559.md` L135–237), each block carries a protocol-determined `base_fee_per_gas` adjusted dynamically across blocks via `ELASTICITY_MULTIPLIER = 2` and `BASE_FEE_MAX_CHANGE_DENOMINATOR = 8` (`L193–195`), and each transaction specifies `(max_fee_per_gas, max_priority_fee_per_gas)`:
```python
# EIPS/eip-1559.md L222-233
priority_fee_per_gas = min(transaction.max_priority_fee_per_gas,
                           transaction.max_fee_per_gas - block.base_fee_per_gas)
effective_gas_price = priority_fee_per_gas + block.base_fee_per_gas
# Signer pays effective_gas_price; base_fee_per_gas is BURNED;
# block.author receives ONLY gas_used * priority_fee_per_gas.
```

#### 3.2 Incentive Compatibility Matrix & Chung–Shi Finite-Block Impossibility Theorem

| Mechanism | Block Capacity Regime | `UIC` (User Truthful)? | `MIC` (Proposer Honest)? | `1-SCP` / `OCA`-Proof (No Miner+User Bribe)? | Failure Mechanism When Violated |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **First-Price Auction (Legacy Bitcoin / Pre-1559 ETH)** | Any | **No** | **Yes** | **Yes** (total revenue stays inside coalition; no burn to steal) | Users shade bids aggressively to extract surplus (Probe 3A: `+2` gain). |
| **Second-Price Auction (Pay Miner)** | Finite | **Yes** (only if miner honest) | **No** (shill-bid attack) | **No** (bid-manipulation collusion) | Proposer injects fake bid at $b_1 - \varepsilon$ to turn second-price into first-price! |
| **Burned Second-Price Auction** | Finite | **Yes** (given honest miner) | **Yes** (miner gets 0 either way) | **No (`1-SCP` fails!)** | Proposer censors 2nd-highest bid `U2`, reducing burned payment from `130` to `0`, and splits `+130` off-chain with `U1` (Probe 3C)! |
| **Ethereum `EIP-1559` (Posted Base Fee Burn + Tip)** | **Uncongested** ($\sum \text{gas} \le \text{cap}$) | **Yes** (`max_fee = v`, minimal tip) | **Yes** | **Yes** (`OCA`-proof, Roughgarden 2021) | Holds strictly while base fee clears demand without hitting block gas cap. |
| **Ethereum `EIP-1559`** | **Congested** ($\sum \text{gas} > \text{cap}$) | **No** | **Yes** | **Yes** | Degrades into a **First-Price Auction on `priority_fee_per_gas`**; Probe 3C shows shading tip from `50` to `31` increases `U1`'s utility from `0` to `19`. |
| **Any Deterministic or Randomized Single-Parameter TFM** | **Finite Block Size** | **Impossible jointly with `1-SCP`!** | — | **Impossible jointly with `UIC`!** | **Chung–Shi Theorem (`SODA 2023`):** Under finite block capacity, **no** non-trivial TFM simultaneously satisfies `UIC` and `1-SCP`! |

#### 3.3 Engineering Design Consequences for Verified Multi-Agent Protocols

Basis: derived from Ghani et al. (`LICS 2018`), Barthe et al. (`WINE 2016`), Caminati et al. (`EC 2015`), Roughgarden (`JACM 2024`), and Chung & Shi (`SODA 2023`).

1. **Verification Architecture Choice:**
   - Use **Compositional Open Games (`play`/`coplay` optics)** during *protocol design and prototyping* to structure multi-stage interactions (auctions, peer-auditing bounties, decentralized task allocation), identify non-credible threats, and run finite-grid diagnostic sweeps (`evaluate`).
   - Use **Relational Hoare Logic (`EasyCrypt` `pRHL`) or Higher-Order Theorem Proving (`Isabelle/HOL`, `Lean 4`)** for *universal mechanism proofs* (`DSIC`/`BIC`) across unbounded type spaces and randomized mechanisms—paired with exact arbitrary-precision integer/rational arithmetic (`Code_Target_Int` / `Fraction`), never unverified `f64` sums or approximate MIP solvers!
2. **Circumventing the Finite-Block `UIC + 1-SCP` Impossibility:** Because Chung & Shi prove exact `UIC + 1-SCP` is mathematically impossible for any single-proposer finite-capacity mechanism, real protocols must explicitly choose one of four formal relaxations: (a) **elastic/overprovisioned capacity** (`EIP-1559` uncongested regime), (b) **approximate $\varepsilon$-incentive compatibility**, (c) **cryptographic decentralized auctioneers (`MPC` / threshold-encrypted mempools)** removing single-proposer censorship power, or (d) **explicit multi-proposer / Bayesian `BIC` relaxation** (burning mechanisms under known prior distributions).
3. **Application to Autonomous Agent & Prover Auditing Incentives:** In multi-agent verification or coding pools where untrusted workers submit candidate patches/proofs and peer auditors earn rewards for finding defects, naive fixed bounties suffer specification gaming (Goodharting) and worker–auditor collusion (analogous to `1-SCP`). Modeling the submitter $\to$ auditor $\to$ verifier-oracle pipeline as a sequential **Open Game** (`submitter >>> auditor >>> oracle_mechanism`) directly exposes off-equilibrium shirking and collusion thresholds before deploying real compute or token stakes.

## Boundaries

- **Live Execution of `open-games-hs`, `EasyCrypt`, and `Isabelle/HOL` Toolchains (`not examined`):** Source code at exact pinned revisions (`open-games-hs@e14be50f7f`, `mirror-afp-devel@7731745138`, `easycrypt@ce19cb6cba`) was directly inspected, and all core algorithms (open-game lenses, exact vs. `float64` VCG, EIP-1559) were executed via standalone Python 3.13 probes; GHC, OCaml/EasyCrypt, and Isabelle/HOL builds were not invoked locally.
- **Repeated-Game Dynamic Equilibria and Folk-Theorem Collusion (`not examined`):** `Open Games` equilibrium semantics in Section 1 and `EIP-1559` / `Chung–Shi` single-block `UIC`/`MIC`/`1-SCP` analysis in Section 3 analyze one-shot or finite-horizon sequential stages; infinitely repeated games (e.g., multi-block `base_fee` manipulation across consecutive Ethereum blocks or trigger-strategy cartels) introduce distinct strategic deviations not verified here.
- **Multi-Dimensional MEV / Transaction Reordering (`known not to apply` to `EIP-1559` `UIC`):** Roughgarden's uncongested `UIC`/`MIC`/`OCA` proof for `EIP-1559` assumes single-parameter user valuations that depend only on *inclusion* in the block, not on *intra-block ordering* relative to other transactions. For DeFi swaps, arbitrage, and liquidations where value depends strongly on transaction position (`MEV`), `EIP-1559` alone does *not* provide order-fairness or `UIC`.
- **Unbounded Continuous Strategy Verification in `open-games-hs` (`unsupported`):** `open-games-hs` computes `optimalPlay` via finite list maximization (`maximumBy` over `[y]`, `BayesianGames.hs` L94) in IEEE-754 `Double`; it cannot certify universal `DSIC`/`BIC` over continuous real-valued bid intervals without external symbolic/SMT or theorem-prover integration.
- **Automated SMT Synthesis of Nonlinear Mechanism Proofs (`unknown`):** While `DSIC` for fixed small linear/discrete auctions can be discharged by SMT (`QF_LRA`/`QF_NIA`), automated SMT/relational synthesis for general multi-dimensional revenue-optimal mechanisms (beyond Myerson's 1D virtual-value characterization) remains an open research boundary.

## Evidence

### Primary Repositories and Inspected Symbols (Observed `2026-11-19`)

1. **`CyberCat-Institute/open-games-hs` @ `e14be50f7f4cb250ac9a03d907996ee97ec48908`:**
   - `modules/engine/src/OpenGames/Engine/Optics.hs` L22–50 (`Optic`, `Precontext`, `Context` with `cmap`, `//`, `\\`, `ContextAdd`).
   - `modules/engine/src/OpenGames/Engine/OpenGames.hs` L21–55 (`data OpenGame`, `lift`, `reindex`, `(>>>)`, `(&&&)`).
   - `modules/engine/src/OpenGames/Engine/Optics/StochasticStateful.hs` L43–71 (`StochasticStatefulContext`, latent type `z`, `cmap`/`//`/`\\`/`prl`/`prr`).
   - `modules/engine/src/OpenGames/Engine/OpenGames/BayesianGames.hs` L61–120 (`DiagnosticInfoBayesian`, `deviationsInContext` with `Double` `epsilon` check and `maximumBy`, `dependentDecision`, `dependentRoleDecision`).
   - `modules/modelling/src/OpenGames/BayesianModelling/AtomicGames.hs` L20–90 (`[opengame| ... |]` DSL definitions).
2. **`isabelle-prover/mirror-afp-devel` @ `773174513872254f8efe1cb3a3ce64037f0b1da6`:**
   - `thys/Vickrey_Clarke_Groves/CombinatorialAuction.thy` L41–75, L751 (`chosenAllocationEquivalence`), L757 (`tiebidsBridgingLemma`), L792 (`resolvingBidBridgingLemma`), L826 (`tiebreakingGivesSingleton`).
   - `thys/Vickrey_Clarke_Groves/StrictCombinatorialAuction.thy` L55–108 (`allAllocations`, `winningAllocationsRel`, `winningAllocationAlg`, `alpha`, `paymentsRel`, `paymentsAlg`).
   - `thys/Vickrey_Clarke_Groves/CombinatorialAuctionCodeExtraction.thy` L25–58 (`HOL-Library.Code_Target_Nat`, `HOL-Library.Code_Target_Int`, `0::integer`, `export_code vcgaAlg payments allocationPrettyPrint in Scala`).
3. **`ethereum/EIPs` @ `b055feec322fbc37e9d77a393a50b3ff56b31c92`:**
   - `EIPS/eip-1559.md` L135–142 (`gas_limit`, `base_fee_per_gas`), L193–195 (`BASE_FEE_MAX_CHANGE_DENOMINATOR`), L212–234 (`priority_fee_per_gas`, `effective_gas_price`, base fee burn vs. `block.author` priority fee credit).
4. **`EasyCrypt/easycrypt` @ `ce19cb6cbab4951e58553c36128e8a19f2f90c6a`:**
   - Reference `pRHL` verification platform used by Barthe et al. (`WINE 2016`).

### Peer-Reviewed Literature

- **Neil Ghani, Jules Hedges, Viktor Winschel, Philipp Zahn**, *"Compositional Game Theory"*, **ACM/IEEE LICS 2018**, `DOI: 10.1145/3209108.3209165`, `arXiv:1603.04641` (v3, 2018).
- **Matteo Capucci, Bruno Gavranović, Jules Hedges, Eigil Fjeldgren Rischel**, *"Towards Foundations of Categorical Cybernetics"*, **ACT 2021 / EPTCS 372**, 2022, `DOI: 10.4204/EPTCS.372.17`, `arXiv:2105.06332` (v2, 2022).
- **Gilles Barthe, Marco Gaboardi, Emilio Jesús Gallego Arias, Justin Hsu, Aaron Roth, Pierre-Yves Strub**, *"Computer-Aided Verification in Mechanism Design"*, **WINE 2016**, `arXiv:1502.04052` (v5, 2016).
- **Marco B. Caminati, Manfred Kerber, Christoph Lange, Colin Rowat**, *"Sound Auction Specification and Implementation"*, **ACM EC 2015**, `DOI: 10.1145/2764468.2764511`.
- **Tim Roughgarden**, *"Transaction Fee Mechanism Design"*, **ACM EC 2021** (`DOI: 10.1145/3465456.3467591`) and **Journal of the ACM** 71(4), Article 30, 2024 (`DOI: 10.1145/3651158`), `arXiv:2106.01340` (v3, 2023).
- **Hao Chung, Elaine Shi**, *"Foundations of Transaction Fee Mechanism Design"*, **ACM-SIAM SODA 2023**, pp. 3856–3899, `DOI: 10.1137/1.9781611977554.ch150`, `arXiv:2111.03151` (v3, 2022).

### Executable Micro-Probe (`Python 3.13.15`, Executed `2026-11-19`)

Self-contained reproduction script (core Open Games lens combinators, IEEE-754 `float64` VCG DSIC counterexample, and EIP-1559 finite-block probe):

```python
#!/usr/bin/env python3
from fractions import Fraction

# 1. Reproducible IEEE-754 float64 combinatorial VCG DSIC counterexample:
#    Goods {A, B}; Bidder 0 true v0({A})=1; Bidder 1 b1({B})=1e16; Bidder 2 b2({AB})=1e16.
#    Tie-breaker prefers whole (2->AB) over split (0->A, 1->B) on equal welfare.
def vcg_3bidder(b0_A, use_float=True):
    b1_B = 1e16 if use_float else Fraction(10**16)
    b2_AB = 1e16 if use_float else Fraction(10**16)
    w_split = b1_B + (float(b0_A) if use_float else Fraction(b0_A))
    winner = "split" if w_split > b2_AB else "whole"
    p0 = (max(b2_AB, b1_B) - b1_B) if winner == "split" else (0.0 if use_float else Fraction(0))
    u0 = (1.0 - float(p0)) if winner == "split" else 0.0
    return winner, w_split, b2_AB, p0, u0

print("Exact truth b0=1.0:  ", vcg_3bidder(1, use_float=False))
print("f64   truth b0=1.0:  ", vcg_3bidder(1.0, use_float=True))
print("f64   misrep b0=1.5: ", vcg_3bidder(1.5, use_float=True))
```

Observed full output (from complete probe including Open Games sequential/parallel lens evaluator, 729-pair exact Fraction combinatorial VCG relational check, `float64` DSIC violation, and EIP-1559 / `1-SCP` simulation):
```text
=== 3A. Compositional Open Games (Bidirectional Play/Coplay Lenses) ===
  Non-credible threat (Out, Fight)  : all_SPE=False  diagnostics=[('Entrant', True, 0, 0, 'Out'), ('Incumbent@In', False, -1, 1, 'Accommodate')]
  SPE (In, Accommodate)             : all_SPE=True  diagnostics=[('Entrant', True, 1, 1, 'In'), ('Incumbent@In', True, 1, 1, 'Accommodate')]
  First-Price Auction      truthful=(7,5): eq=False  details=[('Bidder1(v=7)', 'eq=False', 'u=0', 'best_u=2', 'best_bid=5'), ('Bidder2(v=5)', 'eq=True', 'u=0', 'best_u=0', 'best_bid=0')]
  Second-Price (Vickrey)   truthful=(7,5): eq=True  details=[('Bidder1(v=7)', 'eq=True', 'u=2', 'best_u=2', 'best_bid=5'), ('Bidder2(v=5)', 'eq=True', 'u=0', 'best_u=0', 'best_bid=0')]

=== 3B. Relational 2-Execution DSIC Verifier: Exact Rational VCG vs IEEE-754 Float64 Counterexample ===
  Exact Fraction combinatorial VCG relational check: 729 (true, misreport) pairs checked, DSIC violations = 0
  Exact Fraction (truth b0=1.0):   winner=split, p0=0, u0=1.0
  IEEE-754 f64   (truth b0=1.0):   winner=whole (w_split=10000000000000000.0 vs w_whole=10000000000000000.0), p0=0.0, u0=0.0
  IEEE-754 f64   (misrep b0=1.5):  winner=split (w_split=10000000000000002.0 vs w_whole=10000000000000000.0), p0=0.0, u0=1.0
  DSIC VIOLATION IN IEEE-754 f64:  u0(misreport=1.5) - u0(truth=1.0) = +1.0 > 0!

=== 3C. EIP-1559 Finite-Block UIC Breakdown & 1-SCP Side-Contract Counterexample ===
  EIP-1559 uncongested (cap=5, r=100): included=['U1', 'U2', 'U3'], U1 pays 101, u_U1=49
  EIP-1559 congested   (cap=1, r=100): truthful tip=50 -> u_U1=0; shaded tip=31 -> u_U1=19 (UIC violated by +19)
  Burned 2nd-price TFM (cap=1): honest joint(M+U1)=20, 1-SCP censor-U2 coalition joint=150 (gain=+130)
```

## Revalidation

1. **Open Games Engine Type Signatures:** Diff `modules/engine/src/OpenGames/Engine/{Optics.hs,OpenGames.hs,OpenGames/BayesianGames.hs}` in `CyberCat-Institute/open-games-hs` against `e14be50f7f4cb250ac9a03d907996ee97ec48908` to check whether `Payoff` remains `Double` or adds exact rational/symbolic backends and whether `OpenGame` sequential `(>>>)` / parallel `(&&&)` laws remain unchanged.
2. **Isabelle/HOL VCG Code Extraction:** Check `thys/Vickrey_Clarke_Groves/CombinatorialAuctionCodeExtraction.thy` in `isabelle-prover/mirror-afp-devel` against `773174513872254f8efe1cb3a3ce64037f0b1da6` to confirm `Code_Target_Int` arbitrary-precision extraction and bridging lemmas (`chosenAllocationEquivalence`, `resolvingBidBridgingLemma`, `tiebreakingGivesSingleton`) remain intact.
3. **Numerical `DSIC` Regression Gate:** Run the 15-line `vcg_3bidder` counterexample probe against any candidate auction/allocation solver whenever floating-point arithmetic, fixed-point truncation, or heuristic/approximate MIP winner-determination is introduced; any positive utility delta $u_0(b'_0) - u_0(v_0) > 0$ falsifies `DSIC`.
4. **Protocol Fee-Market Changes:** Diff `EIPS/eip-1559.md` (and multi-dimensional fee market successors such as blob fee markets in `EIP-4844`) against `b055feec322fbc37e9d77a393a50b3ff56b31c92` to check whether priority-fee allocation rules or cryptographic encrypted-mempool / multi-proposer extensions alter the finite-block `UIC` + `1-SCP` trade-off.
