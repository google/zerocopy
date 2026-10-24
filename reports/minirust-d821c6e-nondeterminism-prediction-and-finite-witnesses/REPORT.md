# MiniRust Demonic/Angelic Nondeterminism (`pick`/`predict`), Finite Exposed-Provenance Domains, and Prefix-Coherent Causal Safety Strategies (`d821c6e` / `15200eb`)

## Summary

MiniRust (`minirust/minirust` at commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`) models operational nondeterminism through two primitives in `specr` (`minirust/specr` at commit `15200eb5e676e2ee91f43bd79e674f8fc32e5348`): demonic choice `pick` (where a program is safe only if **all** satisfying choices avoid undefined behavior) and angelic prediction `predict` (used by `IntPtrCast::int2ptr` in `spec/mem/intptrcast.md`, where a program is safe if **some** satisfying choice avoids subsequent undefined behavior).

This report documents a source audit of `minirust/minirust` and `minirust/specr` combined with a mechanized Lean 4 (`v4.34.1`) and executable Python investigation of mixed demonic/angelic nondeterminism, unbounded vs. finite angelic branching, and prefix-coherent safety strategies. Across 4 Lean modules (`UnboundedWitness.lean`, `Execution.lean`, `FiniteCausalStrategies.lean`, `FiniteStrategyDiscriminators.lean` — 45 kernel-checked `#print axioms` theorem audits) and an exhaustive finite-witness Python probe (`witness_probe.py` — 11,310 positive copy cases and 161,776 primitive events), all re-verified on `2026-10-24`, the investigation establishes:

1. **Upstream `libspecr` runtime limitation vs. specification semantics (`libspecr/src/nondet.rs`)**:
   In `minirust/specr` at `15200eb5e676e2ee91f43bd79e674f8fc32e5348`, `pick` is implemented by rejection-sampling at most 50 random candidates via `rand::thread_rng()` before panicking (`panic!("unable to find suitable element in pick")`), and `predict` unconditionally panics with `unimplemented!()`. Thus `libspecr` cannot execute integer-to-pointer casts (`int2ptr`) or verify universal demonic safety.
2. **State-indexed finiteness of `IntPtrCast::int2ptr` eligible predictions (`spec/mem/intptrcast.md`)**:
   In `minirust/minirust` at `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`, `predict` is invoked at a single callsite across the entire specification: `IntPtrCast::int2ptr` (`spec/mem/intptrcast.md:45-53`). Its predicate `|prov: Option<Provenance>| { if let Some(prov) = prov { self.exposed.contains(prov) } else { true } }` restricts eligible answers at any machine state after $n$ prior `expose` operations to a finite domain of size at most $n + 1$: $\text{None} \cup \{\text{Some}(p) \mid p \in \text{self.exposed}\}$.
3. **Failure of $\omega$-continuity and quantifier exchange for unbounded angelic prediction (`UnboundedWitness.lean`, `Execution.lean`)**:
   When an angelic choice ranges over an infinite domain (such as an unbounded `Nat` countdown before UB), every finite prefix bound $k$ can have a safe witness ($\forall k,\; \exists w,\; \text{SafeFor}(k, w)$) while no single upfront witness survives all prefixes ($\neg \exists w,\; \forall k,\; \text{SafeFor}(k, w)$). In the monotone safety game `CountdownState`, the $\omega$-intersection of all finite-horizon safety approximants (`OmegaIntersection`) contains `.root`, yet `OmegaIntersection` is **not** postfixed (`omega_intersection_not_postfixed`) and `.root` is outside the greatest safety fixed point (`finite_approximants_do_not_establish_greatestSafety`).
4. **Sufficiency of per-state finite legal angelic action lists for extracting one prefix-coherent causal strategy (`FiniteCausalStrategies.lean`, `FiniteStrategyDiscriminators.lean`)**:
   When the legal angelic actions at each state are given by an explicit finite list `legalActions : State → List Action` (even when the state space and demonic branching are infinite), the $\omega$-intersection `Winning game` of the finite-horizon safety approximants `Approximant game n` **is** a postfixed invariant (`winning_postfixed`, `winning_unfold`) via a finite-list König/pigeonhole lemma (`finite_list_intersection`). Classical selection extracts a **single** state-indexed strategy `extractedStrategy : State → Option Action` whose resolved transition relation satisfies both `NoUB` and `ReachableProgress` (`extracted_noUB`, `extracted_progress`, `winning_iff_classified_strategy`). Operational discriminators in `FiniteStrategyDiscriminators.lean` separate one-step committed responses (`responseGame`) from non-returning binary search (`searchGame`, where `alwaysSearch` diverges safely in `.search` without ever committing a countdown witness).

## Applicability

- **Upstream specification subjects**:
  - `minirust/minirust` at commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` (retained archive SHA-256 `0b808e620296bde607ed6cf74642f39a023c2dbf9fe842d458fdfb69392913c0`):
    - `spec/mem/intptrcast.md` (1,838 bytes; Git blob OID `241ba96f5498bde49bf9b8c489bafcf12ba98b07`; SHA-256 `ddb67b4ef74e05568fced9f1460730b595b4584d73d48c93fd326ff5dd7378b6`)
    - `spec/lang/machine.md` (14,940 bytes; Git blob OID `12c78fcbb23d59c771ce006a74ee333a0266e5a8`; SHA-256 `121c624125adf8d8d988b6d088d8e85687e8a275ee703a80e486dcb05dfbd91c`)
    - `spec/lang/step/intrinsics.md` (20,288 bytes; Git blob OID `0a2eb8e67affb71bd5b73375c6f9483dae64b469`; SHA-256 `261fe197e65556bae74cf209c64c5913fdd713f3a57d2bf56f0b1fb0e3a34be8`)
    - `README.md` (17,336 bytes; Git blob OID `1fa12c10854fbf28f3c00ed81b1b696d374823cb`; SHA-256 `0cf8eef4f7ea8163dc9746e8b148206d4722be5fd3106cb9c16b3f4b7efb4cb8`)
  - `minirust/specr` at commit `15200eb5e676e2ee91f43bd79e674f8fc32e5348` (archive SHA-256 `7e39738319f77a43fd0ce8e185888306b3a777f7b3f9d3234ec1802b9da5e220`) and `libspecr 0.1.41`:
    - `libspecr/src/nondet.rs` (Git blob OID `95d1779861cccaaeeee767c7571e88debcf8433b`; SHA-256 `562f6e5b1ebc0abb282c846643d3fe7f351f55fdbd0a0b6571f899be7be5b4f1`)
    - `libspecr/src/set/mod.rs` (Git blob OID `81875b2fd83ffe3cc16a031dafa64515fb5098a7`; SHA-256 `538c9889c8068241b47d296e5cda7336fcad0bfc6f5489d12402242b32ecb1a7`)
    - `libspecr/src/set/func.rs` (Git blob OID `666a20a8bec62bf018d4198a40e9749114d00ef9`; SHA-256 `010cbcea47580571cebc89c1238d3d2c84000701b30ee783c62294299164bdad`)
    - `libspecr/src/set/iter.rs` (Git blob OID `abc15086986ab1a4f5c50e032c7289408f013433`; SHA-256 `7ef15faf2e2d658f88f13d19684322261f82f8efd3bc6ac96ee34aa298ccebf9`)
- **Mechanized & executable verification subjects**:
  - Lean `v4.34.1` (`commit 5045d0056413266e57c625dcd7c365b10e377c52`, `x86_64-unknown-linux-gnu`), using only `{propext, Quot.sound, Classical.choice}`.
  - Python 3 (`witness_probe.py`) for exhaustive finite byte-machine witness and negative-control enumeration.

## Findings

### 1. Upstream `pick`/`predict` Specification vs. `libspecr` Runtime (`nondet.rs`, `intptrcast.md`)

**Basis**: `source` and `documentation`

#### 1.1 `libspecr/src/nondet.rs` Runtime Implementation

In `minirust/specr` at `15200eb5e676e2ee91f43bd79e674f8fc32e5348`, `libspecr/src/nondet.rs` defines the executable traits and functions backing MiniRust's `pick` and `predict`:

- **`pick` (`libspecr/src/nondet.rs:32-45`)**:
  ```rust
  pub fn pick<T: Pick>( mut f: impl FnMut(T) -> bool) -> T {
      let mut rng = rand::thread_rng();
      for _ in 0..50 {
          let t = T::pick(&mut rng);
          if f(t) {
              return t;
          }
      }
      panic!("unable to find suitable element in pick");
  }
  ```
  Instead of exploring all demonic branches, `libspecr::pick` draws up to 50 pseudo-random samples and panics if none satisfies `f` (for example, when an alignment requirement is sparse in `0..T::MAX_ADDR`).
- **`predict` (`libspecr/src/nondet.rs:47-50`)**:
  ```rust
  pub fn predict<T: Predict>(_f: impl FnMut(T) -> bool) -> T {
      unimplemented!()
  }
  ```
  `predict` is unconditionally `unimplemented!()` in `libspecr`.

#### 1.2 State-Indexed Finite Domain of `IntPtrCast::int2ptr` (`spec/mem/intptrcast.md`)

In `minirust/minirust` at `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`:

- `README.md:332-360` describes `pick` as demonic choice (universal quantification for safety) and `predict` as angelic choice (existential quantification for safety: a program has UB iff **every** suitable prediction leads to UB).
- Across the entire `spec/` tree at `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`, `predict` has a **single** callsite, in `IntPtrCast<Provenance>::int2ptr` (`spec/mem/intptrcast.md:45-53`):
  ```rust
  pub fn int2ptr(&self, addr: Address) -> ThinPointer<Provenance> {
      let provenance = predict(|prov: Option<Provenance>| {
          if let Some(prov) = prov {
              self.exposed.contains(prov)
          } else {
              true
          }
      });
      ThinPointer { addr, provenance }
  }
  ```
- `IntPtrCast<Provenance>` (`spec/mem/intptrcast.md:10-43`) maintains `exposed: Set<Provenance>`, initialized to `Set::new()` (`IntPtrCast::new` at `intptrcast.md:19-23`, invoked at machine creation in `spec/lang/machine.md:113`) and mutated solely by `self.exposed.insert(ptr.provenance)` inside `IntPtrCast::expose` (`intptrcast.md:27-31`, invoked by the `expose` intrinsic when casting a pointer with `Some(prov)` to an integer).
- Because `Set<T>` in `libspecr/src/set/{mod.rs,func.rs}` wraps `GcCow<BTreeSet<T>>` starting from `BTreeSet::new()` and adding at most one element per `insert`, after $n$ prior `expose` transitions on a finite execution prefix, the set of `Option<Provenance>` values satisfying `int2ptr`'s suitability predicate at that state is finite of cardinality at most $n + 1$:
  $$\mathcal{A}(s) = \{\text{None}\} \cup \{\text{Some}(p) \mid p \in \text{exposed}(s)\}, \qquad |\mathcal{A}(s)| \le n + 1.$$

### 2. Unbounded Angelic Prediction and Failure of $\omega$-Continuity (`UnboundedWitness.lean`, `Execution.lean`)

**Basis**: `execution` and `derived`

When an angelic prediction ranges over an infinite set (such as `Nat`) rather than a state-indexed finite list, finite-horizon safety approximants fail to converge to a single prefix-coherent witness:

1. **Failure of quantifier exchange (`UnboundedWitness.lean`, `Execution.Prediction`)**:
   - In [`support/UnboundedWitness.lean`](support/UnboundedWitness.lean) (`SafeUpTo bound witness := bound ≤ witness`), `every_finite_bound_has_witness` proves $\forall b : \mathbb{N},\; \exists w : \mathbb{N},\; b \le w$, whereas `no_one_witness_covers_all_prefixes` proves $\neg \exists w : \mathbb{N},\; \forall b : \mathbb{N},\; b \le w$, and `finite_witnesses_do_not_imply_coherent_witness` packages the conjunction with zero axioms (`does not depend on any axioms`).
   - In [`support/Execution.lean:169-279`](support/Execution.lean#L169-L279), `Execution.Prediction` embeds this into a state transition system `CountdownState` (`.root` steps angelically to `.ticks n` for any $n : \mathbb{N}$, which then counts down deterministically `.ticks (n + 1)` $\to$ `.ticks n` until the bad state `.ticks 0`):
     - `root_in_every_approximant` ([`Execution.lean:223-227`](support/Execution.lean#L223-L227)): $\forall k,\; \mathrm{Approximant}\;k\;\mathrm{.root}$ holds because at horizon $k$, `.root` can choose `.ticks k`.
     - `omega_intersection_not_postfixed` ([`Execution.lean:235-239`](support/Execution.lean#L235-L239)): $\mathrm{OmegaIntersection}(s) := \forall k,\; \mathrm{Approximant}\;k\;s$ is **not** a postfixed point of the monotone safety transformer `countdownF`, because $\mathrm{OmegaIntersection}(\mathrm{.root})$ holds while $\neg \mathrm{OmegaIntersection}(\mathrm{.ticks}\;n)$ for every $n$.
     - `finite_approximants_do_not_establish_greatestSafety` ([`Execution.lean:275-277`](support/Execution.lean#L275-L277)):
       $$\mathrm{OmegaIntersection}\;\mathrm{.root} \;\wedge\; \neg \mathrm{GreatestSafety}\;\mathrm{.root}.$$
2. **Causal vs. prophetic quantifier order (`Execution.ChoiceScope`, [`Execution.lean:283-312`](support/Execution.lean#L283-L312))**:
   Theorem `order_and_information_discriminator` proves $\neg \mathrm{CausalBefore} \wedge \mathrm{PropheticBefore} \wedge \mathrm{CausalAfter}$ for a single-bit game where an adversary chooses `demonic : Bool`:
   - `CausalBefore` ($\exists p : \mathrm{Bool},\; \forall d : \mathrm{Bool},\; p = d$) is false (`causal_before_impossible`), and an adversary that observes the prediction (`observingAdversary p := !p`) defeats every blind or pre-committed prediction (`observing_adversary_defeats_every_prediction`).
   - `PropheticBefore` ($\forall d : \mathrm{Bool},\; \exists p : \mathrm{Bool},\; p = d$) and `CausalAfter` ($\exists f : \mathrm{Bool} \to \mathrm{Bool},\; \forall d,\; f(d) = d$) both hold, demonstrating that whether `predict` can depend on future demonic choices (`PropheticBefore`) vs. only current machine state (`CausalBefore` / `CausalAfter`) is an independent semantic commitment not settled by finiteness of the answer set alone.

### 3. Finite Per-State Legal Actions and Extraction of One Coherent Causal Strategy (`FiniteCausalStrategies.lean`, `FiniteStrategyDiscriminators.lean`)

**Basis**: `execution` and `derived`

[`support/FiniteCausalStrategies.lean`](support/FiniteCausalStrategies.lean) formalizes an alternating full-information safety game `Game State Action` ([`FiniteCausalStrategies.lean:22-28`](support/FiniteCausalStrategies.lean#L22-L28)) where:
- `legalActions : State → List Action` supplies an explicit finite list of legal angelic actions at each state (without requiring `State`, `Action`, or demonic successor sets `{after | game.raw before action after}` to be finite or inhabited),
- `GoodAction game X state action` requires `action ∈ game.legalActions state`, `Enabled game state action` ($\exists \text{after},\; \text{raw}\;\text{state}\;\text{action}\;\text{after}$), and universal demonic successor membership ($\forall \text{after},\; \text{raw}\;\text{state}\;\text{action}\;\text{after} \to X\;\text{after}$),
- `Transformer game X state` requires `¬ game.bad state ∧ (game.allowed state ∨ ∃ action, GoodAction game X state action)`, and
- `Winning game state := ∀ n, Approximant game n state`.

The module proves:

1. **Finite-list intersection and postfixedness of `Winning` (`finite_list_intersection`, `winning_postfixed`, `winning_unfold`, [`FiniteCausalStrategies.lean:91-156`](support/FiniteCausalStrategies.lean#L91-L156))**:
   Given any descending family of predicates $P : \mathbb{N} \to \alpha \to \mathrm{Prop}$ ($P(n+1, a) \to P(n, a)$) and a finite list `choices : List α`, if $\forall n,\; \exists a \in \text{choices},\; P(n, a)$, then $\exists a \in \text{choices},\; \forall n,\; P(n, a)$. Applying `finite_list_intersection` to `game.legalActions state` proves that `Winning game` is postfixed (`winning_postfixed`) and satisfies the fixed-point equation `Winning game state ↔ Transformer game (Winning game) state` (`winning_unfold`).
2. **Single-strategy extraction and exact `Winning ↔ Verified` characterization (`extracted_noUB`, `extracted_progress`, `winning_iff_classified_strategy`, [`FiniteCausalStrategies.lean:164-288`](support/FiniteCausalStrategies.lean#L164-L288))**:
   Using `Classical.choose`, `extractedStrategy : State → Option Action` selects `none` at `allowed` states and `some action` satisfying `GoodAction game (Winning game) state action` at non-allowed `Winning` states. For the single resolved transition system `Resolved game (extractedStrategy game)` (used uniformly across all reachable steps without re-choosing per horizon):
   - Every reachable state from a `Winning` initial state remains in `Winning` (`extracted_reachable_winning`), avoids `bad` (`extracted_noUB`), and either stops at an `allowed` state or takes an enabled legal action (`extracted_progress`).
   - Conversely, any single policy `policy : State → Option Action` that is `Verified` (`NoUB ∧ ReachableProgress`) satisfies `Approximant game n` for every $n$ (`verified_strategy_approximant`, axiom-free), yielding the exact equivalence (`winning_iff_classified_strategy`):
     $$\mathrm{Winning}\;\mathit{game}\;\mathit{initial} \iff \exists \mathit{policy} : \mathrm{State} \to \mathrm{Option}\;\mathrm{Action},\; \mathrm{StopPolicy}\;\mathit{game}\;\mathit{policy} \wedge \mathrm{Verified}\;(\mathrm{Resolved}\;\mathit{game}\;\mathit{policy})\;\mathit{game.bad}\;\mathit{game.allowed}\;\mathit{initial}.$$
3. **Operational discriminators (`FiniteStrategyDiscriminators.lean`)**:
   - **Repeated one-step response against unbounded demonic requests (`responseGame`, [`FiniteStrategyDiscriminators.lean:15-50,94-183`](support/FiniteStrategyDiscriminators.lean#L15-L50))**: At `.ready request commits`, the angelic player chooses a boolean from `[false, true]` while the demonic adversary simultaneously chooses any next request `next : Nat`. Theorem `response_extracted_answer` proves that `extractedStrategy` selects `some (expected request)` at every state, and `response_actual_run` constructs an infinite safe resolved execution for any demonic request stream `requests : Nat → Nat`.
   - **Binary search vs. atomic Nat prediction (`searchGame`, [`FiniteStrategyDiscriminators.lean:52-91,185-320`](support/FiniteStrategyDiscriminators.lean#L52-L91))**: Replacing an unbounded one-step `Nat` choice with a binary action list `[false, true]` at `.search candidate` (`false` grows `.search (candidate + 1)`; `true` commits `.ticks candidate` which counts down to `.ticks 0` = `Bad`) makes `.search 0` a `Winning` state (`search_winning`), **not** because a safe committed `Nat` witness exists, but because `alwaysSearch` diverges safely in `.search` forever without ever committing (`always_search_verified`, `always_search_never_commits`, `classified_policy_cannot_reach_commit`, `finite_search_is_not_an_atomic_witness`). Moreover, `artificial_countdown_stop` ([`FiniteStrategyDiscriminators.lean:291-305`](support/FiniteStrategyDiscriminators.lean#L291-L305)) proves that `ReachableProgress` is indispensable: a policy that returns `none` at `.ticks (remaining + 1)` is vacuously `NoUB` because it halts early, but is rejected by `Verified`.

### 4. Exhaustive Finite-Witness Byte-Machine Probe (`witness_probe.py`)

**Basis**: `execution`

[`support/witness_probe.py`](support/witness_probe.py) (re-executed on `2026-10-24`, output archived in [`support/witness-probe-results.json`](support/witness-probe-results.json)) exhaustively tests two concrete finite-state operational models (`HistoryFree` and `AliasSensitive`) of a byte-copy loop over lengths $0 \le n \le 3$, source byte alphabet $\{0, 1, 2, 255\}$, destination cell alphabet $\{\text{None}, 0, 255\}$, and slack offsets:

- Across all **11,310** positive well-separated copy configurations and **161,776** executed primitive read/write events, every step preserves the loop invariant and produces the exact final byte slice.
- Both models reject all 6 negative-control families at the exact expected diagnostic boundary (`uninitialized-source` $\to$ `"uninitialized"`, `invalid-bool-at-production` $\to$ `"invalid-bool"`, `out-of-bounds-source` $\to$ `"bounds"`, `stale-provenance` $\to$ `"pointer-arithmetic"`, `absent-provenance` $\to$ `"provenance"`, `missing-destination-authority` $\to$ `"authority"`), while permitting zero-length copies with absent provenance (`zero_length_absent_provenance: "success with zero events, both models"`).
- A concrete discriminator (`distinct_model_witness`: `HistoryFree = "success"`, `AliasSensitive = "authority"`) separates history-free spatial separation from alias-sensitive tag invalidation when a foreign read freezes destination write authority before the copy loop.

## Boundaries

- **Known not to apply**:
  - Finite-horizon safety ($\forall k,\; \mathrm{Approximant}\;k\;s$) does **not** imply existence of a coherent safety strategy when angelic branching is infinite (`Execution.Prediction.finite_approximants_do_not_establish_greatestSafety`, `UnboundedWitness.no_one_witness_covers_all_prefixes`).
  - Replacing an unbounded one-step choice with a binary increment/commit loop (`searchGame`) does **not** produce a committed `Nat` witness; every `Verified` strategy on `searchGame` avoids commitment by diverging in `.search` (`FiniteStrategyDiscriminators.classified_policy_cannot_reach_commit`).
  - Plain `NoUB` without `ReachableProgress` does **not** prevent a strategy from halting artificially before a mandatory countdown to UB (`FiniteStrategyDiscriminators.artificial_countdown_stop`).
- **Not examined in this package**:
  - Prophetic or partial-information strategies where `predict` must guess a future demonic address choice not yet recorded in the current state (`ChoiceScope.CausalBefore` vs. `PropheticBefore` in `Execution.lean` isolates the logical distinction, while `FiniteCausalStrategies.lean` is strictly a full-state causal game).
  - Computational strategy synthesis: `extractedStrategy` in `FiniteCausalStrategies.lean` uses `Classical.choose` (`Classical.choice`) over an infinite proof object `Winning game state`.
- **Unsupported**:
  - Runtime execution of `predict` in `minirust/specr` (`libspecr/src/nondet.rs:47-50`) is `unimplemented!()`.
- **Unknown**:
  - Whether upstream MiniRust will formalize `predict` in `spec/mem/intptrcast.md` as a causal state-indexed choice or a prophetic execution-trace existential quantifier.

## Evidence

All Lean modules, the Python finite-witness probe script, and the fresh execution JSON ledgers are archived in [`support/`](support/):

- Lean verification ledgers:
  - [`support/lean-verification-results.json`](support/lean-verification-results.json) (`Execution`, `FiniteCausalStrategies`, `FiniteStrategyDiscriminators`)
  - [`support/unbounded-witness-results.json`](support/unbounded-witness-results.json) (`UnboundedWitness`)
- Python probe output:
  - [`support/witness-probe-results.json`](support/witness-probe-results.json) (`witness_probe.py`)
- Cross-platform `.olean` object reproducibility: Compiling `Execution.lean`, `FiniteCausalStrategies.lean`, and `FiniteStrategyDiscriminators.lean` on `x86_64-unknown-linux-gnu` produced `.olean` artifacts with SHA-256 digests (`80245392...`, `d3bb2728...`, `38de2bbb...`) **byte-for-byte identical** to the previously recorded `arm64-apple-darwin` `.olean` digests.

| Artifact / Module | Support File | Source SHA-256 | `.olean` SHA-256 / Output | Flags / Runtime | Wall (s) | Audited Theorems / Cases |
| :--- | :--- | :--- | :--- | :--- | ---: | ---: |
| `UnboundedWitness` | [`support/UnboundedWitness.lean`](support/UnboundedWitness.lean) | `48db0320d60dce7dd6536805c0e05dbd3aa76b1ab3e8ec3db9659d219cd817db` | [`support/unbounded-witness-results.json`](support/unbounded-witness-results.json) | `lean -j1 -M768` | 0.3349 | 3 (0 axioms) |
| `AnnealResearch.Execution` | [`support/Execution.lean`](support/Execution.lean) | `cbe3713b840a8a61b617f2ababaa02e4ad97c81628db7d55fc3641611365bf3a` | `80245392778049029caff66583762021428113a0be089311a3843fc03f8c9125` | `lean -j1 -M768` | 0.5981 | 16 |
| `AnnealResearch.FiniteCausalStrategies` | [`support/FiniteCausalStrategies.lean`](support/FiniteCausalStrategies.lean) | `f21a7c132251ad53eb7b4ff5a9cc68176dbcaef1888238a37db7620c4f3fca9d` | `d3bb27282dffd1adb85dc4e92bf7b40371d28353a35f361c31587a60e24595c9` | `lean -j1 -M768` | 0.5572 | 14 |
| `AnnealResearch.FiniteStrategyDiscriminators` | [`support/FiniteStrategyDiscriminators.lean`](support/FiniteStrategyDiscriminators.lean) | `a35860549a6057db1602256953d808d40eda0640baa76c25d9cc949431449a3e` | `38de2bbb19ee3f202828bda50df35584ee55566531abff85703175a0861bfd5d` | `lean -j1 -M1024` | 0.7064 | 12 |
| `witness_probe.py` | [`support/witness_probe.py`](support/witness_probe.py) | `bc2bd2bf89a8703ec11bf5d65c32d3b910ba68697c090e442f0160df3c6be52c` | [`support/witness-probe-results.json`](support/witness-probe-results.json) | `python3` | 0.1221 | 11,310 cases / 161,776 events |

## Revalidation

To re-verify all Lean modules and the Python witness probe from the self-contained [`support/`](support/) directory:

```bash
python3 - <<'EOF'
import os, subprocess, tempfile

support_dir = "reports/minirust-d821c6e-nondeterminism-prediction-and-finite-witnesses/support"

# 1. Standalone UnboundedWitness.lean
subprocess.run(["lean", "-j1", "-M768", os.path.join(support_dir, "UnboundedWitness.lean")], check=True)
print("OK: UnboundedWitness")

# 2. Execution, FiniteCausalStrategies, FiniteStrategyDiscriminators
with tempfile.TemporaryDirectory() as tmp:
    mod_dir = os.path.join(tmp, "AnnealResearch")
    os.makedirs(mod_dir, exist_ok=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = tmp
    for mod, mem in [
        ("Execution", "-M768"),
        ("FiniteCausalStrategies", "-M768"),
        ("FiniteStrategyDiscriminators", "-M1024"),
    ]:
        src = os.path.join(support_dir, f"{mod}.lean")
        olean = os.path.join(mod_dir, f"{mod}.olean")
        subprocess.run(["lean", "-j1", mem, "-o", olean, src], env=env, check=True)
        print(f"OK: AnnealResearch.{mod}")

# 3. Finite witness Python probe
subprocess.run(["python3", os.path.join(support_dir, "witness_probe.py")], check=True)
print("OK: witness_probe.py")
EOF
```

Revalidate this report when:
- Updating `minirust/minirust` beyond `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` (especially `spec/mem/intptrcast.md`),
- Updating `minirust/specr` beyond `15200eb5e676e2ee91f43bd79e674f8fc32e5348` (especially `libspecr/src/nondet.rs` or `libspecr/src/set/*`), or
- Upgrading the Lean 4 toolchain beyond `v4.34.1`.
