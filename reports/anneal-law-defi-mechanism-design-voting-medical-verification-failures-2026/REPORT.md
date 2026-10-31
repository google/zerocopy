<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Historical Verification and Specification Failures in Law, DeFi, Mechanism Design, Voting, and Medical/Aviation Systems: Architectural Lessons for Anneal

## Summary

Formal verification, statutory compilation, economic mechanism design, and
safety-critical certification fail in production far more often from
**specification boundary gaps, vacuous assumptions, compiler/lowering mismatch,
and optimistic external-call framing** than from soundness bugs inside a core
proof kernel. Across four high-consequence domains—decentralized finance (DeFi)
and smart-contract verification, statutory tax and social-benefit engines,
electronic voting and financial/auction market clearing, and clinical medical
devices and airborne collision-avoidance rulebooks—historical postmortems
converge on four structural failure classes that map directly onto Anneal's four
trusted primitives (`Language` / `Partial`, `BehaviorCodec` / `Compiles` /
`Abstracts`, `StepResult.externalCall` / `EventualBehaviorOf` / `ProductiveOn` /
`InhabitedPre`, and positive per-obligation `VerificationResult` /
`TrustPolicy`):

1. **Whole-unit invariant bypass, compiler lock-slot miscompilation, and
   optimistic callback framing in DeFi:**
   - In the **Euler Finance exploit (\$197M, March 13, 2023)**, governance
     upgrade EIP-14 added `EToken.donateToReserves` without the mandatory
     `checkLiquidity` health-factor check enforced by other balance-mutating
     functions, allowing an attacker to intentionally self-inflict unbacked bad
     debt and profit via discounted self-liquidation.
   - In the **Curve Finance / Vyper compiler re-entrancy exploit (\$70M, July
     30, 2023)**, source contracts annotated multiple entrypoints with
     `@nonreentrant('lock')`, but a storage-slot allocation bug in Vyper
     `0.2.15`–`0.3.0` (`data_positions.py`) assigned distinct storage slots to
     each function, turning source-level mutual exclusion into target-bytecode
     cross-function re-entrancy.
   - Across **Wormhole (\$324M, Feb 2022)**, **Beanstalk (\$182M, Apr 2022)**,
     **Nomad (\$190M, Aug 2022)**, **Mango Markets (\$110M, Oct 2022)**,
     **Lendf.Me / ERC-777 (\$25M, Apr 2020)**, **Balancer / Curve read-only
     re-entrancy**, and **ERC-4626 empty-vault share inflation**, exploits
     succeeded at cross-contract boundaries where models assumed external token
     transfers were side-effect-free (`HAVOC_ECF`), omitted representation
     validity on spoofed capability handles (`Sysvar: Instructions`), or failed
     to enforce rounding-direction conservation.
   - In industrial smart-contract provers (**Certora Prover**, **KEVM**, and the
     **Aptos/Sui Move Prover and Bytecode Verifier**), rules routinely passed
     vacuously when `require` preconditions over-constrained reachable states
     (necessitating `--rule_sanity`), when default `HAVOC_ECF` summaries hid
     re-entrant callbacks into the caller or sibling view functions, or when
     unverified lowering and reference-borrow checks diverged from VM semantics.
2. **Default-exception priority inversions, temporal aggregation mismatches, and
   non-atomic ledger synchronization in statutory and accounting systems:**
   - Reverse-engineering the **French DGFiP `M`-language income tax code**
     (`Mlang`, CC 2021) and formalizing **French family benefits and US tax
     statutes in `Catala`** (ICFP 2021) exposed statutory contradictions,
     missing default branches, and floating-point/truncation workarounds in
     official state tax and benefit engines.
   - Australia's **Robodebt automated debt-recovery scheme (2015–2019, Royal
     Commission Final Report July 7, 2023)** and **Social Security Act 1991 s
     1073B income apportionment** unlawfully substituted coarse annual
     tax-office income averages (`ATO / 26`) for statutory fortnightly
     entitlement predicates—an unsound downward refinement of a non-linear
     statutory operator.
   - The **UK Post Office Fujitsu Horizon scandal (1999–2015, *Bates & Others v
     Post Office Ltd* [2019] EWHC 3408 (QB))** demonstrated how UI freeze
     retries (**Dalmellington bug**), duplicate database inserts (**Callendar
     Square bug**), and local-cache/central-ledger desynchronization (**Receipts
     and Payments Mismatch bug**) violated double-entry conservation while legal
     presumptions treated the unverified ledger as infallible.
   - **US SNAP and Medicaid (MAGI vs. non-MAGI) eligibility engines** suffered
     from contradictory cross-statutory exception predicates (bureaucratic
     Catch-22s leaving statutory cohorts uninhabited) and discontinuous marginal
     effective tax rate (METR $> 100\%$) benefit cliffs.
3. **Cryptographic proof-check omissions, fractional vote-transfer
   non-termination, dead-code deployment drift, and Sybil equilibrium collapse
   in voting and markets:**
   - In the **SwissPost / Scytl e-voting system (2019, Haines, Lewis, Pereira,
     and Teague, IEEE S&P 2020)**, the Universal Verifiability specification and
     verifier omitted the constructibility/zero-knowledge proof that Bayer-Groth
     shuffle commitment parameters were generated without a known trapdoor,
     allowing a malicious mixnet or electoral authority to forge passing audit
     proofs for altered tallies.
   - Formal verification of **Australian Senate Single Transferable Vote (STV)**
     tabulation by Pattinson, Tiwari, and Goré uncovered discrepancies between
     natural-language electoral statutes and production counting software
     (`AEC EasyCount`) around fractional transfer value truncation, quota
     exhaustion, and multi-way tie-breaking.
   - **Knight Capital's \$440M loss (August 1, 2012, SEC Release No. 34-70694)**
     stemmed from an incomplete binary deployment to 1 of 8 `SMARS` servers that
     re-activated dead `Power Peg` code when a retired order-flag bit was reused
     without an cumulative fill-quantity state invariant.
   - In **multi-item Vickrey-Clarke-Groves (VCG) and second-price spectrum
     auctions (New Zealand 1990 TV/radio spectrum auction; Ausubel & Milgrom
     2006)**, truthful bidding collapsed under complementary goods, thin
     competition (a NZ\$100,000 valuation winning for NZ\$6), and Sybil/shill
     bidding because single-agent deviation models ignored coalitional/Sybil
     splitting.
4. **Interactive number-entry state-machine anomalies, concurrent interlock
   races, and hybrid advisory reversals in medical devices and aviation:**
   - PVS verification of the **Becton Dickinson / CareFusion Alaris GP infusion
     pump** by Masci, Thimbleby, Curzon, and Oladimeji uncovered keystroke
     handling, chevron saturation/wrapping, and decimal rounding anomalies where
     minor clinician key-slips produced silent 10x–100x dosing changes.
   - The **Therac-25 radiation therapy overdoses (1985–1987, Leveson & Turner
     1993)** resulted from an 8-bit shared-counter wraparound (`Class3`
     incrementing to `0` every 256 ticks) and a 8-second terminal cursor-edit
     race (`Data Entry Complete` hiding subsequent turntable mode edits from the
     beam-spreader interlock).
   - The **2002 Überlingen mid-air collision (BFU Report AX001-1-2/02)** and
     formal verification of **TCAS II / ACAS X** in `KeYmaera` by Jeannin,
     Platzer, et al. (TACAS 2015 / EMSOFT 2015 / STTT 2017) exposed unsafe
     advisory regions where delayed reversal logic (`TCAS II v7.0` vs.
     `Change 7.1`) and discrete lookup-table interpolation under pilot response
     delay violated continuous kinematic safe-separation envelopes.

## Applicability

The findings in this report apply to the ten subject groups recorded in
`REPORT.json`:

1. **Anneal's core verification framework** at
   `joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`
   (`trusted/lean/Trusted/Refinement.lean`,
   `trusted/lean/Trusted/StepResult.lean`, and
   `trusted/lean/Trusted/MirSemantics.lean`) and the **Anneal reference corpus
   verification-hardening packages** at
   `joshlf/anneal@df55c524a051d59e7dd35564f282b30d29133392`
   (`anneal-behavior-codec-and-progress-refinement-2026`,
   `anneal-polar-ctfe-admission-and-semantic-polarity-2026`,
   `anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026`,
   `anneal-rustc-obligation-inventory-and-single-source-codegen-2026`, and
   `anneal-structural-external-calls-and-tcb-mutation-testing-2026`).
2. **Historical production failures, vulnerability disclosures, judicial
   findings, and formal-methods postmortems** across smart contracts and DeFi
   (2020–2023), statutory tax/welfare and accounting systems (1999–2023),
   electronic voting, auctions, and equity order routing (1990–2020), and
   medical devices and airborne collision avoidance (1985–2017).

The relationship among subjects is **comparative and architectural**: historical
failures in external domains are analyzed from primary postmortems, judicial and
regulatory records, and peer-reviewed formal verification literature, and each
failure mechanism is mapped to the exact structural invariant in Anneal's four
trusted primitives that prevents the analogous defect class when Anneal is
instantiated for Rust verification or domain-specific compilation/certification.

## Findings

### 1. Real-World Exploits of Formally Verified and Audited Smart Contracts and DeFi Protocols

#### 1.1 Euler Finance (\$197M Exploit, March 13, 2023): Unverified EIP-14 Function-Boundary Omission of `checkLiquidity`

`Basis: documentation + source + derived`

On March 13, 2023 (Ethereum Mainnet block `16817996`), an attacker drained
approximately \$197 million in DAI, WBTC, stETH, and USDC from the Euler Finance
lending protocol across six transactions.

- **Technical mechanism:** In Euler's architecture, users deposit underlying
  ERC-20 assets to mint collateral shares (`EToken`, representing a claim on the
  pool's reserve) and can mint leveraged debt tokens (`DToken`) up to a
  collateral-adjusted health factor. Every balance-reducing or debt-increasing
  operation in `EToken.sol` (`withdraw`, `transfer`, `transferFrom`, `mint`)
  invoked `checkLiquidity(account)` before completion to verify that the
  account's risk-adjusted collateral value remained at least its liability
  value:
  $$\sum_{i} \text{collateral}_i \cdot c_i \ge \sum_{i} \frac{\text{debt}_i}{b_i}$$
  In July 2022, governance proposal **EIP-14** added a helper function
  `EToken.donateToReserves(uint subAccountId, uint amount)` intended to let
  users burn `eTokens` into protocol reserves to clear account dust. Although
  EIP-14 underwent standalone smart-contract audit review, `donateToReserves`
  decremented the caller's `eToken` collateral balance **without calling
  `checkLiquidity(msg.sender)`**.
- **Exploit execution:** Using a flash loan of 30M DAI from Aave, the attacker
  operated two contracts (`Violator` and `Liquidator`):
  1. `Violator` deposited 20M DAI, called `EToken.mint` at 10x leverage to
     create 195.6M `eDAI` and 200M `dDAI`, repaid 10M DAI of debt using the
     remaining flash-loaned funds, and minted another 195.6M `eDAI` and 200M
     `dDAI` (reaching 410M `eDAI` collateral against 390M `dDAI` debt).
  2. `Violator` called `donateToReserves(0, 100_000_000e18)`, burning 100M
     `eDAI` directly into reserves while leaving 390M `dDAI` debt intact.
     Because `checkLiquidity` was absent, the transaction succeeded, placing
     `Violator` at 310M `eDAI` vs. 390M `dDAI` (80M DAI of unbacked bad debt).
  3. In Euler's dynamic liquidation pricing formula, the liquidation discount
     scaled linearly with how far underwater the borrower was, without capping
     the discount at the point where collateral value fell below debt value.
     `Liquidator` called `liquidate` on `Violator`, absorbing the debt at a
     massive collateral bonus that transferred all 310M `eDAI` to `Liquidator`,
     which then withdrew the entire underlying reserve (38.9M DAI) after having
     only 30M DAI at risk.
- **Why per-function verification and differential audits missed it:** Prior
  formal and manual reviews verified existing functions (`withdraw`, `mint`,
  `liquidate`) under the implicit inductive invariant that **every reachable
  post-transaction state satisfies account solvency** (`HealthFactor(u) >= 1`
  unless underwater solely from external price movement). Differential review of
  EIP-14 checked local functional behavior of `donateToReserves` ("burns
  caller's own `eTokens`, cannot steal another user's balance") rather than
  re-verifying that *every* public entrypoint of the `Crate` preserved the
  global protocol representation invariant `AdtInv`.
- **Architectural lesson for Anneal:**
  1. **Mandatory whole-crate obligation completeness (`Trusted.CrateTheorem` and
     `EnsuresRetLibInv`):** In Anneal (`trusted/lean/Trusted/MirSemantics.lean`
     and
     `reports/anneal-rustc-obligation-inventory-and-single-source-codegen-2026`),
     custom representation invariants (`AdtInv` / `LibInv`) are not optional
     per-function properties chosen ad hoc by a developer. Every `pubSafe`
     function in `Crate.fns` carries a mandatory `EnsuresRetLibInv` and
     `WellFormedOn` obligation in `CrateTheorem`. Adding a new public method
     like `donateToReserves` automatically adds its `EnsuresRetLibInv`
     preservation obligation to the crate's obligation inventory; if
     `donateToReserves` breaks the account solvency invariant, `CrateTheorem` is
     unprovable.
  2. **Positive per-obligation waiver tracking (`VerificationResult`):** If a
     new upgrade function is deployed without a proof of `EnsuresRetLibInv`,
     Anneal's `ScopedVerificationResult` forces the obligation ID
     `("donateToReserves", .ensuresRetLibInv)` to appear explicitly in the
     `waived` list audited against `TrustPolicy.isAllowed`, preventing silent
     regression across incremental governance upgrades.

#### 1.2 Curve Finance and Vyper Compiler Re-Entrancy Lock Collision (\$70M Exploit, July 30, 2023)

`Basis: source + execution + documentation`

On July 30, 2023, multiple Curve Finance liquidity pools (`alETH/ETH`,
`msETH/ETH`, `pETH/ETH`, and `CRV/ETH`) compiled with the Vyper smart-contract
compiler (versions `0.2.15`, `0.2.16`, and `0.3.0`) were exploited for
approximately \$70 million due to a compiler bug (`GHSA-5824-cm3x-3c38`) that
broke `@nonreentrant` mutual-exclusion locks.

- **Technical mechanism:** In Vyper source code, pool authors annotated both
  `remove_liquidity` and `add_liquidity` (as well as `exchange`) with the
  identical re-entrancy lock key `@nonreentrant('lock')`. Semantically, at the
  Vyper source level (`L_src`), all functions sharing the string key `'lock'`
  must read and write a single shared storage slot `slot("lock")`: entering
  `remove_liquidity` sets `storage[slot("lock")] := 1`, causing any re-entrant
  call to `add_liquidity` during an external ETH transfer callback to revert.
  However, in `vyper/semantics/analysis/data_positions.py` (introduced in commit
  `053f06f` for Vyper `0.2.15`), `set_reentrancy_key_position` computed storage
  offsets per function definition rather than per unique key name, incrementing
  the storage-slot counter each time it encountered `@nonreentrant('lock')` on a
  new function. Consequently, in the compiled EVM bytecode (`L_tgt`),
  `remove_liquidity` checked and set storage slot $k$, while `add_liquidity`
  checked and set storage slot $k + 1$.
- **Exploit execution:** During `remove_liquidity`, the Curve pool updated total
  LP token supply (`burnFrom`), transferred native ETH to the caller via a raw
  EVM `CALL` (triggering the attacker contract's `receive()` fallback *before*
  updating the pool's internal token balances `self.balances[i]`), and only
  updated `self.balances` after the `CALL` returned. Inside `receive()`, the
  attacker called `add_liquidity`: because `add_liquidity` checked slot $k + 1$
  (which was `0`), it bypassed the re-entrancy guard and minted new LP tokens
  against a corrupted intermediate state where LP `totalSupply` had already been
  decremented but `self.balances` still held the pre-withdrawal asset amounts.
- **Why source-level auditing and per-function testing missed it:** Source-level
  audits inspected the Vyper source code, where `@nonreentrant('lock')` was
  present on every state-mutating function. Unit tests tested single-function
  re-entrancy (`remove_liquidity` re-entering `remove_liquidity`, which shared
  slot $k$ and correctly reverted) rather than cross-function re-entrancy
  (`remove_liquidity` $\to$ `receive()` $\to$ `add_liquidity`) on the compiled
  bytecode.
- **Architectural lesson for Anneal:**
  1. **Verifying both source and compiled target (`Compiler.Verified`):** Vyper
     `0.2.15`–`0.3.0` is the canonical real-world demonstration of why
     source-only verification (`L_src.sem s ≤ spec`) is insufficient when the
     compiler is unverified. In Anneal's `Trusted/Refinement.lean` (`L420-425`),
     `Compiler.Verified C s spec` requires the three-way conjunction:
     $$L_{\text{src}}.\text{sem}\ s \le \text{spec} \;\land\; \text{Compiles}\ L_{\text{src}}\ L_{\text{tgt}}\ C.\pi\ s\ (C.\text{compile}\ s) \;\land\; L_{\text{tgt}}.\text{sem}\ (C.\text{compile}\ s) \le C.\pi\ \text{spec}$$
     Under `Compiles`, mapping `'lock'` in `remove_liquidity` to slot $k$ and in
     `add_liquidity` to slot $k+1$ breaks the `BehaviorCodec` storage-layout
     simulation (`Stage0Compiler.Compiles`) because the target bytecode allows a
     re-entrant trace that is impossible (`defined = True` with `.reverted` or
     unreachable) in the source semantics.
  2. **Structural call-site invariant checking (`StepResult.externalCall`):** In
     Anneal
     (`reports/anneal-structural-external-calls-and-tcb-mutation-testing-2026`),
     the raw ETH transfer `CALL` inside `remove_liquidity` is modeled by
     `StepResult.externalCall boundaryInv next`. Because `remove_liquidity`
     burned LP shares before updating `self.balances[i]`, the pool's
     representation invariant (`AdtInv`: `balances` coherent with `totalSupply`
     OR global re-entrancy lock bit held across *all* entrypoints viewing or
     mutating `balances`) is `false` at the call site if any entrypoint can
     observe the unlocked state.

#### 1.3 Cross-Contract Callback Re-Entrancy, Bridge Initialization, Flash-Loan Governance, and Rounding-Inflation Exploits (Wormhole, Nomad, Mango Markets, Beanstalk, Lendf.Me, Balancer, ERC-4626)

`Basis: source + execution + documentation + derived`

Between 2020 and 2023, over \$1.2 billion was lost across audited and partially
verified protocols due to five recurring boundary failure patterns:

1. **ERC-777 and Read-Only Cross-Contract Callback Re-Entrancy (Lendf.Me \$25M,
   April 19, 2020; Cream Finance \$18.8M, August 30, 2021; Balancer / Curve
   read-only re-entrancy, 2022–2023):**
   - *Mechanism:* Lendf.Me (a fork of Compound v1) implemented
     `supply(asset, amount)` without a re-entrancy lock, assuming
     `IERC20(asset).transferFrom` merely updated token balances. When supporting
     `imBTC` (an ERC-777 token that invokes `tokensToSend` on the sender before
     transferring), an attacker called `supply` a second time inside the
     `tokensToSend` callback before the outer `supply` updated `userBalances`,
     overwriting the first balance read and doubling credited collateral. Even
     when protocols added re-entrancy locks to *mutating* functions, **read-only
     re-entrancy** exploited `view` functions (`get_virtual_price()` in Curve or
     `getRate()` in Balancer) that lacked `@nonreentrant` guards: during a
     native ETH transfer in `remove_liquidity`, an attacker's `receive()`
     callback entered a *separate* lending protocol that queried Curve's
     `get_virtual_price()` while the Curve pool was mid-withdrawal
     (`totalSupply` reduced, `balances` not yet reduced), reading an
     artificially inflated LP token price and borrowing against it.
   - *Anneal primitive mapping:* Anneal's
     `StepResult.externalCall boundaryInv next` requires `boundaryInv = true`
     *at the moment control leaves the module*. If external code can query any
     public accessor (including read-only getters), `boundaryInv` must hold for
     the module's observable state before the external call executes
     (checks-effects-interactions), or every accessor must check the module lock
     so mid-transition states are unobservable.
2. **Capability-Handle Spoofing at FFI / Syscall Boundaries (Wormhole \$324M,
   February 2, 2022):**
   - *Mechanism:* On Solana, Wormhole's `verify_signatures` instruction checked
     Guardian secp256k1 signatures by calling the deprecated helper
     `solana_program::sysvar::instructions::load_instruction_at` on an
     `instruction_acc` `AccountInfo` passed by the caller. `load_instruction_at`
     did not verify that `instruction_acc.key == sysvar::instructions::id()`.
     The attacker passed a spoofed account whose raw byte buffer mimicked a
     previously executed `Secp256k1` precompile instruction, forging a
     `GuardianSet` attestation and minting 120,000 `wETH` (\$324M).
   - *Anneal primitive mapping:* In Anneal's `BehaviorCodec` and library
     boundary contract (`MirVal.satisfiesInv` / `AdtInv`), deserializing an
     external raw pointer or `AccountInfo` into a trusted system-capability type
     without verifying the address/tag predicate violates `decodeQuery` /
     `AdtInv` admission: `decodeOut = none` (and `WellFormedOn safetyPre`)
     rejects any pipeline that treats an unvalidated untrusted byte slice as a
     verified `Sysvar` capability.
3. **Default-Zero Map Lookup / Initialization Polarity Inversion (Nomad Bridge
   \$190M, August 1, 2022):**
   - *Mechanism:* In Nomad's `Replica.sol` upgrade (commit `945667b`),
     `initialize` called `_setRoot(0x00)`, setting `confirmAt[bytes32(0)] = 1`.
     For any unproven message `m`, `messages[keccak256(m)]` defaulted to
     `bytes32(0)` in EVM zero-initialized storage. When `process(m)` checked
     `acceptableRoot(messages[_messageHash])`, looking up `confirmAt[0x00]`
     returned `1 <= block.timestamp` (`true`), accepting arbitrary forged
     withdrawal messages without a Merkle proof.
   - *Anneal primitive mapping:* This is the exact runtime dual of Anneal's
     negative-polarity fail-open trap
     (`reports/anneal-polar-ctfe-admission-and-semantic-polarity-2026`): mapping
     an uninitialized/unproven state (`0x00` or `.stuck`) to a passing boolean
     guard (`confirmAt[0x00] = 1`). In Anneal's `Partial` and `StepResult`,
     uninitialized or unstepped states map to `.stuck` / `defined = False`,
     never to a valid proof witness.
4. **Flash-Loan Instantaneous Quorum Capture (Beanstalk \$182M, April 17, 2022)
   and Thin-Book Self-Trade Oracle Manipulation (Mango Markets \$110M, October
   11, 2022):**
   - *Mechanism:* Beanstalk's `emergencyCommit(uint32 bip)` allowed a 2/3
     supermajority of staked Stalk/Silo deposits to execute an arbitrary
     `delegatecall` governance payload in the same block (`0` timelock delay
     after a 1-day BIP registration). The attacker flash-loaned \$1B in
     stablecoins, deposited them into the Silo to acquire 79% voting power for a
     single transaction, called `emergencyCommit` on a malicious BIP to drain
     \$182M, and repaid the flash loan in the same block. In Mango Markets, the
     attacker took opposing long and short `MNGO-PERP` positions across two
     accounts and bought spot `MNGO` on thin order books to pump the oracle mark
     price by 1,300% within minutes, borrowing \$110M against unrealized
     self-traded PnL exceeding the pool's total market depth.
   - *Anneal primitive mapping:* Both failures stem from verifying a 1-step
     transitional check (`votes >= 2/3` at a single instant, or
     `collateral * spotPrice >= debt`) without enforcing a multi-step trace
     invariant across `StepResult.externalCall` boundaries (`boundaryInv`
     requiring time-weighted average balances across strictly positive block
     intervals $\Delta t > 0$ and bounding collateral valuation by realizable
     liquidation depth).
5. **ERC-4626 Empty-Vault Rounding Inflation Attack:**
   - *Mechanism:* Standard ERC-4626 tokenized vaults compute shares minted on
     `deposit(assets)` as $\lfloor \text{assets} \cdot S / A \rfloor$, where $S$
     is `totalSupply` and $A$ is `totalAssets`. When a vault is empty
     ($S = 0, A = 0$), an attacker deposits `1 wei` ($S = 1, A = 1$), then
     directly transfers $10^{18}\text{ wei}$ of the underlying token to the
     vault address via `ERC20.transfer` ($S = 1, A = 10^{18} + 1$). When a
     legitimate victim subsequently deposits $1.9 \times 10^{18}\text{ wei}$,
     the vault computes
     $\lfloor 1.9 \times 10^{18} \cdot 1 / (10^{18} + 1) \rfloor = 1\text{ share}$
     ($S = 2, A = 2.9 \times 10^{18} + 1$). The attacker then redeems their 1
     share for
     $\lfloor 1 \cdot (2.9 \times 10^{18}) / 2 \rfloor = 1.45 \times 10^{18}\text{ wei}$,
     stealing $0.45 \times 10^{18}\text{ wei}$ of the victim's deposit via
     integer division truncation.
   - *Anneal primitive mapping:* Under
     `Compiles RealVaultSpec EvmVaultBytecode codec`, `BehaviorCodec` bounds the
     quantization error between ideal rational share accounting and `U256`
     floor/ceil division; if an attacker can perturb `totalAssets` via an
     out-of-band `StepResult.externalCall` (direct token donation) so that
     rounding error exceeds 1 basis point of a depositor's principal, `Compiles`
     fails unless virtual shares/assets offset (`dead shares`) are present.

#### 1.4 Certora CVL Vacuity Traps, `HAVOC_ECF` Optimism, KEVM Abstractions, and Move Prover / Bytecode Verifier Soundness Bugs

`Basis: documentation + source + derived`

Even when formal verification tools (Certora Prover, Runtime Verification KEVM,
and the Move Prover / Move Bytecode Verifier) are applied directly to smart
contracts, historical vulnerability disclosures show four tool-level failure
modes:

1. **CVL `require` Over-Constraint and Rule Vacuity (`--rule_sanity`):**
   - *Mechanism:* In Certora Verification Language (CVL), specifications mix
     `require P;` (which filters out execution traces where $\neg P$, placing
     $P$ on the left of $\to$) with `assert Q;`. In complex multi-contract
     specs, engineers frequently write helper functions containing `require`
     statements (e.g., constraining storage invariants, non-zero denominators,
     or timestamp bounds). Whenever two `require` clauses subtly contradict each
     other—or when every non-reverting path through a contract method violates a
     later `require`—the verification condition
     $\text{PathCondition} \land P_1 \land P_2 \implies Q$ holds **vacuously**
     (`False → Q`), and the Certora Prover reports a green checkmark
     (`VERIFIED`) without checking `Q` on a single execution path. Certora had
     to introduce `--rule_sanity basic/advanced` (checking satisfiability of
     $\text{PathCondition} \land \bigwedge_i P_i$) because vacuous specs
     repeatedly passed in production audits.
   - *Anneal primitive mapping:* Anneal eliminates this failure mode
     structurally in two ways:
     1. In `Trusted/Refinement.lean` (`L148-180`), `VerificationResultOn` always
        proves baseline `L_src.WellFormedOn pre` alongside `specs`, and
        `InhabitedPre pre` + `ProductiveOn pre prog` (`∃ q, pre q` and
        `∀ q, pre q → ∃ h, ∃ out, (sem prog q).val h out`) require a
        constructive witness that the precondition is inhabited and that the
        program produces at least one non-empty outcome on every admitted query.
     2. In `ScopedVerificationResult`
        (`reports/anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026`),
        concrete assumptions and waivers are placed **positively** on the right
        (`ob.id ∈ waived ∨ ob.prop`), never on the left of `→` where a
        contradiction could discharge `assert Q` via `False.elim`.
2. **Certora `HAVOC_ECF` vs. `HAVOC_ALL` External Call Optimism:**
   - *Mechanism:* When a verified contract makes an unresolved external call,
     Certora's default summary mode is `HAVOC_ECF` ("Havoc External Contract
     Fields"), which allows the external call to mutate other contracts' storage
     but **assumes the external call cannot re-enter and mutate the current
     contract's storage**. If a contract has a cross-function re-entrancy bug
     (such as the Lendf.Me ERC-777 or Vyper `@nonreentrant` bug), a CVL rule run
     under default `HAVOC_ECF` silently assumes re-entrancy is impossible and
     reports `VERIFIED`! Conversely, switching to `HAVOC_ALL` wipes the current
     contract's storage completely to arbitrary unvalidated values, breaking all
     representation invariants unless the user manually writes
     `requireInvariant` assumptions (which can re-introduce vacuity or unsoundly
     assume the broken invariant holds during re-entrancy).
   - *Anneal primitive mapping:* Anneal's
     `StepResult.externalCall boundaryInv next` paired with
     `CallerFramePreserved` and `AdtInv` solves the exact `HAVOC_ECF` vs.
     `HAVOC_ALL` dilemma: it neither assumes re-entrancy cannot happen
     (`HAVOC_ECF`) nor wipes private stack frames (`HAVOC_ALL`). Instead, it
     enforces that `boundaryInv` (`AdtInv` on all exposed state) holds *before*
     the external call, preserves unexposed caller-frame locals
     (`CallerFrameIsolated`), and demonically quantifies over all post-call
     states satisfying `AdtInv`, soundly covering arbitrary-depth re-entrant
     callbacks by fuel induction (`open_world_callback_composition_sound`).
3. **Move Prover / Move Bytecode Verifier Soundness and Reference-Borrow Bugs in
   Aptos and Sui (2022–2024):**
   - *Mechanism:* Move separates static verification into the on-chain **Move
     Bytecode Verifier** (which enforces type safety, resource linearity, and
     reference borrow checking in Rust before module publication) and the
     off-chain **Move Prover** (which translates Move bytecode to Boogie/Z3).
     Multiple critical soundness bugs were discovered in both layers:
     - In the Move Prover, integer bit-shift operations (`<<`, `>>`) and vector
       borrow-mutation summaries in the Boogie prelude historically modeled
       shifts without matching the Move VM's abort-on-shift-width-$\ge$-bitwidth
       check, allowing the Move Prover to verify functions as `aborts_if false`
       that aborted at runtime.
     - In the Move Bytecode Verifier on Aptos and Sui, reference-safety and
       type-instantiation verifier bugs (such as the 2022–2023 Zellic / OtterSec
       bytecode verifier disclosures in `reference_safety` and stack-usage
       verifiers, including integer overflow in `meter` / borrow-graph join
       states) allowed crafted Move bytecode to pass verification while aliasing
       mutable references (`&mut T`) and corrupting linear `Coin` resources.
   - *Anneal primitive mapping:* In the Move ecosystem, the Bytecode Verifier is
     a large procedural Rust pass (~15,000+ lines of
     graph/abstract-interpretation code) inside the TCB, and the Move Prover
     trusts both the Boogie translation and the Z3 SMT solver
     (`trustLevel > 0`). In Anneal, the borrow/type checker and SMT tactics live
     *outside* the kernel TCB in `theory/` or untrusted proof generation
     (`proof_gen.rs`), and the Lean 4 kernel checks a foundational proof of
     `Trusted.CrateTheorem` directly over small-step operational semantics gated
     by a 100%-mutation-killing `BoundaryCanarySuite`.

### 2. Statutory Tax, Social-Benefit Eligibility, and Accounting Ledger Failures

#### 2.1 French DGFiP `M`-Language Income Tax and Family-Benefit Bugs Uncovered by `Mlang` and `Catala` (2020–2021)

`Basis: source + execution + documentation`

Since 1990, the French *Direction Générale des Finances Publiques* (DGFiP) has
computed national personal income tax (*impôt sur le revenu*) for over 38
million households using a custom, non-Turing-complete domain-specific language
called **`M`** (~90,000 lines of declarative variable rules and verification
constraints compiled to C). In parallel, French social and family benefits
(*Allocations Familiales*, *Aide Personnalisée au Logement*) and US federal tax
deductions (such as Earned Income Tax Credit under 26 U.S.C. § 32 and Section
121 capital-gains exclusions) are drafted in legislative prose structured as
**default logic with hierarchical exceptions** (a base rule in subsection (a),
overridden by exceptions in (b) and (c), which are themselves overridden by
special cases in (d)).

When Merigoux, Monat, Chataing, and Protzenko reverse-engineered the DGFiP `M`
compiler into **`Mlang`** (CC 2021) and formalized French family-benefit and US
tax statutes in **`Catala`** (ICFP 2021, verified in $\text{F}^\star$), they
uncovered three systemic failure modes in production government code:

1. **Out-of-order exception flattening and priority inversions:** Because `M`
   and legacy COBOL/C agency engines lack first-class prioritized default terms,
   programmers manually flatten nested statutory exceptions into deeply nested
   `if-then-else` trees or sequential variable re-assignments. When Parliament
   enacts an amendment adding a new exception or modifying an income threshold,
   programmers patch an intermediate variable (`calcul_impot`) in a different
   file from the base rule. In the official French family-benefit (*Allocation
   de Soutien Familial* / *Allocations Familiales*) implementation analyzed by
   the `Catala` team, manual flattening inverted the statutory precedence
   between resource-ceiling phase-outs (*complément dégressif*) and child-age
   adjustments, causing edge-case households near the income ceiling to receive
   legally incorrect benefit amounts.
2. **Undefined variable evaluation and IEEE-754 / integer truncation workarounds
   in `M`:** In the DGFiP `M` codebase, uninitialized variables and division by
   zero were suppressed by ad-hoc runtime coercions (`undef` silently coerced to
   `0.0` in arithmetic contexts, and IEEE-754 `double` rounding discrepancies
   fixed via `floor(x + 0.000001)`). `Mlang` revealed that different C compilers
   and optimization levels could alter tax outcomes on boundary cent values if
   floating-point intermediate values were not pinned to an exact deterministic
   semantics.
3. **Missing default branches ("statutory holes"):** Formalizing Section 121 of
   the US Internal Revenue Code and French social security articles in
   `Catala`'s default calculus
   ($\text{default}\ \langle e_1, \dots, e_n \mid e_{\text{just}} \mapsto e_{\text{cons}} \rangle$)
   exposed inputs where *two* exceptions fired simultaneously without a
   statutory priority order (`ConflictError`), or where *no* rule fired because
   mutual exclusions left a gap (`EmptyError`).
- **Architectural lesson for Anneal:**
  1. **Distinguishing conflict (`Partial.ub`) from missing-default stuckness
     (`.stuck`) and enforcing `ProductiveOn`:** In `Catala`, a statutory
     conflict (`ConflictError`) or missing default (`EmptyError`) is a runtime
     exception unless statically discharged. Mapping legislative default logic
     into Anneal's `StepResult` (`trusted/lean/Trusted/StepResult.lean`) maps an
     unresolved equal-priority statutory conflict to `StepResult.failed .ub`
     (`defined = False`) and an unhandled statutory gap (`EmptyError`) to
     `ReachesPrefix.noStep` / `.stuck` (`isSafe = False`). Proving
     `ProductiveOn ValidTaxpayerProfile statuteProg` statically guarantees both
     **conflict-freedom** and **totality** across all taxpayer profiles before a
     tax-year engine is deployed.
  2. **Literate source-to-target refinement
     (`Compiles StatuteLang ProductionRustLang`):** Rather than hand-maintaining
     a flat imperative re-encoding of a statute, `Compiles` requires a
     machine-checked refinement proof that the optimized imperative/branch-free
     tax binary produces the exact cent-level `SemObs` outcome of the
     prioritized statutory specification.

#### 2.2 Australian Robodebt Automated Income-Averaging Scandal and Section 1073B Apportionment Mismatch (2015–2023)

`Basis: normative + documentation + derived`

Between July 2015 and November 2019, the Australian Department of Human Services
(Services Australia) operated the **Online Compliance Intervention (OCI)**—known
publicly as **Robodebt**—which automatically raised 470,000+ welfare overpayment
debts totaling AU\$1.76 billion against social-security recipients. In *Amato v
The Commonwealth of Australia* (Federal Court of Australia, VID611/2019, consent
orders November 27, 2019) and the **Royal Commission into the Robodebt Scheme**
(Final Report delivered July 7, 2023), the scheme—along with a separate
decades-long administrative practice under **Section 1073B of the *Social
Security Act 1991 (Cth)***—was ruled unlawful.

- **Technical and statutory root cause:** Under Sections 1067G and 1068 of the
  *Social Security Act 1991 (Cth)*, entitlement to Youth Allowance and Newstart
  Allowance is defined **per fortnightly instalment period**
  $t \in \{1, \dots, 26\}$ as a non-linear, piecewise-affine function with an
  income-free threshold $\theta$ and taper rates $\tau_1, \tau_2$:
  $$\text{Entitlement}(y_t) = \max\!\big(0,\; B_0 - \tau_1 \max(0, y_t - \theta_1) - \tau_2 \max(0, y_t - \theta_2)\big)$$
  where $y_t$ is the recipient's actual ordinary income earned in fortnight $t$.
  Because $\text{Entitlement}(\cdot)$ is **concave** (due to the
  $-\max(0, \cdot)$ phase-out tapers above threshold $\theta_1$), **Jensen's
  Inequality** implies that for any fluctuating income stream
  $(y_1, \dots, y_{26})$ with annual Australian Taxation Office (ATO) sum
  $Y = \sum_{t=1}^{26} y_t$ and mean $\bar{y} = Y / 26$:
  $$\sum_{t=1}^{26} \text{Entitlement}(y_t) \;\neq\; 26 \cdot \text{Entitlement}\!\left(\frac{Y}{26}\right)$$
  Specifically, a casual or seasonal worker who earned \$0 during 13 unemployed
  fortnights (legally entitled to full benefit $13 \cdot B_0$) and earned high
  wages during 13 employed fortnights (receiving \$0 benefit) had a positive
  average $\bar{y} = Y / 26 > \theta_1$. Robodebt's algorithm replaced unknown
  fortnightly $y_t$ values with the constant average $\bar{y} = Y / 26$,
  computing a phantom overpayment debt whenever
  $\text{Entitlement}(\bar{y}) < B_0$ during the recipient's unemployed
  fortnights—unless the recipient could produce years-old fortnightly payslips
  to refute the algorithm. Separately, under Section 1073B, agency software
  apportioned single payslips spanning employment dates across adjacent
  Centrelink assessment fortnights outside the statutory conditions permitted by
  the Act.
- **Architectural lesson for Anneal:**
  1. **Refinement vs. Abstraction polarity (`Compiles` vs. `Abstracts`) under
     lossy query projection (`BehaviorCodec`):** Robodebt is a textbook
     violation of `BehaviorCodec` query round-tripping
     (`decodeQuery_encodeQuery`) and refinement polarity. The statutory language
     `L_statute` requires a 26-vector query
     $q = (y_1, \dots, y_{26}) \in \mathbb{N}^{26}$, whereas the ATO
     data-matching feed provides only the scalar sum
     $Y = \sum_t y_t \in \mathbb{N}$. Because the projection
     $\pi(y_1, \dots, y_{26}) = \sum_t y_t$ is **non-injective** (many-to-one),
     there is no valid `BehaviorCodec` with `decodeQuery (encodeQuery q) = q`.
     Replacing $q$ with $(\bar{y}, \dots, \bar{y})$ computes only a **lower
     bound on entitlement** (an *upper bound* on debt), which goes in the
     **wrong order direction** (`≥` instead of `≤`) to justify a legal debt
     determination! In Anneal, if only coarse aggregate input $Y$ is available,
     the query must demonically quantify over all fortnightly vectors
     $\{(y_1, \dots, y_{26}) \mid \sum_t y_t = Y\}$, which permits raising a
     debt only for the minimum overpayment guaranteed across *every* possible
     distribution of $Y$ across the 26 fortnights.

#### 2.3 UK Post Office Fujitsu Horizon Accounting Ledger Bugs (1999–2019, *Bates & Others v Post Office Ltd* [2019] EWHC 3408 (QB))

`Basis: normative + documentation + source`

Between 1999 and 2015, the UK Post Office prosecuted more than 700
subpostmasters and subpostmistresses for false accounting and theft based on
shortfalls reported by the **Horizon** retail and accounting system (developed
by ICL / Fujitsu). In *Bates & Others v Post Office Ltd (No 6: Horizon Issues)*
`[2019] EWHC 3408 (QB)` (1,164 paragraphs plus a 461-paragraph Technical
Appendix delivered by Mr Justice Fraser on December 16, 2019), the High Court
established that Horizon contained at least 29 distinct software defects that
unilaterally corrupted branch balance sheets:

1. **The Callendar Square (Falkirk) Bug (`PEAK PC0061213`, 2000–2006):**
   - *Mechanism:* In Legacy Horizon, branch terminals wrote accounting
     transactions to a local Riposte message-store database, which replicated to
     central servers. When a Riposte message-table index became corrupted or
     experienced a network timeout during replication, the counter wrote
     duplicate transaction records into the central audit trail without
     displaying the duplicate on the local branch Roll-Over balance screen,
     creating phantom branch shortfalls of thousands of pounds.
2. **The Dalmellington Bug / Branch Outreach Issue (`PEAK PC0208735`,
   2010–2015):**
   - *Mechanism:* In Horizon Online (`HNG-X`), when a subpostmaster transferred
     cash between a main branch and an outreach sub-office ("Remming In"), the
     Java counter UI froze if a network packet was delayed while waiting for the
     backend BRDB (Branch Database) response. Because the UI did not disable the
     `Enter` key or attach an idempotency token (`TransactionUUID`) to the
     user's confirmation action, each press of `Enter` on the frozen screen
     queued and committed an additional duplicate cash receipt in the backend
     database (creating a £24,000 phantom shortfall at the Dalmellington branch
     in Scotland).
3. **The Receipts and Payments Mismatch Bug (`PEAK PC0203589`, August–October
   2010):**
   - *Mechanism:* In `HNG-X`, when a subpostmaster cancelled or rolled back a
     balance trading period transition after moving a discrepancy into a local
     suspense account, the local counter cache cleared the transaction while the
     central Oracle BRDB database retained it. Consequently, the branch's
     Receipts and Payments summary remained balanced locally on the counter
     terminal while the central ledger recorded a hidden shortfall (affecting
     62+ branches), which Fujitsu support staff ("SSC") manually edited in live
     production databases via raw SQL (`BRDB` direct injection) without branch
     visibility or audit signatures.
- **Architectural lesson for Anneal:**
  1. **Idempotency and conservation invariants in `BehaviorCodec` and
     `SemObs`:** In a double-entry accounting language `L_ledger`, `SemObs` is
     equipped with the Abelian group conservation invariant
     $\sum \text{Debits} - \sum \text{Credits} = 0$, and every external user
     action carries a unique idempotency key in `Query`. Under
     `Compiles SpecLedgerLang DistributedBranchLang codec`, a UI retry on a
     frozen screen corresponds to stuttering steps on the *same* logical query
     (`EventualBehaviorOf`); any backend implementation that commits $k > 1$
     ledger postings for a single logical confirmation violates `obs_decodeOut`
     and `Compiles`.
  2. **Divergence between local view and authoritative artifact (`SingleSource`
     binding):** The Receipts and Payments Mismatch bug—where the counter screen
     showed a balanced account while the central database recorded a debt—is the
     accounting analogue of the dual-emitter divergence identified in
     `reports/anneal-rustc-obligation-inventory-and-single-source-codegen-2026`
     (where `.anneal/Mir.lean` and `.anneal/Prog.s` could diverge). Binding the
     displayed branch receipt and the central ledger commit to a single
     cryptographically hashed, kernel-checked transaction record eliminates
     split-brain accounting states.

#### 2.4 US SNAP and Medicaid (MAGI vs. Non-MAGI) Contradictory Eligibility Exceptions and Benefit Cliffs

`Basis: normative + documentation + derived`

In US federal and state public-benefits rules engines—governing the Supplemental
Nutrition Assistance Program (SNAP, 7 U.S.C. § 2014 / 7 C.F.R. § 273.9) and
Medicaid under the Affordable Care Act (42 U.S.C. § 1396a(e)(14), Modified
Adjusted Gross Income `MAGI` vs. legacy SSI-linked `non-MAGI`
aged/blind/disabled categories)—two structural specification bugs repeatedly
arise in state Integrated Eligibility Systems (IES):

1. **Contradictory Cross-Program Preconditions ("Bureaucratic Catch-22s"):**
   Under ACA Medicaid expansion, non-disabled adults are evaluated under IRS
   tax-household `MAGI` counting rules (42 C.F.R. § 435.603), whereas applicants
   turning 65 or qualifying via disability transition to `non-MAGI` SSI asset
   and deeming rules. In multiple state eligibility engines (and during
   2023–2024 post-PHE Medicaid "unwinding" auto-renewal redeterminations), state
   decision tables routed applicants who reported *both* self-employment tax
   deductions and disability indicators into a compound eligibility guard that
   required `isMagiHousehold = false` (due to disability screening) AND
   evaluated an income-disregard sub-table gated on `isMagiHousehold = true`,
   causing both branches to evaluate to `Ineligible` without conducting the
   federally mandated *ex parte* cross-category review (42 C.F.R. §
   435.916(f)(1)).
2. **Unbounded Marginal Effective Tax Rate (METR $> 100\%$) Cliffs:** When
   SNAP's 130% Federal Poverty Level (FPL) gross-income limit, Medicaid's 138%
   FPL cutoff, and Childcare Development Fund (CCDF) copayment steps interact
   without coupled monotonicity verification, a \$100/month wage increase across
   the 130% or 138% FPL boundary can trigger a \$3,000–\$8,000 net loss in
   household disposable resources.
- **Architectural lesson for Anneal:**
  1. **`InhabitedPre` per statutory category and `ProductiveOn` across category
     handoffs:** In Anneal, if a state rules engine partitions applicants into
     eligibility tracks $T_1, \dots, T_k$ with entry guards $\text{pre}_i$,
     requiring `InhabitedPre pre_i` for every statutory cohort prevents
     self-contradictory guard conjunctions (`isMagi ∧ ¬isMagi`), and requiring
     `ProductiveOn StatutorilyEligibleApplicant iesEngine` forces the *ex parte*
     fallback transition to fire rather than dropping the applicant into an
     unhandled rejection state.

### 3. Electronic Voting, Combinatorial Auction, and Financial Exchange Failures

#### 3.1 SwissPost / Scytl E-Voting Cryptographic Shuffle and Trapdoor Commitment Flaw (2019–2020, Haines, Lewis, Pereira, and Teague)

`Basis: source + normative + documentation`

In February–March 2019, Swiss Post published the source code and formal
specification of its electronic voting system (developed by Scytl and intended
for binding Swiss cantonal elections) for public intrusion testing. Within
weeks, Sarah Jamie Lewis, Olivier Pereira, and Vanessa Teague (later joined by
Thomas Haines in *"How not to prove your election outcome"*, IEEE S&P 2020,
`doi:10.1109/SP40000.2020.00055`) discovered fatal soundness flaws in both the
**Bayer-Groth verifiable mixnet shuffle proof** and the **Schnorr/Chaum-Pedersen
non-interactive zero-knowledge (NIZK) proofs** that allowed complete,
undetectable manipulation of election tallies despite passing the official
Universal Verifier.

- **Technical root cause (missing commitment-key trapdoor check and Fiat-Shamir
  under-hashing):**
  1. **Trapdoor Pedersen Commitment in the Bayer-Groth Shuffle:** To prove in
     zero knowledge that a mix node permuted and re-encrypted a vector of
     ElGamal ciphertexts $(C_1, \dots, C_N)$ without dropping or substituting
     votes, the Bayer-Groth protocol commits to the permutation matrix using a
     multi-pedersen commitment key
     $ck = (g, g_1, \dots, g_n) \in \mathbb{G}^{n+1}$ in a prime-order subgroup
     $\mathbb{G} \subset \mathbb{Z}_p^*$. Soundness of the Bayer-Groth shuffle
     proof holds **if and only if the prover does not know any discrete
     logarithm relation $\log_g(g_i)$ among the generators in $ck$**. If whoever
     generates $ck$ knows $x_i$ such that $g_i = g^{x_i} \pmod p$ (the
     commitment trapdoor), they can open a commitment to *any* forged
     permutation and produce a Bayer-Groth proof that passes verification with
     probability $1$. In Scytl's implementation (`CommitmentParamsGenerator`),
     the commitment generators $g_i$ were generated inside a trusted setup
     component **without emitting a verifiable seed derivation or NIZK proof of
     knowledge/indistinguishability**, and the Universal Verifier specification
     simply assumed $ck$ was trapdoor-free without checking how $g_i$ were
     constructed!
  2. **Insecure Fiat-Shamir Hash Serialization (`ExponentiationProof`):** In
     several Schnorr/Chaum-Pedersen NIZK proofs used for vote decryption and
     electoral-board key generation, Scytl concatenated variable-length strings
     into the Fiat-Shamir SHA-256 hash transcript without length prefixes or
     omitted the public statement generators from the hash challenge
     $e = H(\text{statement}, \text{commitment})$, allowing an attacker to shift
     field boundaries or choose statement bases *after* computing the challenge.
- **Architectural lesson for Anneal:**
  1. **Never treat a synthesized witness parameter as an unchecked TCB
     hypothesis (`TCBModel` and `TrustedBoundary.lean`):** The SwissPost/Scytl
     bug occurred because the Universal Verifier checked
     `VerifyShuffle(ck, C, C', π) = true` under the unverified implicit
     assumption `TrapdoorFree(ck)`. In Anneal
     (`reports/anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026`),
     any soundness premise that is not constructively discharged inside the
     verifier must either be verified from a transparent seed derivation (e.g.,
     hash-to-group nothing-up-my-sleeve construction checked by the auditor) or
     explicitly surface as a `TrustedAssumption` in `VerificationResultOn`. If a
     cryptographic parameter generator is unverified, placing `TrapdoorFree(ck)`
     silently outside the verifier allows a forged proof to pass at
     `trustLevel = 0`.
  2. **Injective transcript encoding (`BehaviorCodec`):** The Fiat-Shamir
     hash-concatenation flaw (`H(a || b) == H(a' || b')` for
     $(a, b) \neq (a', b')$) is a direct failure of `decodeQuery_encodeQuery`:
     any serialization into a verification challenge transcript must be a
     round-tripping injection so distinct public statements cannot collide on
     the same fiat-shamir challenge.

#### 3.2 Australian Senate Single Transferable Vote (STV) Tabulation Discrepancies (Pattinson, Tiwari, and Goré)

`Basis: source + execution + documentation`

In Australian Senate elections (governed by Section 273 of the *Commonwealth
Electoral Act 1918 (Cth)*), seats are allocated by **Single Transferable Vote
(STV)** using the **Inclusive Gregory Method**: when a candidate's tally $T_c$
exceeds the Droop quota $Q = \lfloor V / (S + 1) \rfloor + 1$, all ballots
currently assigned to $c$ are transferred to their next continuing preference at
a fractional **transfer value**:
$$\text{TV}_c = \frac{T_c - Q}{N_c}$$
where $N_c$ is the total number of ballot papers sitting in $c$'s pile.

When Dirk Pattinson, Mukesh Tiwari, and Rajeev Goré formalized the Australian
Senate STV rules in the **Coq theorem prover** and compared their extracted,
certifying tabulator against the Australian Electoral Commission's (AEC)
production `EasyCount` software and statutory text, they uncovered subtle
specification and arithmetic divergences:

1. **Order of Truncation in Fractional Transfer Values vs. Vote Totals:**
   Section 273(9B) of the *Commonwealth Electoral Act 1918* specifies that the
   transfer value $\text{TV}_c$ is truncated to 8 decimal places, and when a
   parcel of $k$ identical ballots is transferred at value $\text{TV}_c$, the
   votes added to the receiving candidate's tally are
   $\lfloor k \cdot \text{TV}_c \rfloor$ (dropping any fractional remainder).
   However, ambiguity in the statute over whether parcels from multiple prior
   transfers are grouped *before* or *after* multiplying by $\text{TV}_c$ and
   truncating to an integer changes candidate totals by up to $P$ votes (where
   $P$ is the number of distinct sub-parcels), which can flip the elimination
   order of marginal candidates in close sixth-seat Senate races (such as the
   2013 Western Australia Senate recount, which was decided by 14 votes out of
   1.3 million ballots before being voided).
2. **Tie-Breaking Non-Determinism vs. Deterministic Software Implementations:**
   The statute mandates that when two candidates have identical tallies at an
   elimination or surplus-transfer step and prior-round counts are also tied,
    the Australian Electoral Officer must decide the order by lot
    (angelic/external
   nondeterminism). Legacy tabulation implementations frequently broke ties
   implicitly via array index or candidate storage order (`0`-indexed ballot
   position) without pausing for an explicit external tie-break input.
- **Architectural lesson for Anneal:**
  1. **Separating statutory non-determinism (`Partial` outcome sets and
     `StepResult.externalCall`) from implementation choices (`Compiles`):** In
     Anneal, when a statute permits multiple valid outcomes (or requires an
     external Electoral Officer tie-break lot), the specification
     `L_statute.sem s` models the tie-break via `StepResult.externalCall` (or a
     multi-element outcome set `Out → Prop`). Under `Compiles`, a tabulation
     binary cannot silently invent a tie-break outcome without recording the
     external officer decision in `SemObs`, and exact fixed-point parcel
     truncation in `L_src` forces the compiled Rust tabulator to match the
     statutory parcel-grouping order to the single vote.

#### 3.3 Knight Capital \$440M Limit-Order-Book Router Failure (August 1, 2012, SEC Release No. 34-70694): Dead-Code Flag Reuse and Partial Deployment

`Basis: normative + documentation + derived`

On the morning of August 1, 2012, **Knight Capital Americas LLC**—then the
largest retail equity market maker in the United States—activated new software
in its **Smart Market Access Routing System (`SMARS`)** to participate in the
New York Stock Exchange's new Retail Liquidity Program (RLP). Within 45 minutes
of market open (9:30–10:15 AM EDT), `SMARS` routed 4 million unintended child
orders for 397 million shares across 154 NYSE-listed stocks in response to just
212 incoming retail parent orders, accumulating \$3.5 billion in net long
positions and \$3.15 billion in net short positions and inflicting a realized
pre-tax loss of **\$440 million** (SEC Administrative Proceeding File No.
3-15570, Exchange Act Release No. 34-70694, October 16, 2013).

- **Technical root cause (bitflag repurposing + dead-code cumulative-quantity
  omission + 1-of-8 server deployment drift):**
  1. **Dead-Code `Power Peg` Function with Removed Stop-Condition Check:** In
     2003, Knight deactivated an experimental order-execution algorithm called
     **`Power Peg`**, which was designed to move stock prices during test runs
     by repeatedly sending aggressive child orders and tracking cumulative share
     fills until the parent order's target quantity was reached. In 2005, during
     a refactoring of `SMARS`, developers moved the cumulative fill-quantity
     comparison out of the `Power Peg` function **without deleting the
     `Power Peg` function itself or testing whether it still terminated**. As a
     result, if `Power Peg` was ever invoked after 2005, it entered an unbounded
     loop that fired child orders into external exchanges at full line rate
     (`~97,000` orders/minute) without ever checking whether the parent order
     had already been 100% filled.
  2. **Order Bitflag Repurposing and 7-of-8 Server Deployment:** In July 2012,
     to route orders to the new NYSE RLP, Knight engineers repurposed the exact
     boolean bitflag in the internal `SMARS` order message struct that had
     previously gated `Power Peg`: in the new 2012 RLP build, setting that flag
     invoked the new RLP router and excised the call site to `Power Peg`.
     However, during manual deployment on July 27–31, 2012, a technician copied
     the new `SMARS` binary to only **7 of the 8 production `SMARS` servers**.
     When markets opened on August 1, 2012, upstream servers tagged retail
     parent orders with the repurposed RLP flag; the 1st through 7th `SMARS`
     servers routed them normally to the NYSE RLP, while the **8th server**
     (still running the un-updated binary) interpreted the repurposed bitflag as
     a command to execute the broken `Power Peg` loop.
- **Architectural lesson for Anneal:**
  1. **Unbounded loop / non-termination detection via `EventualBehaviorOf` and
     order-quantity conservation in `SemObs`:** In `EventualBehaviorOf`
     (`reports/anneal-behavior-codec-and-progress-refinement-2026`), a compiler
     or order-routing state machine that enters a non-terminating child-order
     emission loop on a finite parent order quantity $Q_{\text{parent}}$
     violates both `EventualBehaviorOf` termination alignment and the `SemObs`
     order-conservation invariant
     ($\sum_{j} q_{\text{child}, j} \le Q_{\text{parent}}$), stepping to
     `Partial.ub` as soon as cumulative child order quantity exceeds
     $Q_{\text{parent}}$.
  2. **Cryptographic single-source binary binding
     (`trusted/root-manifest.sha256` and `.olean`-bound emission):** Knight
     Capital's 8th server failed because the binary running in production was
     not cryptographically bound to the schema version of the wire protocol
     (`BehaviorCodec`). Anneal's single-source artifact binding
     (`reports/anneal-rustc-obligation-inventory-and-single-source-codegen-2026`
     and `trusted/audit`) hashes the exact verified target artifact alongside
     its `BehaviorCodec` interface, rejecting mixed-version deployments where a
     wire tag's `decodeQuery` meaning has changed.

#### 3.4 Multi-Object Vickrey / VCG Auction Revenue Collapse and Sybil/Shill-Bidding Vulnerabilities (New Zealand 1990 Spectrum Auction; Ausubel and Milgrom 2006)

`Basis: documentation + derived`

The **Vickrey-Clarke-Groves (VCG)** mechanism is the crown jewel of normative
economic mechanism design: for any quasi-linear utility profile
$u_i(x, p_i) = v_i(x) - p_i$, allocating the social-welfare-maximizing outcome
$x^* \in \arg\max_x \sum_i b_i(x)$ and charging each winner their marginal
externality on other bidders:
$$p_i = \max_{x} \sum_{j \neq i} b_j(x) \;-\; \sum_{j \neq i} b_j(x^*)$$
is **Dominant-Strategy Incentive Compatible (DSIC)**—truthful bidding
($b_i = v_i$) is a dominant strategy for every isolated individual agent $i$.

Despite this mathematically proven theorem, real-world deployments of VCG and
sealed-bid Vickrey auctions have suffered catastrophic economic failures:

1. **The 1990 New Zealand Radio/Television Spectrum Auction Collapse (McMillan
   1994):** Advised by economic consultants relying on the theoretical
   efficiency of Vickrey's second-price theorem, the New Zealand government
   auctioned UHF television and cellular spectrum licenses using simultaneous
   sealed-bid second-price auctions without reserve prices. Because bidder
   valuations were publicly observable only after the fact and competition in
   regional niches was thin, revenues collapsed to **NZ\$36 million** against a
   projected **NZ\$250 million**: in one notorious case, a bidder submitted a
   truthful valuation bid of **NZ\$100,000** for a nationwide spectrum license
   and paid the second-highest bid of **NZ\$6**; in another lot, a bidder bid
   **NZ\$7 million** and paid **NZ\$5,000**.
2. **The Ausubel-Milgrom "Lovely but Lonely Vickrey Auction" Sybil / False-Name
   and Core-Violation Paradox (Ausubel & Milgrom 2006; Yokoo, Sakurai, and
   Matsubara 2004):** Ausubel and Milgrom proved that whenever goods exhibit
   **complementarities** (superadditive valuations $v(A \cup B) > v(A) + v(B)$),
   the VCG mechanism violates **Core Stability**, **Revenue Monotonicity**, and
   **Sybil / False-Name Proofness**:
   - Consider Goods $A$ and $B$. Bidder 1 is a national carrier who values the
     package $\{A, B\}$ at \$2B (and single items at \$0). Bidders 2 and 3 are
     regional carriers who value $A$ at \$2B and $B$ at \$2B respectively.
   - Under VCG, Bidders 2 and 3 win $A$ and $B$ (total welfare \$4B vs. \$2B).
     What does Bidder 2 pay? Without Bidder 2, the optimal allocation gives $B$
     to Bidder 3 (welfare \$2B). With Bidder 2, Bidder 3 still gets \$2B. Thus
     Bidder 2's VCG payment is $\$2\text{B} - \$2\text{B} = \$0$, and by
     symmetry Bidder 3 also pays **\$0**! Even though Bidder 1 offered \$2B in
     cash for $\{A, B\}$, the VCG mechanism hands $\{A, B\}$ to Bidders 2 and 3
     for **zero revenue** (an outcome outside the Core, since Bidder 1 and the
     seller form a blocking coalition).
   - Worse, **a single bidder can profitably cheat VCG via a Sybil attack**: if
     only Bidder 1 ($v(\{A, B\}) = \$2\text{B}$) is present in the auction,
     Bidder 1 can create two pseudonymous shell accounts ("Bidder 2" bidding
     \$2B on $A$ and "Bidder 3" bidding \$2B on $B$), win both licenses, and
     reduce their own VCG payment to **\$0**!
- **Architectural lesson for Anneal:**
  1. **Multi-agent coalitional and Sybil framing in `StepResult.externalCall`
     and relational `Query` specifications:** Standard DSIC proves safety only
     against *unilateral single-ID deviations*
     $(v_i, v_{-i}) \to (v'_i, v_{-i})$ under the closed-world assumption that
     agent identities $i \in \{1, \dots, n\}$ are fixed and non-colluding. In an
     open-world environment (permissionless smart contracts or shell-company
     spectrum bidding), an adversary's action space in `StepResult.externalCall`
     includes **identity splitting**
     ($1 \text{ physical agent} \mapsto k \text{ Sybil IDs}$). In Anneal,
     verifying a mechanism under open-world identity creation requires lifting
     `Query` to partition-equivalence classes of bids or proving
     **Core-Selecting / False-Name-Proof** postconditions (`L.SpecOn`) where
     total payments satisfy no-blocking-coalition constraints
     ($\sum_{i \in S} p_i \ge v_j(S)$ for every losing bidder $j$).

### 4. Medical Device Firmware and Aviation Collision-Avoidance Rule Failures

#### 4.1 Becton Dickinson / CareFusion Alaris GP Infusion Pump Interactive Number-Entry and Rounding Anomalies Uncovered in PVS (Masci and Thimbleby)

`Basis: source + execution + documentation`

Volumetric bedside infusion pumps deliver high-risk intravenous medications
(insulin, norepinephrine, heparin, potassium chloride, chemotherapy) where a 10x
rate error is rapidly fatal. Between 2005 and 2015, the US FDA received over
56,000 adverse event reports and 710 deaths associated with infusion pumps,
prompting the FDA's **Infusion Pump Improvement Initiative (2010)** and the UL
2800 / IEC 60601-2-24 safety standards.

When Paolo Masci, Harold Thimbleby, Paul Curzon, Patrick Oladimeji, and Rimvydas
Rukšėnas formally modeled the **CareFusion (BD) Alaris GP Volumetric Infusion
Pump** user-interface firmware in the **PVS (Prototype Verification System)**
theorem prover (CAV 2013, FM 2014, SAFECOMP 2015), they discovered that the
pump's interactive number-entry state machine violated basic **Predictability,
Reversibility, and Monotonicity** properties under realistic clinician
keystrokes:

1. **Asymmetric Chevron Step-Size and Clamping / Saturation Traps:** The Alaris
   GP lacks a numeric 0–9 keypad; clinicians adjust the infusion rate
   ($\text{mL/h}$) and Volume to be Infused ($\text{VTBI}$) using four chevron
   keys (`double-up` $\mathord{\uparrow\uparrow}$, `single-up`
   $\mathord{\uparrow}$, `single-down` $\mathord{\downarrow}$, `double-down`
   $\mathord{\downarrow\downarrow}$) whose increment step sizes change
   dynamically by decade ($0.1, 1, 10, 100\text{ mL/h}$) and depend on internal
   floating-point timer scaling. Masci and Thimbleby proved in PVS that:
   - **Irreversibility ($\downarrow(\uparrow(x)) \neq x$):** Starting from valid
     fractional rates (e.g., $x = 99.7\text{ mL/h}$), pressing `double-up` snaps
     and rounds the display to an integer decade boundary ($100\text{ mL/h}$),
     after which pressing `double-down` steps to $90\text{ mL/h}$ rather than
     returning to $99.7\text{ mL/h}$.
   - **Silent Upper-Bound Clamping Drop:** When entering a target rate near the
     configured hard ceiling (`MaxRate`), a single extra press of
     $\mathord{\uparrow\uparrow}$ saturates at `MaxRate` without an audible
     modal lock, causing subsequent compensating presses of
     $\mathord{\downarrow}$ by a clinician looking at the paper chart to compute
     from `MaxRate` rather than the intended value.
2. **Missing Decimal Point / Key-Bounce 10x–100x Overdose on Numeric Keypads (B.
   Braun / Hospira / Alaris PC Unit):** On keypad-based pumps modeled in
   Thimbleby's *Press On* and PVSio-web studies, entering `1`, `.`, `5` when the
   decimal-point key suffers contact bounce or when a leading zero is omitted in
   modes that silently ignore `.` above $100\text{ mL/h}$ parses `1.5` as
   **`15`** (10x overdose) or `10.5` as **`105`** without raising a syntax error
   (`StepResult.stuck` / modal confirmation prompt).
- **Architectural lesson for Anneal:**
  1. **Total, prefix-free input parsing in `BehaviorCodec` (`decodeOut = none` /
     invalid-input rejection):** In Anneal's `PartialBehaviorCodec`
     (`reports/anneal-behavior-codec-and-progress-refinement-2026`),
     `decodeQuery` and `decodeOut` must reject syntactically malformed or
     ambiguous keystroke sequences (such as two decimal points `1..5`, an
     ignored decimal point above a decade threshold, or an unacknowledged
     saturation clamp) by returning `none` (or transitioning to an explicit
     modal error state in `SemObs`), rather than silently coercing `1.5`
     $\mapsto$ `15`.
  2. **Algebraic reversibility as a 2-step `SpecOn` invariant:** Requiring
     $\text{stepDown}(\text{stepUp}(s)) = s$ for all interior states
     $s < \text{MaxRate}$ is a direct `L.SpecOn` relational obligation on the UI
     `SmallStepMachine`.

#### 4.2 Therac-25 Radiation Therapy Linear Accelerator Race Conditions and 8-Bit Counter Overflow (1985–1987, Leveson and Turner 1993)

`Basis: documentation + source + derived`

Between June 1985 and January 1987, the **Therac-25** computer-controlled
medical linear accelerator (manufactured by Atomic Energy of Canada Limited,
AECL) delivered massive radiation overdoses (15,000–25,000 rads of raw 25 MeV
electron beam instead of 200 rads of X-ray photon therapy) to six patients
across clinics in the United States and Canada, killing three and permanently
maiming three. Nancy Leveson and Clark Turner's landmark forensic investigation
(*"An Investigation of the Therac-25 Accidents"*, IEEE Computer 26(7):18–41,
July 1993, `doi:10.1109/MC.1993.274940`) traced the accidents to two distinct
bugs in the PDP-11 assembly real-time executive after AECL removed the hardware
mechanical interlocks present in the earlier Therac-20:

1. **The `Treat` / `Hand` / `Datent` 8-Second Cursor-Edit Race Condition
   (Kennestone, Ontario, and Yakima accidents):**
   - *Mechanism:* The PDP-11 software ran concurrent tasks communicating through
     shared memory without locks. When the radiation technician typed treatment
     parameters on the DEC VT100 terminal, the keyboard handler (`Datent`) wrote
     the mode (`X` for 25 MeV X-ray vs. `E` for low-current Electron mode) into
     a shared variable `MEOS` (2-byte mode/energy word) and set the shared
     variable `Data Entry Complete` (`Tphase = 1`) as soon as the cursor reached
     the bottom `Command` line. Once `Tphase` transitioned, the `Treat` task
     read `MEOS` to configure the bending magnets (`Ptime`, taking ~8 seconds)
     and independently verified that the rotating turntable (`Hand` task) had
     placed the heavy tungsten X-ray target/beam-flattener in the beam path.
     **However, `Datent` only copied edits into the magnet-setting parameter
     block on initial entry, unless it noticed the cursor had moved back up.**
     If an experienced operator typed `X` (X-ray, setting high 25 MeV beam
     current), realized they meant `E` (Electron), and used the VT100 `Up-Arrow`
     key to overwrite `X` with `E`
      and return to the `Command` line *within the 8-second magnet-setting
      window*,
     the turntable task saw the updated `E` (rotating the tungsten target *out*
     of the beam path for low-energy electrons) while the magnet/beam-current
     task never re-read the edited memory word (because the `Datent` completion
     flag was already non-zero), firing a raw, unattenuated 25 MeV high-current
     electron beam directly into the patient!
2. **The Tyler Overflow Bug (8-Bit Shared Flag `Class3` Incrementing to `0`):**
   - *Mechanism:* In the `House` housekeeping task (`Set-Up Test` phase), a
     1-byte unsigned shared variable named `Class3` held the error count of
     collimator/turntable position checks: `Class3 == 0` meant **all interlocks
     verified safe**, whereas `Class3 != 0` meant **unsafe / inhibit beam**.
     Instead of assigning `Class3 := 1` (`MOVB #1, CLASS3`) when a check failed,
     the assembly routine executed `INCB CLASS3` (incrementing `Class3` by 1 on
     every 16.7 ms cycle while the upper collimator was still aligning). Every
     **256th pass** (~4.2 seconds), the 8-bit `INCB CLASS3` wrapped around from
     `255` (`0xFF`) to **`0` (`0x00`)**! If the operator pressed the `Set` key
     during that exact 16.7 ms tick when `Class3 == 0`, the software concluded
     the collimator was aligned and enabled the high-energy beam while the
     field-light mirror was still in the beam path.
- **Architectural lesson for Anneal:**
  1. **Machine-word modular wraparound vs. mathematical `Nat` in target
     semantics (`BoundaryCanarySuite`):** The Therac-25 `INCB CLASS3` bug
     (`255 + 1 = 0` turning an error counter into `0 = Safe`) is the exact
     real-world catastrophe that motivates Anneal's `BoundaryCanarySuite` guard
     `M01`/`X01`
     (`reports/anneal-structural-external-calls-and-tcb-mutation-testing-2026`
     and `reports/anneal-polar-ctfe-admission-and-semantic-polarity-2026`),
     which refutes any trusted evaluator that models fixed-width registers
     (`u8`/`u64`) using unbounded `Nat` addition instead of modular wraparound
     or checked overflow traps.
  2. **Call-site / actuation-site invariant re-verification
     (`StepResult.externalCall`):** In the Therac-25 cursor-edit race, the
     system checked magnet/turntable consistency at the *beginning* of an
     8-second asynchronous hardware routine while allowing concurrent
     shared-state mutation before firing the electron gun. Under Anneal's
     `StepResult.externalCall boundaryInv next`, firing the physical actuator
     (the electron beam) is an external transition whose `boundaryInv`
     (`BeamCurrent == Low ∨ TurntablePosition == XRayTargetLocked`) must
     evaluate to `true` on the **current state at the exact step of beam
     actuation**, not 8 seconds earlier.

#### 4.3 TCAS II Mid-Air Collision over Überlingen (July 1, 2002) and ACAS X Hybrid-Systems Boundary Bugs Uncovered in `KeYmaera` (Jeannin and Platzer 2015–2017)

`Basis: normative + source + documentation`

Airborne Collision Avoidance Systems (**TCAS II** and its FAA NextGen successor
**ACAS X**) issue vertical Resolution Advisories (`RA`: `Climb` at
$\ge 1500\text{ ft/min}$, `Descend` at $\le -1500\text{ ft/min}$,
`Increase Climb`, `Maintain`, or `Reversal`) when two aircraft approach a Near
Mid-Air Collision (NMAC) cylinder ($|h_1 - h_2| < 100\text{ ft}$ vertically and
$r < 500\text{ ft}$ horizontally).

Two major classes of failures—one fatal operational disaster and one set of
formally discovered design defects—illustrate the verification hazards of
cyber-physical rulebooks:

1. **The 2002 Überlingen Mid-Air Collision (Bashkirian Airlines Flight 2937 and
   DHL Flight 611, July 1, 2002; German BFU Investigation Report `AX001-1-2/02`,
   May 2004):**
   - *Mechanism:* At 21:35 UTC over Überlingen, Germany, a Tupolev Tu-154M (BTC
     2937) and a Boeing 757-200SF (DHX 611) converged at Flight Level 360
     ($36,000\text{ ft}$). At 43 seconds before impact, **TCAS II v7.0**
     simultaneously issued coordinated complementary advisories: `Descend` to
     DHL 611 and `Climb` to BTC 2937. However, 7 seconds earlier, an overloaded
     Zurich air traffic controller had verbally instructed BTC 2937 to
     *descend*. Following Russian aviation manual priorities that treated ATC
     instructions as superseding TCAS, the BTC 2937 crew descended—matching DHL
     611's TCAS-commanded descent! Under TCAS II v7.0 logic (**Change 7.0**), a
     reversal logic condition (`Change E7`) required `TCAS` to detect that the
     intruder was failing to follow its RA and reverse DHL 611's advisory from
     `Descend` to `Climb`; however, Change 7.0 suppressed the reversal when
     vertical separation was initially increasing or gated on a delayed altitude
     crossing threshold, so DHL 611's TCAS **never issued a `Climb` reversal**
     (issuing only `Increase Descent` at 22 seconds before impact), and both
     aircraft descended into each other at $29,300\text{ ft}$, killing all 71
     aboard. This led to Eurocontrol/FAA **TCAS II Version 7.1** (`CP112E`),
     which patched the `reversal` state-machine guard for non-compliant
     intruders.
2. **ACAS X Unsafe Advisory Regions Uncovered via `KeYmaera` Hybrid-Systems
   Verification (Jeannin, Ghorbal, Kouskoulas, Gardner, Schmidt, Zawadzki, and
   Platzer, TACAS 2015 / EMSOFT 2015 / STTT 2017,
   `doi:10.1007/s10009-016-0434-1`):**
   - *Mechanism:* Unlike TCAS II's handwritten rule tables, FAA's **ACAS X**
     generates a compressed multi-gigabyte lookup table by solving a discretized
     Markov Decision Process (MDP) via dynamic programming over state tuples
     $(h, \dot{h}_{\text{own}}, \dot{h}_{\text{int}}, \tau, \text{prevRA})$.
     Jeannin, Platzer, and co-authors formulated a continuous Differential
     Dynamic Logic ($\text{d}\mathcal{L}$) safe-able region invariant in the
     **`KeYmaera`** theorem prover (accounting for 5-second pilot response
     delay, $g/4$ to $g/3$ vertical acceleration bounds, and two-sided
     upper/lower parabolic trajectory envelopes) and checked the industrial ACAS
     X Run 13 lookup table against the proved hybrid envelope. They discovered
     **thousands of state-space points where the ACAS X MDP lookup table issued
     unsafe advisories** that could lead to an NMAC even under nominal pilot
     response:
     - **MDP Soft-Penalty Tradeoff ("Goodharting the Reward Function"):**
       Because the MDP solver optimized a numeric reward function combining a
       large finite penalty for NMAC ($-10,000$) with small penalties for
       issuing disruptive alerts or reversals ($-10$), in boundary states where
       an NMAC had low probability under the assumed Gaussian vertical-rate
       transition kernel, the MDP preferred issuing a weak advisory
       (`Do Not Descend` instead of `Climb`) to save the alert penalty—violating
       hard worst-case kinematic safety!
     - **Multilinear Interpolation & Discretization Artifacts:** Between
       discrete grid vertices $(h_i, \dot{h}_j, \tau_k)$, continuous aircraft
       kinematics crossed the parabolic safety boundary inside a grid cell whose
       corners were all marked safe.
- **Architectural lesson for Anneal:**
  1. **Separating hard safety (`Partial.ub` / `WellFormedOn`) from soft
     optimization (`specs`):** The ACAS X MDP failure—where a numeric cost
     function traded off a hard collision-avoidance constraint against a soft
     pilot-comfort penalty—demonstrates why Anneal
     (`Trusted/Refinement.lean:145-180`) strictly separates the non-negotiable
     baseline safety lattice (`Partial.ub` and `L_src.WellFormedOn pre`, where
     `defined = False` is the top element $\top$ that cannot be averaged away by
     probabilities) from secondary functional preferences (`specs`).
  2. **Sound upward abstraction of discrete lookup tables by continuous
     envelopes (`Abstracts L_hybridEnvelope L_lookupTable`):** Following Jeannin
     and Platzer's architecture, a 2-gigabyte MDP lookup table synthesized by an
     untrusted numerical solver need not be trusted: Anneal's `Abstracts`
     relation checks in Lean that every discrete cell of the lookup table
     refines the symbolic $\text{d}\mathcal{L}$ safe-separation inequality
     (including cell-width Lipschitz/Taylor interpolation padding), while
     `StepResult.externalCall` models non-compliant intruder maneuvers (such as
     the Überlingen BTC 2937 descent) via demonic choice over physical aircraft
     acceleration bounds.

### 5. Cross-Domain Synthesis Matrix: Mapping Historical Failures to Anneal's Four Trusted Primitives

`Basis: derived`

The table below synthesizes all 14 historical postmortem classes across DeFi,
statutory law, accounting, voting, auctions, financial markets, medical devices,
and aviation, showing the exact failure mechanism and the corresponding Anneal
primitive in `trusted/lean/Trusted/` (and its reference-corpus hardening
extensions) that closes the vulnerability class:

| Historical Incident / System | Domain & Date | Primary Failure Mechanism | Anneal Primitive 1: `Language`, `SemObs` & `Partial` (`defined` vs. `Partial.ub`) | Anneal Primitive 2: `BehaviorCodec`, `Compiles` & `Abstracts` | Anneal Primitive 3: `StepResult.externalCall`, `EventualBehaviorOf`, `ProductiveOn` & `InhabitedPre` | Anneal Primitive 4: `VerificationResult`, `TrustPolicy` & `BoundaryCanarySuite` |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Euler Finance (\$197M)** | DeFi Lending (`2023-03-13`, EIP-14) | New `donateToReserves` function omitted `checkLiquidity` health check, allowing self-inflicted bad debt and profitable self-liquidation | `Partial.ub` on account solvency breach (`collateral * c < debt / b`) | `Compiles` requires every lowered entrypoint to preserve `SemObs` reserve solvency | `ProductiveOn` ensures healthy liquidations succeed without reverting | Whole-crate `CrateTheorem` (`EnsuresRetLibInv` on all `pubSafe` fns); unproved upgrade methods must be explicitly listed in `waived` |
| **Curve Finance / Vyper `@nonreentrant` (\$70M)** | Smart-Contract Compiler (`2023-07-30`, Vyper `0.2.15`–`0.3.0`) | `data_positions.py` allocated distinct storage slots to `remove_liquidity` and `add_liquidity` sharing `@nonreentrant('lock')` | Source semantics blocks re-entrant entry; target EVM bytecode exhibits cross-function state corruption (`Partial.ub`) | **`Compiler.Verified` & `Compiles`:** target bytecode fails storage-slot simulation against source lock semantics | **`StepResult.externalCall`:** raw ETH `CALL` before `self.balances` update violates `boundaryInv` if any entrypoint can enter unlocked | Rejects trusting source-only audits (`L_src.sem s ≤ spec`) without target compilation proof (`Compiles`) |
| **Lendf.Me (\$25M) & Balancer/Curve Read-Only Re-Entrancy** | DeFi Callbacks (`2020-04-19` / `2022–2023`) | ERC-777 `tokensToSend` and native ETH `receive()` callbacks re-entered mutating or `view` oracle functions (`get_virtual_price`) mid-update | `Partial.ub` on share-price or balance-conservation violation | `obs_decodeOut` preserves observable oracle price invariants across external boundaries | **Direct hit for `StepResult.externalCall`:** `boundaryInv = false` steps immediately to `.failed .ub` if `AdtInv` is broken at callback site | `BoundaryCanarySuite` includes explicit re-entrant callback refutation canary (`canary_reentrant_callback_rejected`) |
| **Wormhole (\$324M), Nomad (\$190M), Beanstalk (\$182M) & ERC-4626 Inflation** | Bridges, Governance & Vaults (`2022`) | Spoofed `Sysvar` account (`load_instruction_at`), `confirmAt[0x00] = 1` zero-root bug, 0-delay flash-loan `emergencyCommit`, and `1 wei` share rounding | Unproven message acceptance or share theft > rounding bound is `Partial.ub` | `PartialBehaviorCodec` (`decodeOut = none`) rejects unvalidated `Sysvar` capability pointers and bounds rational-to-`U256` rounding drift | `StepResult.externalCall` models flash-loan / donation interleavings; `EventualBehaviorOf` enforces multi-block timelock separation | Polar admission guards (`ConstIsSafe` / non-zero root canaries) prevent mapping default `0x00` to verified `true` |
| **Certora CVL Vacuity, `HAVOC_ECF` & Move Prover / Verifier Bugs** | Formal Verifiers (`2020–2024`) | Contradictory `require` rules passing vacuously (`--rule_sanity`), `HAVOC_ECF` ignoring re-entrancy, and Boogie/bytecode borrow-checker bugs | `WellFormedOn pre` proved alongside `specs` so vacuous functional specs never weaken baseline safety | Proof-gated compilation eliminates intermediate verifier IR (`Boogie` / `AnSSA`) from the TCB via `Preorder.le_trans` | `InhabitedPre pre` + `ProductiveOn pre prog` statically refute vacuous `require` preconditions; `externalCall` replaces optimistic `HAVOC_ECF` | Positive per-obligation `ScopedVerificationResult` (`ob.id ∈ waived ∨ ob.prop`) prevents `False.elim` explosion from contradictory assumptions |
| **French DGFiP `M`-Language & Family-Benefit Bugs (`Mlang` / `Catala`)** | Statutory Tax & Benefits (`2020–2021`, ICFP/CC 2021) | Manual flattening of statutory exception hierarchies inverted priority of family-benefit phase-outs; `undef` coerced to `0.0` | Equal-priority statutory conflict maps to `Partial.ub`; missing default (`EmptyError`) maps to `.stuck` | `Compiles StatuteLang RustLang` proves imperative tax binary refines declarative prioritized default calculus | `ProductiveOn ValidHousehold statute` proves every taxpayer profile resolves to a unique, non-stuck legal determination | `TrustPolicy` tracks transitional tax-year rounding waivers explicitly |
| **Australian Robodebt & Section 1073B Apportionment** | Welfare Compliance (`2015–2023`, Royal Commission `2023-07-07`) | Replaced 26 fortnightly income inputs $(y_1, \dots, y_{26})$ with annual average $Y/26$ inside a concave entitlement formula (violating Jensen's Inequality) | Raising an overpayment debt exceeding actual fortnightly statutory liability is `Partial.ub` | **Refinement vs. Abstraction polarity:** non-injective sum projection $Y = \sum y_t$ violates `decodeQuery_encodeQuery`; averaging goes in the wrong lattice direction (`≥` vs. `≤`) | Demonic choice (`StepResult.choice .demonic`) over all $(y_1, \dots, y_{26})$ summing to $Y$ bounds provable minimum debt | Rejects unlawful administrative assumptions via `TrustPolicy` audit |
| **UK Post Office Fujitsu Horizon (`Bates v Post Office`)** | Retail Accounting Ledger (`1999–2019`, `[2019] EWHC 3408`) | Frozen UI `Enter` retries (**Dalmellington**), duplicate Riposte rows (**Callendar Square**), and local-cache/central-DB split-brain (**Receipts & Payments Mismatch**) | Unbalanced double-entry posting ($\sum \text{Dr} \neq \sum \text{Cr}$) or phantom duplicate debit is `Partial.ub` | `BehaviorCodec` with idempotency keys maps repeated UI retries to stuttering on 1 logical transaction (`obs_decodeOut`) | `EventualBehaviorOf` collapses $k$ network retry steps into 1 committed transaction; single-source binding prevents local/central split-brain | Eliminates blind legal presumption of correctness in unverified software (`trustLevel` accounting) |
| **US SNAP & Medicaid (`MAGI` vs. `non-MAGI`) Engines** | Social Benefits (`2014–2024`) | Contradictory cross-category guards (`isMagi ∧ ¬isMagi`) dropping disabled self-employed applicants without *ex parte* review | Unhandled applicant drop is `.stuck` (`defined = False`) | `Compiles FederalStatute StateIesEngine` enforces federal 42 C.F.R. § 435.916 floor | **`InhabitedPre` & `ProductiveOn`:** proves every statutory eligibility category is inhabited and *ex parte* fallback is total | State Section 1115 waivers modeled as positive `waived` IDs in `VerificationResult` |
| **SwissPost / Scytl E-Voting Shuffle & Commitment Flaw** | Cryptographic E-Voting (`2019–2020`, IEEE S&P 2020) | Universal Verifier assumed commitment key $ck = (g, g_1, \dots, g_n)$ had no known discrete-log trapdoor without checking seed/NIZK construction; non-injective Fiat-Shamir hashing | Accepting a forged tally proof is `Partial.ub` | `decodeQuery_encodeQuery` enforces injective length-prefixed serialization into Fiat-Shamir transcripts | Constructive witness verification of setup parameters inside the verifier | **Universal `TCBModel` realizability:** prohibits hiding `TrapdoorFree(ck)` as an unchecked implicit TCB assumption |
| **Australian Senate STV Tabulation (`EasyCount` vs. Coq)** | Election Tabulation (`2013–2020`, Pattinson et al.) | Ambiguous parcel-grouping order before integer truncation $\lfloor k \cdot \text{TV}_c \rfloor$ and implicit array-index tie-breaking | Dropping valid votes or unauthorized tie-break is `Partial.ub` | `Compiles StatutoryStv CertifyingTabulator` pins exact rational-to-fixed-point parcel truncation | `StepResult.externalCall` models statutory Electoral Officer lot-drawing for exact ties; `ProductiveOn` proves loop termination | Audited certificate checker verifies round-by-round transfer log |
| **Knight Capital `SMARS` `Power Peg` (\$440M)** | Equity Order Routing (`2012-08-01`, SEC Rel. `34-70694`) | Repurposed RLP bitflag triggered dead `Power Peg` code (missing cumulative fill check) on 1 of 8 servers left un-updated | Emitting child orders with $\sum q_{\text{child}} > Q_{\text{parent}}$ is `Partial.ub` | `BehaviorCodec` binds wire bitflag semantics to exact protocol version | **`EventualBehaviorOf`:** rejects non-terminating child-order emission loops that never reach `.terminated` | Single-source `.olean`-bound artifact hashing prevents 7-of-8 server binary/codec drift |
| **New Zealand 1990 Spectrum Auction & VCG Sybil Paradox** | Mechanism Design (`1990` / Ausubel & Milgrom `2006`) | Thin competition (NZ\$100k bid paying NZ\$6) and superadditive package bids enabling \$0-payment Core violations and Sybil split-bidding | Profitable Sybil deviation or Core blocking-coalition breach is `Partial.ub` | `Compiles MechanismSpec SolverCode` pairs MILP solver with primal-dual certificate checker | `StepResult.externalCall` models open-world Sybil identity splitting ($1 \mapsto k$ pseudonyms); `ProductiveOn` proves market clearing | Separates NP-hard optimality timeout waivers (`waived`) from strict Individual Rationality and Core safety |
| **Alaris GP Pump (`PVS`), Therac-25 & TCAS II / ACAS X (`KeYmaera`)** | Medical Devices & Aviation (`1985–2017`) | Alaris chevron rounding/10x key-bounce; Therac-25 8-bit `INCB CLASS3` wraparound & 8s cursor race; Überlingen reversal failure & ACAS X MDP soft-penalty unsafe cells | Overdose, unshielded 25 MeV beam, or Near Mid-Air Collision (NMAC) is `Partial.ub` ($\top$, never traded off against soft penalties) | `Abstracts HybridEnvelope AcasLookupTable` verifies discrete MDP tables against continuous $\text{d}\mathcal{L}$ barrier certificates; `decodeOut = none` rejects malformed keystrokes | `StepResult.externalCall` re-verifies `boundaryInv` at exact beam-firing step and models non-compliant intruder aircraft maneuvers | **`BoundaryCanarySuite` (`M01`/`X01`):** kills 8-bit/64-bit modular wraparound bugs (`255 + 1 = 0`) and maps GSN hardware assumptions to `TrustPolicy` |

## Boundaries

To prevent future agents from over-generalizing the historical comparisons in
this report, the following boundaries apply:

1. **Not examined — direct execution of third-party blockchain VMs, `Catala`,
   `PVS`, or `KeYmaera X` inside Anneal's build:** The findings on Euler
   Finance, Vyper, Certora, Move, `Catala`, Robodebt, Horizon, SwissPost/Scytl,
   Australian STV, Knight Capital, VCG auctions, Alaris GP, Therac-25, and TCAS
   II / ACAS X are established from primary source repositories, CVEs, court
   judgments, regulatory inquiry reports, and peer-reviewed verification papers
   (`documentation`, `normative`, and `source` evidence). Anneal's repository
   (`joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`) currently targets
   Rust (`Runtime(PostCleanup)` MIR and x86-64 machine code) checked in Lean 4;
   instantiating `Language` for EVM bytecode, `Catala` default terms, or hybrid
   ODE flowpipes is an architectural design mapping (`derived`), not a currently
   shipping compiler backend in `trusted/rustc-capture/`.
2. **Known not to apply — purely economic or human-organizational failures
   outside formal specifications:** Formal verification of software and
   mechanisms in Anneal cannot by itself prevent a legislature from enacting a
   socially regressive tax schedule, an auctioneer from setting a zero reserve
   price in a thin single-item market (as in parts of the 1990 New Zealand
   spectrum auction), or an air traffic controller from issuing a verbal command
   contradicting an onboard TCAS advisory (as at Überlingen) unless the formal
   environmental model (`StepResult.externalCall` and `Query`) explicitly
   includes non-compliant human/counterparty behavior in its demonic choice set.
3. **Unsupported — probabilistic expected-value tradeoffs over `Partial.ub`:**
   Anneal's `Partial B` type constructor
   (`trusted/lean/Trusted/Refinement.lean:245-261`) models Undefined Behavior
   (`defined = False`) as the single qualitative top element `Partial.ub`.
   Quantitative Markov Decision Process (MDP) reward tradeoffs (such as ACAS X's
   expected-cost scoring) cannot be used to relax `defined = True`; any
   probabilistic or expected-utility reasoning must live inside the defined
   payload `B` (`Out → Prop` instantiated over probability mass functions in
   `theory/`) while preserving hard `defined = True` safety envelopes
   unconditionally.

## Evidence

All observations in this report were gathered and cross-checked on `2026-10-31`
against the following primary sources:

1. **Anneal Verification Framework and Hardening Corpus (`source` +
   `execution`):**
   - `joshlf/anneal@e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`:
     - `trusted/lean/Trusted/Refinement.lean` (`Preorder`, `Partial`,
       `Partial.ub`, `Language`, `SpecOn`, `WellFormedOn`, `Compiles`,
       `Abstracts`, `Compiler.SoundOn`, `Compiler.Verified`,
       `TrustedAssumption`, `TrustPolicy`, `VerificationResultOn` at
       `L207-472`).
     - `trusted/lean/Trusted/StepResult.lean` (`TerminationKind`, `StepResult`,
       `PrefixOutcome.isSafe`, `ExecQuery`, `ExecOut`, `SmallStepMachine`,
       `ReachesPrefix`, `BehaviorOf` at `L58-199`).
     - `trusted/lean/Trusted/MirSemantics.lean` (`AdtInv`,
       `MirVal.satisfiesInv`, `FnKind`, `EnsuresRetLibInv`, `CrateTheorem`).
   - `joshlf/anneal@df55c524a051d59e7dd35564f282b30d29133392`
     (`zerocopy/reference` branch):
     - `reports/anneal-behavior-codec-and-progress-refinement-2026/REPORT.md`
       and `support/BehaviorCodecExpressiveness.lean` (`BehaviorCodec`,
       `PartialBehaviorCodec`, `EventualBehaviorOf`, `ProductiveOn`,
       `InhabitedPre`).
     - `reports/anneal-structural-external-calls-and-tcb-mutation-testing-2026/REPORT.md`
       and `support/StructuralExternalCallAndCanaries.lean`
       (`StepResult.externalCall`, `CallerFramePreserved`,
       `open_world_callback_composition_sound`, `BoundaryCanarySuite`).
     - `reports/anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026/REPORT.md`
       and `support/ProofGatedCompilationAndTrustPolicy.lean` (`TCBModel`,
       `ScopedVerificationResult`, positive per-obligation waiver isolation).
     - `reports/anneal-polar-ctfe-admission-and-semantic-polarity-2026/REPORT.md`
       (four-quadrant semantic polarity matrix and negative-polarity vacuity
       prevention).
     - `reports/anneal-rustc-obligation-inventory-and-single-source-codegen-2026/REPORT.md`
       (whole-crate obligation inventory and single-source `.olean`-bound
       emission).
2. **DeFi Exploits and Smart-Contract Verification (`source` +
   `documentation`):**
   - **Euler Finance:** Governance proposal EIP-14 commit introducing
     `donateToReserves` in `contracts/modules/EToken.sol` without
     `checkLiquidity`; Ethereum Mainnet block `16817996` (`2023-03-13`);
     Omniscia and Certora post-incident analyses of EIP-14 and Euler V2
     invariant verification.
   - **Curve Finance / Vyper Compiler:** GitHub Security Advisory
     `GHSA-5824-cm3x-3c38` (`vyperlang/vyper`, `2023-07-30`, affecting versions
     `0.2.15`, `0.2.16`, `0.3.0`), root-caused to per-function storage-slot
     incrementing in `vyper/semantics/analysis/data_positions.py`
     (`set_reentrancy_key_position`).
   - **Wormhole, Nomad, Beanstalk, Mango Markets, Lendf.Me, ERC-4626:** Wormhole
     Solana bridge exploit (`2022-02-02`, unvalidated `Sysvar: Instructions`
     account in `verify_signatures` via `load_instruction_at`); Nomad
     `Replica.sol` upgrade (`2022-08-01`, `confirmAt[bytes32(0)] = 1` accepting
     unproven messages); Beanstalk Farms governance exploit (`2022-04-17`,
     single-block flash-loan supermajority in `emergencyCommit`); Mango Markets
     oracle manipulation (`2022-10-11`, US DOJ SDNY indictment and conviction of
     Avraham Eisenberg); Lendf.Me ERC-777 `imBTC` `tokensToSend` re-entrancy
     (`2020-04-19`); OpenZeppelin ERC-4626 virtual-shares defense documentation.
   - **Certora, KEVM, and Move Prover / Bytecode Verifier:** Certora Prover
     documentation on `--rule_sanity` (`basic` / `advanced` vacuity detection)
     and external call summaries (`HAVOC_ECF` vs. `HAVOC_ALL`); Aptos/Sui Move
     Bytecode Verifier reference-safety and stack-usage advisories (Zellic /
     OtterSec disclosures, 2022–2023) and Move Prover Boogie shift/borrow
     modeling analyses.
3. **Statutory Tax, Social Benefits, and Accounting Ledgers (`normative` +
   `documentation` + `source`):**
   - **`Mlang` and `Catala`:** Denis Merigoux, Raphaël Monat, and Jonathan
     Protzenko, *"A Modern Compiler for the French Tax Code"*, CC 2021
     (`doi:10.1145/3446804.3446850`); Denis Merigoux, Nicolas Chataing, and
     Jonathan Protzenko, *"Catala: A Programming Language for the Law"*, Proc.
     ACM Program. Lang. 5 (ICFP 2021), Article 77 (`doi:10.1145/3473582`),
     `CatalaLang/catala`.
   - **Australian Robodebt & Section 1073B:** *Report of the Royal Commission
     into the Robodebt Scheme* (Commissioner Catherine Holmes AC SC, July 7,
     2023, ISBN `978-1-921091-92-6`); *Amato v The Commonwealth of Australia*
     (Federal Court of Australia, VID611/2019); Commonwealth Ombudsman reports
     on *Social Security Act 1991 (Cth)* Section 1073B income apportionment
     (2023–2024).
   - **UK Post Office Horizon:** *Bates & Others v Post Office Ltd (No 6:
     Horizon Issues)* `[2019] EWHC 3408 (QB)` (Mr Justice Fraser, December 16,
     2019, including the Technical Appendix detailing `PEAK PC0061213` Callendar
     Square, `PEAK PC0208735` Dalmellington / Branch Outreach, and
     `PEAK PC0203589` Receipts and Payments Mismatch bugs).
   - **US SNAP & Medicaid:** 7 U.S.C. § 2014 / 7 C.F.R. § 273.9 (SNAP income and
     deduction rules); 42 U.S.C. § 1396a(e)(14) and 42 C.F.R. §§ 435.603,
     435.916(f)(1) (`MAGI` vs. `non-MAGI` *ex parte* redetermination mandates).
4. **Voting, Auctions, and Financial Exchanges (`normative` + `documentation` +
   `source`):**
   - **SwissPost / Scytl E-Voting:** Sarah Jamie Lewis, Olivier Pereira, and
     Vanessa Teague, *"Ceci n'est pas une preuve: How not to prove your election
     outcome"* (March 2019); Thomas Haines, Sarah Jamie Lewis, Olivier Pereira,
     and Vanessa Teague, *"How not to prove your election outcome"*, 2020 IEEE
     Symposium on Security and Privacy (S&P), pp. 644–660
     (`doi:10.1109/SP40000.2020.00055`).
   - **Australian Senate STV:** Dirk Pattinson and Mukesh Tiwari, *"Votes as
     Proofs: Modular Formalisation of STV in Coq"* / Rajeev Goré, Dirk
     Pattinson, and Mukesh Tiwari (ITP / IJCAR / E-Vote-ID); *Commonwealth
     Electoral Act 1918 (Cth)* Section 273.
   - **Knight Capital:** U.S. Securities and Exchange Commission, *In the Matter
     of Knight Capital Americas LLC*, Exchange Act Release No. 34-70694, Admin.
     Proc. File No. 3-15570 (October 16, 2013).
   - **VCG and Spectrum Auctions:** Lawrence M. Ausubel and Paul Milgrom, *"The
     Lovely but Lonely Vickrey Auction"*, Chapter 1 in *Combinatorial Auctions*
     (MIT Press, 2006, pp. 17–40); John McMillan, *"Selling Spectrum Rights"*,
     Journal of Economic Perspectives 8(3):145–162 (1994); Makoto Yokoo, Yuko
     Sakurai, and Shigeo Matsubara, *"The Effect of False-Name Bids in
     Combinatorial Auctions: New Fraud in Internet Auctions"*, Games and
     Economic Behavior 46(1):174–188 (2004).
5. **Medical Devices and Aviation Collision Avoidance (`normative` + `source` +
   `documentation`):**
   - **Alaris GP Infusion Pump (`PVS`):** Paolo Masci, Rimvydas Rukšėnas, Paul
     Curzon, and Harold Thimbleby / Patrick Oladimeji et al., formal models of
     the CareFusion Alaris GP volumetric pump in `PVS` and `PVSio-web` (CAV
     2013, FM 2014, SAFECOMP 2015); Harold Thimbleby, *Press On: Principles of
     Interaction Programming* (MIT Press, 2007) and *Fix IT* (Oxford University
     Press, 2021).
   - **Therac-25:** Nancy G. Leveson and Clark S. Turner, *"An Investigation of
     the Therac-25 Accidents"*, IEEE Computer 26(7):18–41 (July 1993,
     `doi:10.1109/MC.1993.274940`).
   - **Überlingen TCAS II & ACAS X (`KeYmaera`):** German Federal Bureau of
     Aircraft Accidents Investigation (BFU), *Investigation Report AX001-1-2/02*
     (May 2004, Überlingen mid-air collision on July 1, 2002); Jean-Baptiste
     Jeannin, Khalil Ghorbal, Yanni Kouskoulas, Ryan Gardner, Aurora Schmidt,
     Erik Zawadzki, and André Platzer, *"A Formally Verified Hybrid System for
     Safe Advisories in the Next-Generation Airborne Collision Avoidance
     System"*, International Journal on Software Tools for Technology Transfer
     (STTT) 19(6):717–741 (2017, `doi:10.1007/s10009-016-0434-1`; earlier
     versions in TACAS 2015 and EMSOFT 2015).

## Revalidation

To verify that Anneal's trusted primitives and reference-corpus hardening models
continue to block the four cross-domain failure classes documented in this
report after any modification to `trusted/lean/Trusted/` or `theory/Anneal/`:

1. **Re-verify the mechanized Lean 4 proofs for `BehaviorCodec`,
   `EventualBehaviorOf`, `StepResult.externalCall`, `ScopedVerificationResult`,
   and `BoundaryCanarySuite`:** Run the Lean 4.34.1 kernel checker with
   asynchronous elaboration disabled and kernel type-checking enforced across
   the preserved support modules in the companion Anneal hardening reports on
   `refs/heads/reference`:

   ```console
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     reports/anneal-behavior-codec-and-progress-refinement-2026/support/BehaviorCodecExpressiveness.lean
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     reports/anneal-structural-external-calls-and-tcb-mutation-testing-2026/support/StructuralExternalCallAndCanaries.lean
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     reports/anneal-tcb-realizability-proof-gated-compilation-and-audit-probes-2026/support/ProofGatedCompilationAndTrustPolicy.lean
   ```

2. **Check the discriminating theorems corresponding to each historical failure
   archetype:**
   - *Curve/Vyper compiler divergence & Knight Capital loop rejection:* Verify
     that `eventual_wellFormed_iff_prefix_wellFormed` and
     `PartialBehaviorCodec.comp` in `BehaviorCodecExpressiveness.lean` elaborate
     with zero axioms and reject infinite-loop targets (`loopBody`).
   - *Lendf.Me / Balancer callback re-entrancy & Therac-25 actuation-site
     check:* Verify that `canary_reentrant_callback_rejected` and
     `open_world_callback_composition_sound` in
     `StructuralExternalCallAndCanaries.lean` reject mid-call invariant breaches
     (`boundaryInv = false`) while accepting restored-before-call frames.
   - *Certora vacuity, SwissPost/Scytl unchecked setup assumptions & Euler
     per-obligation waivers:* Verify that `contradictory_hTcb_proves_ub_crate`,
     `alwaysUbCrate_unprovable_under_universal_tcb`, and
     `scoped_omission_isolates_buggy_fn` in
     `ProofGatedCompilationAndTrustPolicy.lean` elaborate with zero axioms.
   - *Therac-25 `Class3` wraparound & Move verifier bit-shift/overflow checks:*
     Verify that `currentX86Model_fails_BoundaryCanarySuite` and
     `instBoundaryCanarySuiteFixedX86Model` in
     `StructuralExternalCallAndCanaries.lean` kill all 13/13 target-semantics
     guard mutations.
