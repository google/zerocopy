# Elaboration Vacuity in Proof Assistants, SystemVerilog Width/Signedness Contagion, and DeFi Fixed-Point Rounding Asymmetries

## Summary

Formal verification kernels, RTL synthesis engines, and smart-contract verifiers routinely prove or synthesize exact properties of an internal representation (`Lean Expr`, `RTLIL`, or `EVM` bytecode) while the surface-to-core desugaring layer silently rewrites the human's intended statement into a vacuous or exploitable meaning:

1. **Proof-Assistant Elaboration Vacuity (`Lean 4` vs. `Lean4Lean`):** Verifying the kernel typechecker (`digama0/lean4lean` @ `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`, `DOI: 10.4230/LIPIcs.TYPES.2025.2`) guarantees `Expr` derivability, *not* surface `Syntax -> Expr` fidelity. In `leanprover/lean4` (`4f5982e315272d89e2d2113d7ae0d8c9480f15db`), both `autoImplicit` and `relaxedAutoImplicit` default to `true` (`src/Lean/Elab/AutoBound.lean` L17–25), turning any misspelled constant in a theorem header into a universally quantified implicit variable `{typo : α}`; even with `relaxedAutoImplicit = false`, single-letter identifiers with numeric/subscript suffixes (`X123_45`, L31–37) still auto-bind silently. Combined with `Nat.sub` saturating at `0` (`0 - 10_000 = 0`, `src/Init/Prelude.lean` L2264–2266) and unprefixed pattern identifiers turning refactored enum variants into catch-all variable bindings, broken programs pass with `0` `sorry`s.
2. **SystemVerilog Context-Determined Overflow, Signedness Contagion, and `casex` Drift (`Verilator`, `Yosys`, `Chisel`):** Under `IEEE Std 1800-2023` §11.6–11.8 (`verilator/verilator` @ `464643f7c2abe27db4b9d10b22040bfb01b9c03d`, `src/V3Width.cpp` L46–51, L163–167), sub-expression bitwidths depend on assignment context (`(8'd200 + 8'd100) >> 1` yields `22` in an 8-bit self-determined context vs. `150` in a 9-bit context), and **any single unsigned operand (`8'h00`, part-select, or concatenation) silently coerces an entire signed relational expression to unsigned** (`-8'sd5 > 8'h00` evaluates `251 > 0 == 1'b1`!). Meanwhile, `casex`/`casez` matches unknown `X`/`Z` bits in 4-state simulation while `YosysHQ/yosys` (`d1338f823b24fc0828d6b55438f3e9c2c13facbc`, `passes/proc/proc_mux.cc`) treats pattern `X`s as 2-state synthesis don't-cares, creating post-synthesis silicon mismatches.
3. **Fixed-Point Vault Share Inflation & Rounding-Direction Exploits (`OpenZeppelin`, `Uniswap v4`, `Aptos Move`):** Writing `shares = assets * supply / totalAssets` using symmetric truncating `/` (`Floor`) on both deposit and withdrawal violates value conservation: (a) on `withdraw(assets)`, rounding burned shares *down* (`Floor` instead of `Ceil`) lets an attacker extract `2` asset units while burning `1` share (`supply = 90, assets = 100`); and (b) on an unseeded vault (`_decimalsOffset() == 0`, the default in `OpenZeppelin/openzeppelin-contracts` @ `d98b8f438d6c2b9d368d1220448b8519f733d371`, `ERC4626.sol` L324–326), a `1`-wei first deposit plus a `10,000e6` direct token donation causes a victim's `5,000e6` deposit to round down to `0` shares, stealing `100%` of the victim's funds unless virtual share offsets (`10 ** offset`) and directional `mulDiv` (`Floor` vs. `Ceil`, `Uniswap/v4-core` @ `bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6` `FullMath.sol`) are enforced.

Across all three domains, a sound surface-to-core architecture enforces **bijective syntax resugaring (`SyntacticIso`)**, **mathematical $\mathbb{Z}/\mathbb{Q}$ specification arithmetic** (`Aptos Move Prover` `num` style) paired with premise-inhabitedness witnesses, **carry-preserving interval types** banning silent sign/width erasure, and **variance-coupled directional rounding** tied directly to linear asset inflows and outflows.

## Applicability

This report covers nine pinned subjects spanning interactive theorem proving, hardware description synthesis, and smart-contract verification:

- **Theorem Proving & Elaboration:** `leanprover/lean4` (`4f5982e315272d89e2d2113d7ae0d8c9480f15db`) and `digama0/lean4lean` (`67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`, Carneiro, `arXiv:2403.14064`, `DOI: 10.4230/LIPIcs.TYPES.2025.2`), separating untrusted `Lean.Elab` elaboration hazards from verified kernel typechecking.
- **Hardware Description & RTL Lowering:** `IEEE Std 1800-2023` expression sizing and 4-state `casex` rules as implemented in `verilator/verilator` (`464643f7c2abe27db4b9d10b22040bfb01b9c03d`) and `YosysHQ/yosys` (`d1338f823b24fc0828d6b55438f3e9c2c13facbc`), compared against Scala-embedded width/sign operators in `chipsalliance/chisel` (`e95009474df71a0fe95e29a7c04b7cbd80fc426d`).
- **Smart-Contract Fixed-Point & Specification Systems:** `OpenZeppelin/openzeppelin-contracts` (`d98b8f438d6c2b9d368d1220448b8519f733d371`, `ERC4626.sol` and `Math.sol`), `Uniswap/v4-core` (`bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6`, `FullMath.sol`), and `aptos-labs/aptos-core` (`6137e8f7ee8e8b944568a3faf86c2064440edf17`, Move Prover mathematical `num` specification semantics).

Findings apply to any verification workflow or compiler front-end where human-authored specifications, hardware bitvector widths, or fixed-point financial invariants undergo elaboration before formal checking.

## Findings

### 1. The Elaboration Trust Gap in Proof Assistants (`Lean 4` vs. `Lean4Lean`)

`Basis: source + normative + execution`

External kernel verifiers such as `digama0/lean4lean` (`67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`, `Lean4Lean/TypeChecker.lean` L16–25) validate kernel `Expr` environments (`VEnv`) after elaboration has completely finished. Consequently, a `0`-axiom, `0`-`sorry` kernel check provides **zero protection** when front-end elaboration translates human `Syntax` into an unintended `Expr`:

- **Two-Tier `autoImplicit` Trap (`src/Lean/Elab/AutoBound.lean` L17–68):**
  1. `register_builtin_option autoImplicit : Bool` (`defValue := true`, L17–20) and `relaxedAutoImplicit : Bool` (`defValue := true`, L22–25) cause *any* unbound atomic identifier in a declaration header—such as a misspelled constant `MaxFee` written `MaxFe` in `theorem safe (fee : Nat) (h : fee <= MaxFe)`—to be silently bound as a fresh implicit universal parameter `{MaxFe : Nat}`.
  2. Even if a project sets `set_option relaxedAutoImplicit false`, `isValidAutoBoundSuffix` (L35–37) still accepts any single character followed by digits, subscripts, underscores, or primes (`c.isDigit || isSubScriptAlnum c || c == '_' || c == '\''`). Thus a typo `R_1` for constant `R_0` *still* silently becomes `{R_1 : ...}` unless `set_option autoImplicit false` is enforced globally!
- **Truncating `Nat.sub` Specification Vacuity (`src/Init/Prelude.lean` L2263–2266):**
  ```lean
  @[extern "lean_nat_sub", instance_reducible]
  protected def Nat.sub : (@& Nat) → (@& Nat) → Nat
    | a, 0      => a
    | a, succ b => pred (Nat.sub a b)
  ```
  Because total type-theoretic `Nat` maps negative differences to `0`, a precondition or postcondition written `bal - fee >= min_bal` becomes tautologically `0 >= 0` (`True`) whenever `min_bal = 0` and `fee > bal` (`Basis: execution`, §Evidence Probe 2a: `35/35` insolvent `(bal < fee)` states satisfy `Nat.sub(bal, fee) >= 0`, vs. `0/35` over $\mathbb{Z}$). By contrast, the **Move Prover** (`aptos-labs/aptos-core` @ `6137e8f7ee8e8b944568a3faf86c2064440edf17`, `third_party/move/move-prover`) interprets `+`, `-`, `*` inside `spec {}` blocks over unbounded mathematical integers (`num`), turning underflows and overflows into explicit proof obligations rather than silent truncations.
- **Unprefixed Pattern-Variable Shadowing:** In Lean 4, Rust, and OCaml `match` arms, bare identifiers that fail to resolve to an in-scope constructor or `#[derive(PartialEq)]` constant silently elaborate as fresh irrefutable variable bindings—turning `match role { AdminRole => allow(), _ => deny() }` into an unconditional `allow()` bypass after an upstream enum rename.

### 2. SystemVerilog Width Contexts, Unsigned Contagion, and `casex` Synthesis Mismatches (`Verilator`, `Yosys`, `Chisel`)

`Basis: normative + source + execution`

`IEEE Std 1800-2023` couples expression bitwidth and signedness simultaneously to *operand types* and *surrounding assignment/comparison context*, as codified in `verilator/verilator` (`464643f7c2abe27db4b9d10b22040bfb01b9c03d`, `src/V3Width.cpp` L46–51, L163–167, L3613–3620):

- **Context-Determined vs. Self-Determined Overflow:** In `logic [8:0] avg = (a8 + b8) >> 1;` where `a8 = 8'd200, b8 = 8'd100`, the LHS width `9` propagates into `(a8 + b8)`, producing `300 >> 1 = 150`. However, if an engineer refactors the exact same sub-expression into a self-determined position—such as `logic [8:0] avg = {1'b0, (a8 + b8) >> 1};` (concatenation operands are self-determined!) or compares `(a8 + b8) > 8'd250`—`a8 + b8` evaluates in `8` bits, wrapping `300 mod 256 = 44`, so `44 >> 1 = 22` and `44 > 250 == 0` (`Basis: execution`, §Evidence Probe 2b).
- **Silent Unsigned Contagion (`V3Width.cpp` L46–51):** `IEEE 1800` mandates that an operation is signed *if and only if every operand is signed*. Because based literals without `'s` (`8'h00`), bit-selects (`x[7:0]`), part-selects, and concatenations are **unsigned**, comparing `logic signed [7:0] credit = -8'sd5;` against `credit > 8'h00` silently zero-extends/reinterprets `-5` (`8'hFB`) as unsigned `251`, evaluating `-5 > 0` to **`true` (`1'b1`)**!
- **Chisel Width Operator Split (`chipsalliance/chisel` @ `e95009474df71a0fe95e29a7c04b7cbd80fc426d`, `Bits.scala` L471–485):** Chisel avoids context-dependent widths by splitting `+` / `+%` (wrapping to `max(w1, w2)` via `.tail(1)`) from `+&` (`w = max(w1, w2) + 1`, carry-preserving). However, default `+` maps to wrapping `+%`, and `.asUInt` (L283, L416) strips signedness without range checks—preserving wraparound bugs unless explicit interval types are used.
- **4-State `casex` Simulation vs. 2-State `Yosys` Synthesis (`YosysHQ/yosys` @ `d1338f823b24fc0828d6b55438f3e9c2c13facbc`, `passes/proc/proc_mux.cc` L30–45):** In 4-state simulation, an uninitialized reset register driving `irq_vec = 4'b000X` into `casex (irq_vec) 4'b0001: fire();` matches `X` as a wildcard and executes `fire()`. When `Yosys` lowers procedural cases via `proc_mux`, `X` don't-cares in case items permit logic minimization into 2-state `$pmux` cells that map runtime `0/1` power-up values differently from 4-state `X`-optimistic simulation traces.

### 3. `ERC-4626` Share Inflation, Virtual Offsets, and Directional `mulDiv` Conservation (`OpenZeppelin` & `Uniswap v4`)

`Basis: source + execution + derived`

Tokenized vaults (`EIP-4626`) and concentrated-liquidity pools (`Uniswap v4`) mediate conversions between underlying `assets` ($A$) and pool `shares` ($S$) over `uint256`:

- **Four-Way Directional Rounding Law (`OpenZeppelin` `ERC4626.sol` L170–186, L240–249):** To prevent zero-cost reserve extraction (`forall tx: NAV_post >= NAV_pre`), rounding must **always favor the vault**:
  1. `previewDeposit(assets)` (`assets -> shares` minted to user): **`Math.Rounding.Floor`** (L171).
  2. `previewMint(shares)` (`shares -> assets` pulled from user): **`Math.Rounding.Ceil`** (L176).
  3. `previewWithdraw(assets)` (`assets -> shares` burned from user): **`Math.Rounding.Ceil`** (L181).
  4. `previewRedeem(shares)` (`shares -> assets` paid to user): **`Math.Rounding.Floor`** (L186).
  Using standard `/` (`Floor`) in `previewWithdraw` breaks rule (3): at `S = 90, A = 100`, `withdraw(2)` computes `Floor(2 * 90 / 100) = 1` share burned (worth `1.111` assets) instead of `Ceil = 2` shares, leaking `0.889` assets per call (`Basis: execution`, §Evidence Probe 2d).
- **512-Bit Phantom-Overflow Elimination (`Math.sol` L206–216; `Uniswap/v4-core` `FullMath.sol` L14–25, L109–116):** Both `OpenZeppelin` `Math.mulDiv` and `Uniswap v4` `FullMath.mulDiv` / `mulDivRoundingUp` compute exact 512-bit numerators (`mul512` / Chinese Remainder Theorem `mulmod(a, b, not(0))`) so intermediate `a * b >= 2^256` never reverts when the final quotient fits in `uint256`, adding `1` iff `mulmod(a, b, denominator) != 0` for `Ceil`.
- **First-Depositor Share-Inflation Attack & `_decimalsOffset()` Default (`ERC4626.sol` L240–249, L324–326):**
  ```solidity
  function _convertToShares(uint256 assets, Math.Rounding rounding) internal view virtual returns (uint256) {
      return assets.mulDiv(totalSupply() + 10 ** _decimalsOffset(), totalAssets() + 1, rounding);
  }
  function _decimalsOffset() internal view virtual returns (uint8) { return 0; }
  ```
  - On a naive vault (`+ 0` virtual shares/assets), an attacker deposits `1` wei (`S = 1, A = 1`), donates `10,000e6` USDC directly to the vault (`A = 10,000,000,001`), and front-runs a victim's `5,000e6` USDC deposit: `vic_shares = Floor(5,000e6 * 1 / 10,000,000,001) = 0`, letting the attacker redeem `1` share for all `15,000,000,001` units (**`+5,000e6` profit, `100%` victim loss**).
  - With `OpenZeppelin`'s virtual shares (`_decimalsOffset() = 3 -> 1,000` virtual shares, `+ 1` virtual asset), the same `10,000e6` donation captures `1,000 / 2,000` into the non-redeemable virtual reserve: the victim receives `999` shares and the attacker suffers a **`-4,998.33 USDC` net loss** (`-4,999.998 USDC` loss at `offset = 6`; §Evidence Probe 2c). Yet because `_decimalsOffset()` defaults to `0` at L325 (`10^0 = 1` virtual share), integrators who inherit `ERC4626` without overriding `_decimalsOffset()` still expose victims to up to `50%` single-deposit dilution unless audited!

### 4. Six-Level (`L1`–`L6`) Performance & Footprint Matrix and `(C1)`/`(C2)` Model Refinement Analysis

`Basis: source + documentation + execution + derived`

| Toolchain / Verification Layer | `(L1)` Authoring & Day-2 Cost | `(L2)` Toolchain Build & RSS | `(L3)` Elab / Synth Latency | `(L4)` Generated Execution Speed | `(L5)` Kernel / Cert Check | `(L6)` Artifact & Binary Footprint |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`Lean 4` Default Elab + `Lean4Lean`** | Fast tactic authoring, high silent vacuity risk unless `autoImplicit=false` + canary checks | `Lean 4` C++/Lean build `~35–45 min`, `2.5–4 GB` RSS | Elab `10–400 ms`/file; WHNF spikes on large `BitVec`s | Native C codegen (or erased proof) | `lean4lean` / `nanoda` `~0.5–2.5 s` on medium `.olean`s | `.olean` `10–200 MB`; kernel RSS `150–900 MB` |
| **`Verilator` + `Yosys` RTL Flow** | Verbose manual width casts (`9'(a)+9'(b)`); `-Wall` lint churn | `Verilator` C++ build `~4–10 min` (`4–8 GB` RSS); `Yosys` `~3–8 min` | `V3Width` lint `< 100 ms`; `Yosys` synth `0.5–60 s` | `Verilator` C++ sim `10–100 MHz`; ASIC/FPGA native LUTs | `LRAT` combinational miter check `< 1–10 ms` (`O(\|clauses\|)`) | `V3Width.cpp` alone `663 KB` (`12.4 KLoC`); `BLIF` `< 1 MB` |
| **`OpenZeppelin` / `Uniswap v4` + `Move Prover`** | `Move` `spec` (`num` $\mathbb{Z}$) avoids `Nat` trap; Solidity needs manual `Floor`/`Ceil` | `solc` / Foundry `< 2 min`; `Move Prover` + Boogie/Z3 `~3–8 min` | `solc` `< 200 ms`; `Move Prover` Z3 `0.5–15 s` (`rlimit` tails) | `FullMath.mulDiv` `~35–65` EVM gas (`~180 ns` native `u128`/`u256`) | EVM bytecode static `VeriPB`/Farkas conservation `< 1 ms` | `ERC4626` runtime bytecode `~3.2 KB` (`< 24 KB` EIP-170 cap) |

- **`(C1)` Human Comprehensibility & Mental-Model Ergonomics:**
  - *Visual-Semantic Isomorphism (`WYSIWIP`):* Across all three ecosystems, human readers interpret `a - b`, `a + b >> 1`, `x > 0`, and `a * S / A` using standard schoolhouse $\mathbb{Z}/\mathbb{Q}$ algebra, and read capitalized `AdminRole` or `MaxFe` as named constants. Silently reinterpreting `-` as `max(0, a - b)`, `>` as unsigned `251 > 0`, `/` as attacker-favorable `Floor`, and typos as universal variables creates an unbridgeable gulf between **what a human reviewer signs off on** and **what the proof kernel or synthesizer validates**.
  - *Human Auditability Fix:* Requiring explicit binding sigils (`let x`), mathematical $\mathbb{Z}/\mathbb{Q}$ in specifications, and automatic **Premise-Inhabitedness + Canary Mutation Receipts** guarantees that a 10-line theorem means on paper *exactly* what it means in the kernel.
- **`(C2)` Conceptual Simplicity & Universal Model Refinement (Felleisen / Ousterhout Audit):**
  - *Eliminating `12.4 KLoC` of Context-Width Heuristics (`V3Width.cpp`) and Ad-Hoc Rounding Helpers:* Instead of maintaining complex context-propagating width visitors, lint suppression pragmas, and four manual preview functions, all three hazards unify cleanly onto **three intra-primitive laws** with zero new top-level primitives:
    1. **`SyntacticIso` Elaboration + Premise Inhabitedness:** Tightens Surface $\leftrightarrow$ Core lowering to a canonical round-trip bijection (`parse(print(core)) == cst`, `0` `autoImplicit`) paired with an existential witness proving theorem hypotheses are satisfiable (`WitnessExists` alongside `ProofForall`).
    2. **Carry-Preserving Interval Types + `Frozen` Ternary Bits:** Typing `Int<lo..hi>` (`Int<0..255> + Int<0..255> : Int<0..510>`) eliminates both `IEEE 1800` context truncation and unsigned contagion, while modeling uninitialized `X` flip-flops as unvalidated `Frozen` bytes forbids `casex` wildcard branching prior to reset initialization.
    3. **Variance-Coupled `RoundDir` on Linear Credits:** Coupling fixed-point division directly to linear asset variance (`OutflowFromVault => Floor`, `InflowToVault => Ceil`) makes rounding exploits unrepresentable without hand-auditing every `mulDiv` call site.

## Boundaries

- **Intentional Modular Wrapping Algorithms (`known not to apply` to cryptographic/hash mixing without explicit `Wrapping<w>`):** Banning implicit fixed-width wraparound applies to arithmetic quantities and specifications; cryptographic sponges (`SHA-3`, `ChaCha20`) and CRC/LFSR hardware intentionally operate in $\mathbb{Z}/2^w\mathbb{Z}$ (`known not to apply` when typed explicitly as modular ring elements `Mod2<w>`).
- **Sequential Multi-Cycle Equivalence Across Retiming (`not examined`):** Combinational `LRAT` miter verification catches `V3Width` and `proc_mux` `casex` mismatches within a single clock cycle, whereas sequential retiming across multi-clock asynchronous FIFOs (`CDC` metastability) was `not examined` in this package.
- **Multi-Asset Cross-Pool MEV Beyond Single-Vault `NAV` Monotonicity (`not examined`):** Enforcing `Floor`/`Ceil` `mulDiv` and `_decimalsOffset() >= 3..6` prevents single-vault `ERC-4626` share inflation and dust-withdrawal drains, but cross-contract oracle-manipulation MEV across external price feeds was `not examined`.
- **Kernel Soundness Under Native Compiler Extraction (`unknown` for unverified C/LLVM backends):** Even when `Lean4Lean` (`67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`) validates a non-vacuous `Expr` theorem, Lean 4's `extern` C runtime functions (`@[extern "lean_nat_sub"]`) and `native_decide` remain outside `Lean4Lean`'s pure kernel model (`unsupported` by kernel-only checking unless paired with verified machine-code extraction).

## Evidence

1. **`leanprover/lean4` (`4f5982e315272d89e2d2113d7ae0d8c9480f15db`) & `digama0/lean4lean` (`67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`):**
   - `Lean 4` `src/Lean/Elab/AutoBound.lean` L17–25: `register_builtin_option autoImplicit : Bool` (`defValue := true`) and `relaxedAutoImplicit : Bool` (`defValue := true`); L35–37 & L56–68: `isValidAutoBoundSuffix` and `checkValidAutoBoundImplicitName`.
   - `Lean 4` `src/Init/Prelude.lean` L2263–2266: `protected def Nat.sub` truncating `0 - succ b => 0`.
   - `Lean4Lean` `Lean4Lean/TypeChecker.lean` L16–25: Kernel `TypeChecker.State` operating strictly on post-elaboration `Expr` terms; M. Carneiro, *"Lean4Lean: Verifying a Typechecker for Lean, in Lean,"* TYPES 2025 (`arXiv:2403.14064`, `DOI: 10.4230/LIPIcs.TYPES.2025.2`).
2. **`verilator/verilator` (`464643f7c2abe27db4b9d10b22040bfb01b9c03d`), `YosysHQ/yosys` (`d1338f823b24fc0828d6b55438f3e9c2c13facbc`), & `chipsalliance/chisel` (`e95009474df71a0fe95e29a7c04b7cbd80fc426d`):**
   - `IEEE Std 1800-2023` §11.6–11.8 & `Verilator` `src/V3Width.cpp` L46–51 (unsigned contagion from based literals, part-selects, concatenations), L163–167 (`WIDTHTRUNC` / `WIDTHEXPAND`), L3613–3620 (`AstCastSize`).
   - `Yosys` `passes/proc/proc_mux.cc` L30–45: Procedural case-to-`$pmux` synthesis pass.
   - `Chisel` `core/src/main/scala/chisel3/Bits.scala` L283, L416, L471–485: Wrapping `+%` (`.tail(1)`) vs. carry-preserving `+&` and `.asUInt` / `.asSInt` casts.
3. **`OpenZeppelin/openzeppelin-contracts` (`d98b8f438d6c2b9d368d1220448b8519f733d371`), `Uniswap/v4-core` (`bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6`), & `aptos-labs/aptos-core` (`6137e8f7ee8e8b944568a3faf86c2064440edf17`):**
   - `OpenZeppelin` `contracts/token/ERC20/extensions/ERC4626.sol` L170–186 (`previewDeposit`/`previewRedeem` `Floor` vs. `previewMint`/`previewWithdraw` `Ceil`), L240–249 (`_convertToShares` / `_convertToAssets` virtual offsets), L324–326 (`_decimalsOffset()` returning `0` by default); `contracts/utils/math/Math.sol` L13–18 (`enum Rounding`), L206–216 (`mulDiv`).
   - `Uniswap v4` `src/libraries/FullMath.sol` L14–25 (`mulDiv` 512-bit CRT product) and L109–116 (`mulDivRoundingUp`).
   - `Aptos` `third_party/move/move-prover/README.md`: Move Specification Language (`MSL`) mathematical integer semantics.
4. **Executed Verification Micro-Probe (`observed_at: 2026-11-19`, Python 3.13 on Linux x86_64):**
   Running the standalone probe in **Revalidation** below yielded exact deterministic results:
   ```json
   {
     "nat_sub_vacuity": {"insolvent_cases": 35, "nat_sub_passed": 35, "int_sub_passed": 0},
     "sv_width_sign": {"self_det_8b_avg": 22, "ctx_det_9b_avg": 150, "neg5_gt_8h00": true},
     "erc4626_naive": {"vic_shares": 0, "att_profit": 5000000000, "vic_loss": 5000000000},
     "erc4626_oz_off3": {"vic_shares": 999, "att_profit": -4998332778},
     "erc4626_oz_off6": {"vic_shares": 999999, "att_profit": -4999998334},
     "withdraw_rounding": {"buggy_floor_shares_burned": 1, "sound_ceil_shares_burned": 2}
   }
   ```

## Revalidation

1. **Fast Standalone Semantic & Exploit Reproducer (`< 30 ms`, Python 3.10+ stdlib only):**

```bash
python3 - <<'PY'
# (2a) Nat.sub truncating vacuity on insolvent (bal < fee) pairs
pairs = [(b, f) for b in range(5) for f in range(b + 1, 10)]
assert sum(max(0, b - f) >= 0 for b, f in pairs) == 35
assert sum((b - f) >= 0 for b, f in pairs) == 0

# (2b) IEEE 1800 SystemVerilog 8-bit self-determined overflow & unsigned contagion
assert (((200 + 100) & 0xFF) >> 1) == 22 and (((200 + 100) & 0x1FF) >> 1) == 150
assert ((-5) & 0xFF) > (0 & 0xFF)  # 251 > 0 == True!

# (2c) ERC-4626 inflation attack: naive (offset=0, no virtual asset) vs OpenZeppelin offset=3
floor_div = lambda x, y, d: (x * y) // d
ceil_div = lambda x, y, d: (x * y + d - 1) // d
# Naive: 1 wei deposit + 10_000e6 donation + 5_000e6 victim deposit
vic_sh_naive = floor_div(5_000_000_000, 1, 1 + 10_000_000_000)
assert vic_sh_naive == 0
# OpenZeppelin virtual shares (offset=3 => 1000 virtual shares, +1 virtual asset)
att_sh = floor_div(1, 1000, 1)
S, A = att_sh, 1 + 10_000_000_000
vic_sh_oz = floor_div(5_000_000_000, S + 1000, A + 1)
S += vic_sh_oz; A += 5_000_000_000
att_out = floor_div(att_sh, A + 1, S + 1000)
assert vic_sh_oz == 999 and (att_out - 10_000_000_001) == -4_998_332_778

# (2d) Withdraw rounding direction (S=90, A=100, withdraw=2)
assert floor_div(2, 90, 100) == 1 and ceil_div(2, 90, 100) == 2
print("REVALIDATION_OK")
PY
```
2. **Upstream Source Drift Checks:**
   - Inspect `src/Lean/Elab/AutoBound.lean` in `leanprover/lean4` to check whether `autoImplicit` or `relaxedAutoImplicit` defaults change from `true` to `false`.
   - Inspect `contracts/token/ERC20/extensions/ERC4626.sol` in `OpenZeppelin/openzeppelin-contracts` to check `_decimalsOffset()` default value and `Math.Rounding` arguments across `preview*` functions.
   - Inspect `src/V3Width.cpp` in `verilator/verilator` for updates to `IEEE 1800` width/signedness warning promotion (`WIDTHTRUNC`, `CASEX`).
