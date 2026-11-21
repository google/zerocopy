# GMP Bitset LRAT Checkers, Init-Only Tseitin Bit-Blasting, and F2-Linear SIMD Certificates in Lean 4

## Summary

Lean `v4.34.1`'s built-in `bv_decide` tactic (`Std.Tactic.BVDecide`) cannot
directly discharge theorems under a strict three-axiom trust boundary
(`{propext, Classical.choice, Quot.sound}`) with `trustLevel := 0` private-level
kernel replay (`importModules ... (trustLevel := 0) (loadExts := false)
(level := .private)` + `toKernelEnv.replay`): every `bv_decide` proof emits a
per-goal `<thm>._native.bv_decide.ax_*` native-evaluation axiom backed by
`Lean.ofReduceBool`, and upstream `Std.Sat.AIG` / `CompactLRATChecker` rely on
`partial def`, `Std.HashMap`, and platform-opaque `USize` indexing that do not
reduce inside the standalone Lean kernel. At the same time, locked verification
hosts frequently ship without external `z3`, `cvc5`, `bitwuzla`, or standalone
`cadical` packages on `PATH`.

Direct source inspection and kernel-checked prototypes in Lean `v4.34.1`
(`leanprover/lean4` `5045d0056413266e57c625dcd7c365b10e377c52`) and Anneal's
Pass-1 audit boundary (`joshlf/anneal`
`c131b320eeeb26ef692e5afd5ec8db49ee518613`) establish five primary results:

1. **Zero-external-solver certificate harvesting from Lean `v4.34.1`'s bundled
   toolchain:** Even when `PATH` contains zero SAT/SMT binaries, the official
   Lean `v4.34.1` Linux `x86_64` toolchain ships a standalone `bin/cadical`
   (`2.1.2`) binary alongside `Lean.Meta.Tactic.BVDecide.External.satQuery` and
   in-process LRAT trimming (`LratCert.load` / `LRAT.trim`). An untrusted
   pre-pass can invoke these bundled facilities to export pure GMP-packed data
   witnesses `(AigArena, cnf, lrat)` that are verified inside a `prelude` +
   `Init.*`-only Lean `v4.34.1` module (`support/BvSimdTseitin.lean`, 3,063
   lines, `0` `sorry`, `12.96 s` compile, `1,356 ms` fresh private-level kernel
   replay) with zero native or custom axioms (`[Quot.sound, Classical.choice,
   propext]`), zero `partial`, zero `set_option`, and default `maxRecDepth =
   512`.
2. **Word-parallel C++ GMP `mpz_t` bitset RUP/LRAT checking + live-slot
   recycling (`250..15,000` steps):** Because Lean 4's C++ kernel (`reduce_nat`
   in `src/kernel/type_checker.cpp`) executes `Nat.land`, `Nat.lor`, `Nat.xor`,
   `Nat.shiftLeft`, and `Nat.shiftRight` directly over GMP `mpz_t` limbs,
   encoding the falsified-literal assignment and each clause as `Nat` bitmasks
   reduces arbitrary-width clause residual evaluation to a single limb-parallel
   `rem := Nat.xor mask (Nat.land mask falsified)`, unit detection to
   `Nat.land rem (Nat.sub rem 1) == 0`, and $\log_2$-free literal negation to a
   mod-3 parity test (`if rem % 3 == 1 then rem <<< 1 else rem >>> 1`, since
   $2^{2v} \equiv 1 \pmod 3$ and $2^{2v+1} \equiv 2 \pmod 3$). Combining GMP
   bitsets with live-interval clause-slot recycling inside a Peano-free 8-way
   `OctTrie` (`gmp_oct3_recycled`) verifies `250`, `1,000`, and `5,000` RUP
   steps in `0.94 s` (`849 ms` replay), `3.93 s` (`4,213 ms` replay), and
   `42.05 s` (`40,792 ms` replay)—`8.47x` faster than `Trie Bool` and `29.2x`
   faster than `List` at `250` steps, `7.61x` faster with `5.03x` lower RSS than
   `Trie Bool` at `1,000` steps, and succeeding at `5,000` steps where both
   `Trie Bool` and `List` time out—while compressing `.olean` certificates by
   `8.71x` relative to constructor ASTs (`24.9 KB` vs. `217.4 KB` at `N = 250`)
   and avoiding `Array` `maxRecDepth = 512` failures (`numVars = 1,024`) and
   `Array.set` bounds-proof blowups (`15.48 s` / `3.41 GB` RSS on just `25`
   steps at `numVars = 500`). At `15,000` RUP steps in a single `decide +kernel`
   goal, WHNF cache eviction (`m_whnf_core_cache`) and live `Expr` retention
   exceed a `180 s` single-file budget (`7.83 GB` RSS at `180 s`), establishing
   why multi-thousand-step SIMD VCs should decompose via lane congruence or
   lemma cuts rather than monolithic LRAT replay.
3. **LCNF `._unsafe_rec` synthesis vs. Pass-1 `ModuleData.constants` audits:**
   In Lean `v4.34.1`, any recursive computable `def` written with equation
   syntax—even structurally recursive `def f | 0 => ... | n + 1 => f n`—causes
   `Lean.Compiler` (LCNF) to emit a private `f._unsafe_rec` entry with
   `isPartial = true` inside `ModuleData.constants` (`44` such entries in
   `support/LratBench.lean`). `Lean.Kernel.Environment.replay`
   (`src/Lean/Replay.lean:180-183`) skips `isUnsafe || isPartial` constants
   because kernel proof terms reduce the structural `brecOn` body and never
   reference `f._unsafe_rec`, but strict module-inventory auditors such as
   Anneal's `validateRepoConstant` (`trusted/audit/TrustedBoundary.lean:1117-1153`)
   reject every `isUnsafe || isPartial` entry in `ModuleData.constants`.
   Writing computable loops directly via `@Nat.rec` (`support/Pass1GmpLrat.lean`)
   eliminates `100%` of `._unsafe_rec` constants (`lcnf_unsafe_rec = 0` across
   all `231` constants) and discharges up to `1,000` RUP steps via plain `rfl`
   (`14.47 s`, zero tactic configuration flags) before hitting the `200,000`-heartbeat
   `Meta.whnf` cap at `1,500` steps.
4. **Call-by-name kernel accumulation, real-solver hint fan-in, and SIMD lane
   congruence lifting:** Probing real CaDiCaL `2.1.2` LRAT proofs on 64-bit and
   256-bit VCs exposes three failure modes invisible on synthetic `6`-hint RUP
   microbenchmarks:
   - Single learned RUP steps in 64-bit `bzhi` / `sub` proofs reach `1,681`
     hints (`723` deletions in a single GC line), overflowing linear `List Nat`
     recursion at `maxRecDepth = 512` unless hints are balanced into
     `StepTree (List Nat)` (`≤ 16` IDs per leaf) and deletions are sliced.
   - In call-by-name `Kernel.whnf`, wrapping an accumulator in an identity
     helper `f (forceNode acc)` leaves an unreduced thunk; consecutive `.del`
     steps build lazy chains exceeding `maxRecDepth = 512` unless forced in
     continuation-passing style (`match acc with | .empty => k .empty | .node
     ... => k (.node ...)`).
   - Naive monolithic 256-bit bit-blasting of 16-lane AVX2 `VPADDSW`
     commutativity generates `10,545` AIG gates, `30,095` CNF clauses, and
     `76,306` LRAT actions (`3.12 MB` packed Lean source; `15.8 GB` RSS in a
     monolithic multi-VC module), whereas proving the 16-bit lane saturation VC
     via LRAT (`660` gates, `1,088` LRAT actions) and lifting across all 16
     lanes via a mechanized lane-congruence theorem (`simdMapBinary16_comm`)
     proves exact 256-bit `BitVec 256` commutativity in `36.70 s` (`30.53 s`
     replay, `24.2x` smaller source, `70.1x` fewer LRAT actions).
5. **$\mathbb{F}_2$-linear and $\mathbb{F}_2$-bilinear GMP unit-basis bypass for
   `pclmulqdq` and `vpshufb`:** On carryless multiplication (`clmulKaratsuba`
   vs. schoolbook `clmul`), CDCL SAT/LRAT explodes from `30,606` RUP steps at
   $w = 8$ to `365,898` RUP steps (`578,453` LRAT actions, `16.30 s` solve) at
   $w = 20$ and times out (`> 20 s`) at $w \ge 24$—and even unary 64-bit
   constant-polynomial CRC-64-ECMA folding (`0x42f0e1eba9ea3693`) times out in
   CaDiCaL (`> 20.2 s`). By contrast, a mechanized `prelude` + `Init.*`
   $\mathbb{F}_2$-linear / $\mathbb{F}_2$-bilinear GMP unit-basis evaluator
   (`support/F2BasisSimd.lean`, 966 lines, `0` `sorry`, axioms `[Quot.sound,
   propext]` with zero `Classical.choice` and zero native axioms) proves 64-bit
   unary CRC-64-ECMA folding in `1.03 s` (`10.7 KB` `.olean`), 128-bit 16-lane
   `vpshufb` $\mathrm{GF}(2^8)$ split-nibble multiplication in `6.10 s`
   (`10.9 KB` `.olean`), and full $64 \times 64 \to 128$-bit `pclmulqdq`
   Karatsuba equivalence across all $2^{128}$ input pairs (`4,096` basis pairs)
   in `36.42 s` (`24.9 KB` `.olean`).

## Applicability

These findings apply to kernel-checked bitvector, x86-64 status-flag, SWAR,
BMI2, and 128/256-bit SIMD verification in Lean `v4.34.1` under no-native-axiom
trust models:

- **Lean 4 kernel, compiler, and `BVDecide` stack:** `leanprover/lean4` commit
  `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`), verified under
  synchronous Pass-1 flags (`-DElab.async=false -Ddebug.skipKernelTC=false`),
  default `maxRecDepth = 512`, default `maxHeartbeats = 200000` (zero
  `set_option` overrides), and fresh private-level kernel replay
  (`importModules ... (trustLevel := 0) (loadExts := false) (level := .private)`
  followed by `baseEnv.setExporting false` and `baseEnv.toKernelEnv.replay`).
- **Bundled SAT solver artifact:** `lean-4.34.1-linux-x86_64/bin/lean`
  (SHA-256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`)
  and `lean-4.34.1-linux-x86_64/bin/cadical` (`CaDiCaL 2.1.2`, SHA-256
  `8e92f427cfb72072fc605ec6d5f641443c35921b29c39ab2f027776cd533afce`), tested on
  a Linux `7.1.6` `x86_64` host (`Intel Xeon @ 2.60 GHz`, 96 logical CPUs) where
  `z3`, `cvc5`, `cadical`, `bitwuzla`, `kissat`, `drat-trim`, and `lrat-trim`
  are all absent from `PATH`.
- **Anneal Pass-1 trust boundary:** `joshlf/anneal` commit
  `c131b320eeeb26ef692e5afd5ec8db49ee518613`, which enforces two distinct gates
  on `theory/` Lean modules that materially govern certificate design:
  1. `trusted/lean/foundation-lock.json` locks 51 `Init.*` modules (admitting
     `Init.Core`, `Init.Data.Nat.{Basic,Div.Basic,Bitwise.Basic}`,
     `Init.Data.BitVec.BasicAux`, `Init.Data.List.Basic`, and `Init.Tactics`,
     while currently excluding `Init.Data.BitVec.{Basic,Lemmas,Bitblast}`).
  2. `trusted/audit/TrustedBoundary.lean` (`allowedTheoryTacticKinds`, lines
     `152-206`, and `validateRepoConstant` / `ensureReplayableConstant`, lines
     `1117-1255`) rejects `decide` tactic configuration suffixes (`+kernel`,
     `+native`) at preflight and rejects any constant in `ModuleData.constants`
     marked `isUnsafe` or `isPartial`—including compiler-synthesized
     `._unsafe_rec` auxiliaries.

Accordingly, this report separates two exact library profiles:

1. **Strict 51-module `foundation-lock.json` profile (`support/Pass1GmpLrat.lean`):**
   Imports only 6 locked `Init.*` modules, uses direct `@Nat.rec` recursion so
   `ModuleData.constants` contains zero `isUnsafe`/`isPartial` entries
   (`lcnf_unsafe_rec = 0`), and supports both plain `rfl` (`[propext]` via
   `Init.Data.Nat.Div.Basic`, zero tactic configuration flags, scaling through
   `1,000` RUP steps in `14.47 s` under the `200,000`-heartbeat `Meta.whnf` cap)
   and `by decide +kernel` (`[propext]`, scaling to `5,000+` RUP steps per
   declaration).
2. **Full `prelude` + `Init.*` semantic `BitVec` profile
   (`support/BvSimdTseitin.lean`, `support/F2BasisSimd.lean`,
   `support/NonlinearSimdCanaries.lean`):** Imports only `Init.Data.BitVec.*`
   and `Init.Tactics` (`0` `Std.*` or `Lean.*` imports in verified modules, `0`
   `sorry`, `0` native/custom axioms), proving semantic `BitVec w` soundness
   theorems over `BitVec.getLsbD`, `BitVec.carry`, `BitVec.ult`, and
   `BitVec.slt` that require `Init.Data.BitVec.{Basic,Lemmas,Bitblast}` if
   admitted into a downstream `foundation-lock.json` manifest.

## Findings

### 1. Zero-External-Solver Certificate Harvesting from Lean `v4.34.1`

Basis: source + execution

In `leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`),
invoking `by bv_decide` on a 64-bit bitvector theorem (`swar_via_bv_decide`)
discharges the goal via `Lean.ofReduceBool` (`src/Lean/Elab/Tactic/BVDecide/`),
leaving a goal-specific native-evaluation axiom in `#print axioms`:

```text
'swar_via_bv_decide' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 swar_via_bv_decide._native.bv_decide.ax_1_5]
```

Any trust policy that restricts axioms to `{propext, Classical.choice,
Quot.sound}`—or replays `.olean` modules through `Lean.Kernel.Environment.replay`
with `trustLevel := 0` without compiled C++/IR native execution—rejects
`bv_decide` theorems. At the same time, standard kernel-safe tactics in Lean
`v4.34.1` fail on nonlinear 64-bit bitwise-arithmetic obligations such as
equivalence of Mycroft's SWAR zero-byte predicate
`((x - 0x0101010101010101#64) &&& ~~~x &&& 0x8080808080808080#64) != 0#64` and
the borrow-free SWAR predicate
`(~~~((((x &&& 0x7f7f7f7f7f7f7f7f#64) + 0x7f7f7f7f7f7f7f7f#64) ||| x) ||| 0x7f7f7f7f7f7f7f7f#64)) != 0#64`:

- `omega` and `bv_omega` fail immediately (`returncode = 1`: `omega could not
  prove the goal: No usable constraints found`, because bitwise `&&&`, `|||`,
  and `~~~` intertwined with 64-bit carry chains lie outside linear Presburger
  arithmetic).
- `grind` fails (`returncode = 1`, leaving an unresolved `BitVec 64` counter-goal
  after congruence and bitvector normalization).

However, inspecting the Lean `v4.34.1` toolchain sysroot reveals that zero
external solver installation is required to obtain trimmed LRAT certificates:

1. **Bundled `cadical` 2.1.2 binary:** Relative to `IO.appPath` (`.../bin/lean`),
   the toolchain ships `(← IO.appPath).parent.get! / "cadical"` (`CaDiCaL 2.1.2`),
   callable directly from an untrusted scratch Lean pre-pass via
   `Lean.Meta.Tactic.BVDecide.External.satQuery cadicalPath cnfPath lratPath
   timeoutSec true .proof`.
2. **Built-in LRAT parser and backward UNSAT-core trimmer:** Upstream
   `Lean.Meta.Tactic.BVDecide.LratCert.load lratPath true` parses the binary
   LRAT proof emitted by CaDiCaL and runs `LRAT.trim` in process, pruning dead
   learned clauses and exposing exact initial-clause hint references (`hints :
   Array Nat`) without `lrat-trim` or `drat-trim` on `PATH`.
3. **Pure data seam across the trust boundary:** Because the untrusted harvester
   emits only plain GMP integer trees (`StepTree Nat` decoded by
   `decodePackedAig`, `decodePackedInit`, and `decodePackedSteps`), neither
   `cadical`, `External.satQuery`, `Std.HashMap`, nor `LratCert.load` enters the
   verified theorem module's import graph or trusted computing base. Every
   certificate harvested across all 10 nonlinear 64-bit and 256-bit UNSAT VCs
   tested contained **zero RAT steps** (`lrat_rat = 0`), confirming that pure
   RUP (`addRup`, `del`, `addEmpty`) suffices for CaDiCaL `2.1.2` proofs over
   Tseitin-encoded bitvector and SIMD circuits when inprocessing features that
   emit RAT clauses are not required.

### 2. Word-Parallel C++ GMP Bitset RUP/LRAT Checkers vs. Trie, List, and Array Checkers

Basis: source + execution + derived

In `src/kernel/type_checker.cpp` (`reduce_nat`), Lean 4's kernel intercepts
closed `Nat` operations—including `Nat.land`, `Nat.lor`, `Nat.xor`,
`Nat.shiftLeft`, `Nat.shiftRight`, `Nat.sub`, `Nat.mod`, and `Nat.beq`—and
executes them natively in C++ GMP (`mpz_t`) limb arrays (`64` literal positions
per machine word) without unfolding recursive Lean definitions. By mapping
variable $v \ge 0$ to positive literal $2v$ (bit $2v$) and negative literal
$2v + 1$ (bit $2v + 1$), a clause $C$ compiles to $M_C = \bigvee_{\ell \in C}
(1 \lll \ell)$ and the set of currently falsified literals under RUP hypothesis
$\neg C_{\mathrm{target}}$ initializes to $F_0 = M_{C_{\mathrm{target}}}$. Each
unit-propagation hint `cid` then executes in $O(L/64)$ C++ word operations:

1. **Word-parallel residual mask:** `rem := Nat.xor mask (Nat.land mask
   falsified)` strips every falsified literal from `mask` in two GMP calls.
2. **Conflict and power-of-two unit detection:** `Nat.beq rem 0` detects an
   empty (falsified) clause in $O(1)$. Otherwise, `Nat.beq (Nat.land rem
   (Nat.sub rem 1)) 0` holds if and only if exactly one unassigned literal
   remains ($rem = 2^\ell$, proved sound in `BvSimdTseitin.single_bit_iff_pow2`).
3. **$\log_2$-free literal negation via mod-3 parity:** Extracting $\ell =
   \log_2(\mathrm{rem})$ in Lean would require $O(\log V)$ bit-search steps per
   unit propagation. Instead, because $2^{2v} = 4^v \equiv 1 \pmod 3$ and
   $2^{2v+1} = 2 \cdot 4^v \equiv 2 \pmod 3$, the negated literal bit
   $2^{\ell \oplus 1}$ is computed directly in GMP without recovering $\ell$:
   `negRaw := if Nat.beq (Nat.mod rem 3) 1 then Nat.shiftLeft rem 1 else
   Nat.shiftRight rem 1`, updating `falsified' := Nat.lor falsified negRaw`.

#### Architectural Micro-Structure: Peano Dispatch, Bit-Paging, and LCNF `._unsafe_rec`

Benchmarking six checker architectures (`support/Pass1GmpLrat.lean`,
`support/LratBench.lean`, and `support/lrat_scaling_results.json`) across a
500-variable sliding-window RUP derivation (`6–7` hints/step, periodic batch
deletions keeping `≤ 386` live clauses) exposed five kernel-evaluation rules:

1. **Peano `@Nat.casesOn` unwrapping vs. 3-bit `Bool.casesOn` in `OctTrie`:**
   Writing 8-way trie branch selection as `match rem with | 0 => ... | 1 => ...
   | 6 => ... | _ => ...` elaborates to **seven nested `@Nat.casesOn` Peano
   predecessor checks** on every trie level (`7.44 s` at `N = 1,000`; `69.55 s`
   at `N = 5,000`). Replacing Peano matching with a 3-level binary tree of
   `Nat.beq (Nat.land i 4) 0`, `Nat.beq (Nat.land i 2) 0`, and `Nat.beq
   (Nat.land i 1) 0` executes purely via C++ `reduce_nat` + `Bool.casesOn`,
   cutting `N = 1,000` compile time to **`3.93 s`** (`1.89x` faster) and
   `N = 5,000` to **`42.05 s`** (`1.65x` faster, `3,860 MB` RSS).
2. **Flat bit-paged GMP buckets (`GmpDb16`) vs. `@Nat.casesOn` limb-copy cost:**
   Packing multiple clause masks into 16 flat GMP integers (`GmpDb16`, stride
   `1,024` bits/slot, `~25` slots = `400` GMP limbs per bucket) eliminates tree
   traversal at `N = 250` (`1.31 s`, `279.3 MB` RSS—lowest memory of all
   checkers) and `N = 1,000` (`8.73 s`, `792.9 MB` RSS). However, forcing an
   updated `25,600`-bit bucket integer to a literal via `@Nat.casesOn x (k 0)
   (fun p => k (Nat.succ p))` copies `400` GMP limbs on `x - 1` and re-copies
   `400` limbs on `p + 1` at every subsequent hint lookup, causing `GmpDb16` to
   exceed `120 s` at `N = 5,000`. Keeping each clause in its own `OctTrie` leaf
   (`some mask`, `16` limbs) avoids cross-clause limb copying.
3. **LCNF `._unsafe_rec` elimination (`Pass1GmpLrat` vs. `LratBench`):**
   Equation-compiled `support/LratBench.lean` emits `527` kernel constants plus
   **`44` `._unsafe_rec` constants** (`isPartial = true`), whereas `@Nat.rec`-based
   `support/Pass1GmpLrat.lean` emits `231` kernel constants and **`0`
   `._unsafe_rec` constants** (`26 ms` library replay, `0` axioms `[]`), passing
   strict `ModuleData.constants` `isUnsafe || isPartial` audits.
4. **Constructor AST `.olean` bloat and `%[...|_]` elaborator failure vs. GMP
   stream packing:** Representing a `250`-step proof as a `StepTree LratStep`
   constructor AST produces a **`217,360 B` `.olean`** (`1.99 s` compile), and
   at `N = 1,000` (`85.1 KB` source, including a `63`-ID deletion list) Lean
   `v4.34.1` fails during elaboration (`error: elaboration function for
   '«term%[_|_]»' has not been implemented` when list-literal chunking triggers
   under `prelude` without `Init.Data.List.Notation` elaborators). Packing `8`
   LRAT steps per `u16` GMP integer leaf (`gmp_oct3_recycled`) shrinks the
   `N = 250` `.olean` by **`8.71x` (`24,944 B`)** and compiles cleanly at
   `N = 1,000` (`72,872 B` `.olean`) and `N = 5,000` (`330,280 B` `.olean`).
5. **`by rfl` (`Meta.whnf`) vs. `by decide +kernel` (`Kernel.whnf`):** Plain
   `rfl` avoids `decide +kernel` tactic flags and scales linearly from `N = 250`
   (`3.07 s`) through **`N = 1,000` (`14.47 s`, `1,021.6 MB` RSS, `3,688 ms`
   replay)** under default `maxHeartbeats = 200000`, before hitting
   `(deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has
   been reached` at `N = 1,500` (`21.95 s`). `Kernel.whnf` (`decide +kernel`) is
   not subject to `Meta` heartbeats and runs **`3.68x` faster** than `Meta.whnf`
   at `N = 1,000` (`3.93 s` vs. `14.47 s`):

| Tactic / Reducer | `N = 250` | `N = 500` | `N = 750` | `N = 1,000` | `N = 1,500` | Axiom Cone |
| --- | --- | --- | --- | --- | --- | --- |
| `rfl` (`Meta.whnf`, `0` tactic flags) | `3.07 s` (`328 MB`) | `6.79 s` (`551 MB`) | `10.64 s` (`788 MB`) | `14.47 s` (`1,022 MB`) | `FAIL` (`200k` heartbeats at `21.95 s`) | `[propext]` |
| `by decide +kernel` (`Kernel.whnf`) | `0.94 s` (`285 MB`) | — | — | `3.93 s` (`838 MB`) | Scales past `5,000` (`42.05 s`) | `[propext]` |

#### Cross-Architecture Scaling Matrix (`250`, `1,000`, `5,000`, `15,000` RUP Steps)

All rows below run under `lean -DElab.async=false -Ddebug.skipKernelTC=false`
with default `maxRecDepth = 512` and standalone fresh private-level
`toKernelEnv.replay`:

| Checker Architecture | `N = 250` (Compile / RSS / `.olean` / Replay) | `N = 1,000` (Compile / RSS / `.olean` / Replay) | `N = 5,000` (Compile / RSS / `.olean` / Replay) | `N = 15,000` |
| --- | --- | --- | --- | --- |
| `gmp_oct3_recycled` (`@Nat.rec`, `0` `_unsafe_rec`, `u16` recycled) | **`0.94 s`** / `285.0 MB` / `24.9 KB` / **`849 ms`** | **`3.93 s`** / `837.5 MB` / `72.9 KB` / **`4,213 ms`** | **`42.05 s`** / **`3,860.2 MB`** / **`330.3 KB`** / **`40,792 ms`** | `TIMEOUT > 180 s` (`7,829 MB` RSS at `180 s`) |
| `gmp_db16_bitpaged` (`@Nat.rec`, `0` `_unsafe_rec`, 16-bucket GMP) | `1.31 s` / **`279.3 MB`** / `25.1 KB` / `1,334 ms` | `8.73 s` / **`792.9 MB`** / `73.0 KB` / `8,958 ms` | `TIMEOUT > 120 s` (`400`-limb `@Nat.casesOn`) | `TIMEOUT > 120 s` |
| `gmp_quad8_unrecycled` (`QuadTrie`, monotonic IDs, `u32` stream) | `1.74 s` / `368.6 MB` / `32.9 KB` / `1,824 ms` | `7.84 s` / `1,222.5 MB` / `102.0 KB` / `8,933 ms` | `41.32 s` / `6,370.6 MB` / `472.5 KB` / `41,196 ms` | `TIMEOUT > 75 s` |
| `trie_bool_depth15` (`Trie Bool` assign + `Trie (List Nat)` DB) | `7.96 s` / `1,119.4 MB` / `33.7 KB` / `6,524 ms` | `29.89 s` / `4,216.9 MB` / `102.9 KB` / `28,603 ms` | `TIMEOUT > 60 s` | Skipped after `5,000` timeout |
| `list_assoc` (`List` association assign + clause DB) | `27.47 s` / `3,318.2 MB` / `33.6 KB` / `22,491 ms` | `TIMEOUT > 60 s` | Skipped after `1,000` timeout | Skipped |
| `array_flat` (`Array` flat indexing, `if h : idx < arr.size`) | Fails / blows up: at `numVars = 1,024` (`N = 5`), **`FAIL` (`0.39 s`)**: `(kernel) application type mismatch` (`mkZeroArray` exceeds `maxRecDepth = 512`); at `numVars = 500` (`N = 25`), **`15.48 s` / `3,414.6 MB` RSS** (`16,677 ms` replay); at `N = 250`, `TIMEOUT > 35 s` | — | — | — |

Two scaling boundaries stand out:

- **Why `Array` fails in the Lean kernel:** Flat `Array` indexing inside
  `Kernel.whnf` suffers a double failure: initializing `mkZeroArray 1024 []`
  exceeds `maxRecDepth = 512` (`application type mismatch` on `Eq.refl true`),
  and even below the recursion cap (`numVars = 500`, `N = 25` steps), dependent
  `arr.set idx v h` constructs symbolic kernel inequality proof terms on every
  unit propagation, consuming **`3.41 GB` RSS for just `25` RUP steps** (`>160x`
  slower than `gmp_oct3_recycled`).
- **Why single-goal `decide +kernel` bends upward between `1,000` and `15,000`
  steps:** Between `N = 250` (`3.76 ms/step`) and `N = 1,000` (`3.93 ms/step`),
  `gmp_oct3_recycled` scales linearly. Between `1,000` and `5,000` steps, per-step
  time doubles to `8.41 ms/step` (`3.86 GB` RSS), and at `15,000` steps a single
  monolithic `decide +kernel` invocation exceeds `180 s` (`7.83 GB` RSS; shrinking
  leaf chunks from `8` steps to `2` or `1` steps/leaf at `N = 5,000` worsens
  wall time from `42.05 s` to `85.00 s` / `89.08 s` and bloats `.olean` size from
  `330 KB` to `1.49 MB`). Once live kernel `Expr` nodes exceed `m_whnf_core_cache`
  (`8,192` entries) and accumulate uncollected `OctTrie` spine allocations inside
  one `is_def_eq` call, per-step WHNF cost grows superlinearly—directly motivating
  per-lane congruence lifting (`§3`) and algebraic basis bypasses (`§4`) over
  multi-ten-thousand-step monolithic LRAT certificates.

### 3. Kernel-Reducible `Init`-Only `BitVec` and SIMD-Lane Tseitin Bit-Blaster

Basis: source + execution + derived

To eliminate `Std.Sat.AIG` (`Std.HashMap` / `USize` opacity and `partial`
algorithms) while keeping circuit DAG sharing across multi-use subexpressions,
`support/BvSimdTseitin.lean` (3,063 lines, `prelude` + `Init.Data.BitVec.{Basic,
Lemmas,Bitblast}` + `Init.Tactics`, `0` `sorry`) separates **untrusted DAG
construction** from **self-verifying kernel gate lookup**:

1. **Zero-trust `AigArena` directories (`lookupAtom_sound`, `lookupAnd_sound`):**
   An `AigArena` stores `maxGate : Nat`, `nodes : OctTrie AigNode`, and two
   read-only `OctTrie Nat` hint directories (`atomDir` keyed by
   `(w <<< 15) ||| (v <<< 9) ||| b` and `gateDir` keyed by canonical ordered
   literal pair `(min l1 l2 <<< 16) ||| max l1 l2`, read at `OctTrie` fuel `11`
   covering $8^{10} = 2^{30}$ keys). Neither `atomDir` nor `gateDir` is trusted:
   `lookupAtom` and `lookupAnd` fetch candidate gate ID `g` from the directory
   and then verify in `nodes` that `g < maxGate`, that node `g` actually stores
   `.atom w v b` (or `.andGate a b` matching `{l1, l2}`), and—crucially for DAG
   acyclicity without a separate topological-sort pass—that every fan-in literal
   satisfies `(a >>> 1) < g` and `(b >>> 1) < g`. Because strictly decreasing
   gate indices well-order the arena, the semantic evaluator `aigAssignUpTo`
   proves gate-evaluation stability (`aigAssignUpTo_lt`) by plain structural
   induction on `maxGate`.
2. **UNSAT-core Tseitin CNF verification (`checkTseitinCnfTree_sound`):**
   Rather than generating all $3G + 2$ Tseitin clauses inside the kernel,
   `checkTseitinClause` verifies that each clause present in the certificate's
   `cnf : StepTree (Nat × List Nat)` is locally entailed by `nodes` under
   `evalLit σ rootLit = true` (either `[rootLit]`, `[2*g + 1]` for `.constFalse`,
   `[2*g + 1, l_i]`, or `[2*g, l_1 ^^^ 1, l_2 ^^^ 1]` for `.andGate l_1 l_2`).
   Consequently, the untrusted harvester filters initial CNF clauses down to
   `usedInit`—the subset referenced in `LratCert.load`'s trimmed proof hints. On
   multi-lane SIMD obligations where only a subset of lanes participates in the
   UNSAT core (such as `ssse3_vpmaddubsw_64_lane_and_sat`), UNSAT-core filtering
   prunes `35,822` total Tseitin clauses down to `1,630` checked clauses (`95.4%`
   reduction) with zero loss of soundness.
3. **Complete bitvector, x86-64 flag, BMI2, and SIMD operator suite
   (`checkBvUnsatCert_sound`):** `BvExpr w` and `BvPred` mechanize arbitrary-width
   `var`, `const`, `not`, `and`, `or`, `xor`, ripple-carry `add` (`blastAdcAux`
   proved against `BitVec.carry` and `BitVec.getLsbD_add_add_bool`), two's
   complement `neg` and `sub`, constant shifts (`shlConst`, `lshrConst`,
   `ashrConst`), `extract`, `concat`, `zeroExtend`, `signExtend`, `ite` muxes,
   shift-add `mul`, `eq`, unsigned `ult` (`!carryOut` of `x + ~y + 1`), signed
   `slt` (`!(msb x ^^ msb y) ^^ carryOut`), x86-64 `SUB`/`CMP` status flags
   (`CF`, `ZF`, `SF`, `OF`, `PF`), BMI2 (`BLSI`, `BLSR`, `BLSMSK`, 64-bit
   barrel-shifted `BZHI`), 4-pair 64-bit nonlinear `VPMADDUBSW` (`u8 * i8`
   20-bit signed-clamped multiply-accumulate), and $N$-lane `VPADDSW` (`i16`
   signed-saturating addition), culminating in:

```lean
theorem checkBvUnsatCert_sound
    (expr : BvPred) (aig : AigArena)
    (cnf : StepTree (Nat × List Nat)) (lrat : StepTree LratStep)
    (env : BvEnv) :
    checkBvUnsatCert expr aig cnf lrat = true →
    evalBv expr env = false
```

   Compiling `BvSimdTseitin.lean` under `-DElab.async=false
   -Ddebug.skipKernelTC=false` takes `12.96 s` wall (`470.74 MB` RSS, `7.46 MB`
   `.olean`), and fresh private-level kernel replay verifies all `1,007` kernel
   declarations in `1,356 ms` with transitive axioms `[Quot.sound,
   Classical.choice, propext]`.

#### Real-Target Probing: Four Scaling & Semantic Traps on 64-Bit and 256-Bit VCs

Testing `BvSimdTseitin` against real CaDiCaL `2.1.2` proofs across 11 bitvector
and SIMD VCs (`support/nonlinear_vc_results.json`) exposed four phenomena that do
not appear on small synthetic CNF benchmarks:

1. **SWAR byte-mask non-equivalence vs. boolean zero-byte equivalence:**
   64-bit Mycroft `((x - 0x0101..01) & ~x & 0x8080..80)` and borrow-free
   `~(((x & 0x7f7f..7f) + 0x7f7f..7f) | x | 0x7f7f..7f)` are **not** equal as
   `BitVec 64` masks (`swar_mask_non_eq_sat_probe` returns `SAT` in `141 ms`: at
   `x = 0x0100`, byte `0` is zero and its subtraction borrow clears byte `1`'s
   high bit in Mycroft's mask while borrow-free isolates each byte), whereas
   boolean `has_zero_byte` equivalence (`(mask != 0#64) = (mask' != 0#64)`) is
   universally `UNSAT` (`719` AIG gates, `672` core clauses, `94` RUP steps, `0`
   RAT steps) and yields the semantic corollary
   `mycroft_has_zero_byte_eq_borrow_free : ∀ x : BitVec 64, ...` (`14.64 s`
   compile, `14,724 ms` kernel replay, `0` `._unsafe_rec`).
2. **Real-solver hint fan-in (`1,681` hints/step) vs. `maxRecDepth = 512`:**
   On 64-bit `bmi2_bzhi64_comp` and `x86_sub_{signed,unsigned}_64`, CaDiCaL
   `2.1.2` emits single RUP steps with up to **`1,681` unit-propagation hints**
   and single deletion lines with up to **`723` clause IDs** (`802` hints and
   `556` deletions on `bmi2_blsi_blsr_64`). A linear `List Nat` hint propagator
   or `u16` list decoder immediately crashes in `Kernel.whnf` with `(kernel)
   deep recursion detected` at default `maxRecDepth = 512`. Representing clauses
   and hints as balanced binary `StepTree (List Nat)` with `≤ 16` literals/IDs
   per leaf (`propagateGmpTree`) and slicing `.del` steps to `≤ 16` IDs caps
   per-step kernel stack depth below `30` frames regardless of hint count.
3. **`OctTrie` fuel off-by-one (`8^(d-1)` vs. `8^d`) and `brecOn` kernel cost:**
   Because `OctTrie.get` / `OctTrie.set` consume one unit of `fuel` at the
   `idx = 0` leaf check after shifting by 3 bits per level, `fuel = d` addresses
   indices `< 8^(d - 1)` (`< 4,096` at `d = 5`, `< 32,768` at `d = 6`). VCs
   whose recycled clause slots stay below `4,096` (`swar_has_zero_byte_64` at
   `673`, `x86_xor_pf_64` at `312`, `vpaddsw_lane16_comm_and_sat` at `1,606`)
   succeed at `aDepth = 5`, whereas `bmi2_blsi_blsr_64` (`max_recycled_slot =
   4,711`) overflows `8^4 = 4,096` at `aDepth = 5` (`lratOk = false`) and larger
   64-bit arithmetic VCs (`6,504` slots, `14,958` LRAT actions) exceed a `75 s`
   per-VC budget under `BvSimdTseitin`'s equation-compiled `brecOn` `OctTrie`
   (`~10x` slower per RUP step than `Pass1GmpLrat`'s Peano-free `@Nat.rec`
   stream kernel).
4. **Monolithic 256-bit SIMD bit-blasting vs. 16-bit lane LRAT + congruence
   lifting:** Bit-blasting 256-bit 16-lane AVX2 `VPADDSW` commutativity
   monolithically (`avx2_vpaddsw_256_monolithic_probe`) produces `10,545` AIG
   gates, `30,095` total CNF clauses (`25,534` core), and **`76,306` LRAT
   actions** (`39,414` RUP + `36,891` deletions, `3.12 MB` packed Lean source;
   combining 9 VCs in one monolithic `7.14 MB` packed / `23.1 MB` raw-AST file
   drives Lean's elaborator to `15.8 GB` RSS and `> 12 min` wall time). Instead,
   proving the 16-bit lane VC (`vpaddsw_lane16_comm_and_sat`: `660` gates,
   `1,603` core clauses, `603` RUP steps, `128.9 KB` source, `36.70 s` compile,
   `30,533 ms` replay) and lifting across all 16 lanes via `simdMapBinary16_comm`
   + `evalBvExpr_simdVpaddsw` proves exact 256-bit `BitVec 256` AVX2
   commutativity (`avx2_vpaddsw256_comm_semantic` and `avx2_vpaddsw256_eval_comm`
   in `support/NonlinearSimdCanaries.lean`, `174.0 KB` total, `37.91 s` compile,
   `40,197 ms` replay) with **`24.2x` smaller source** and **`70.1x` fewer LRAT
   actions**:

| Verification Obligation | Width / Lanes | AIG Gates | CNF Clauses (Total / Core) | CaDiCaL + Trim (`ms`) | Trimmed LRAT (Total / RUP / RAT) | Max Slot | Packed Cert (`KB`) | Lean Compile / Replay |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `swar_mask_non_eq_sat_probe` | `64`-bit | `733` | `2,003` / — | `141` | `SAT` counterexample (`x = 0x0100`) | — | — | Counterexample found |
| `swar_has_zero_byte_64` (+ semantic eq) | `64`-bit (8B SWAR) | `719` | `1,961` / `672` | `92 + 1` | `189` / `94` / `0` | `673` | `42.5` | `14.64 s` / `14.72 s` |
| `x86_xor_pf_64` (`PF(x ^ y) = !(PF x ^ PF y)`) | `64`-bit flags | `391` | `785` / `276` | `79 + 2` | `703` / `430` / `0` | `312` | `72.8` | `14.96 s` / `12.18 s` |
| `vpaddsw_lane16` + lifted **256-bit AVX2** `VPADDSW` | `16`-bit $\to$ `256`-bit (`16` lanes) | `660` | `1,880` / `1,603` | `152 + 2` | `1,088` / `603` / `0` | `1,606` | `124.4` | `36.70 s` / `30.53 s` |
| `avx2_vpaddsw_256_monolithic_probe` (naive) | `256`-bit monolithic | `10,545` | `30,095` / `25,534` | `696 + 112` | `76,306` / `39,414` / `0` | `25,559` | `3,047.3` | Avoided (`15.8 GB` RSS in mono file) |
| `bmi2_blsmsk_64` / `blsi_blsr_64` / `bzhi64` | `64`-bit BMI2 | `1,451–2,823` | `4,157–7,889` / `2,766–6,478` | `150–215 + 1–18` | `659–4,701` / `329–2,575` / `0` | `2,767–6,504` | `180.7–1,499.3` | Harvested (`0` RAT; needs `@Nat.rec` + `d=6`) |
| `ssse3_vpmaddubsw_64_lane_and_sat` | `64`-bit (`4` pairs, `u8*i8`) | `12,070` | `35,822` / `1,630` | `141 + 3` | `1,283` / `742` / `0` | `1,654` | `465.7` | Harvested (`95.4%` CNF core trim) |

### 4. $\mathbb{F}_2$-Linear and $\mathbb{F}_2$-Bilinear GMP Unit-Basis Bypass for `pclmulqdq` and `vpshufb`

Basis: source + execution + derived

Carryless polynomial multiplication (`PCLMULQDQ` for CRC folding and AES-GCM
`GHASH`) and split-nibble SIMD Galois-field table lookups (`VPSHUFB` for
$\mathrm{GF}(2^8)$ Reed-Solomon / AES `MixColumns`) are built out of deep XOR
parity trees over $\mathbb{F}_2$. Because Tseitin parity networks have high
resolution width in CDCL SAT solvers, bit-blasting `clmulKaratsuba` vs.
schoolbook `clmul` in upstream `Std.Tactic.BVDecide` + bundled CaDiCaL `2.1.2`
scales exponentially and stalls well below 64 bits (`support/f2_vs_sat_crossover.json`).

`support/F2BasisSimd.lean` (966 lines, `prelude` + `Init.Data.BitVec.{Basic,
Lemmas}` + `Init.Tactics`, `0` `sorry`) bypasses SAT/LRAT completely by
mechanizing finite-dimensional $\mathbb{F}_2$-vector-space basis reduction
directly in Lean's GMP kernel:

1. **Unary $\mathbb{F}_2$-linear basis theorem (`checkF2Linear1_sound`):** Every
   $x \in \mathrm{BitVec}\;w$ decomposes into the XOR sum of its set unit-basis
   vectors `bvBasisPrefix x w = x` (`1#w <<< k` for $0 \le k < w$). Any two
   operators $f, g : \mathrm{BitVec}\;w_{\mathrm{in}} \to
   \mathrm{BitVec}\;w_{\mathrm{out}}$ satisfying `IsF2Linear1` (`f 0 = 0` and
   `f (a ^^^ b) = f a ^^^ f b`) are universally equal (`∀ x, f x = g x`) if and
   only if `checkF2Linear1 f g = true`, which checks `f (1 <<< k) == g (1 <<< k)`
   for $0 \le k < w_{\mathrm{in}}$ (`w_in` concrete GMP evaluations).
2. **Two-pass $\mathbb{F}_2$-bilinear basis theorem (`checkF2Bilinear_sound`):**
   For bilinear operators $B_1, B_2 : \mathrm{BitVec}\;w_1 \to
   \mathrm{BitVec}\;w_2 \to \mathrm{BitVec}\;w_{\mathrm{out}}$ (`IsF2Bilinear`:
   linear in `x` for each fixed `y` and linear in `y` for each fixed `x`, proved
   structurally for both `clmul` and `clmulKaratsuba64`), fixing basis vector
   $e_i = 1 \lll i$ yields unary $\mathbb{F}_2$-linear maps $y \mapsto B_1\,e_i\,y$
   and $y \mapsto B_2\,e_i\,y$ agreed on all $e_j = 1 \lll j$ ($w_1 \cdot w_2$
   GMP evaluations), and a second application of `checkF2Linear1_sound` lifts
   pointwise agreement on $e_i$ to all $x, y$.
3. **128-bit `vpshufb` linearity certificate (`gf256SimdVpshufb128_isLinear`):**
   For a dynamic `src` and constant `ctrl`, `src ↦ vpshufb128 src ctrl` is
   unconditionally $\mathbb{F}_2$-linear (`vpshufb128_constCtrl_isLinear`). When
   the data vector `v : BitVec 128` drives the 4-bit shuffle indices of constant
   16-byte tables `lutLo, lutHi : BitVec 128` (`vpshufb128 lutLo (v & 0x0f..0f)
   ^^^ vpshufb128 lutHi ((v >>> 4) & 0x0f..0f)`), the map is $\mathbb{F}_2$-linear
   whenever each 16-entry table satisfies the 256-pair boolean check
   `checkLut16Linear lut = true` (`lut[0] == 0` and `lut[a ^ b] == lut[a] ^ lut[b]`
   for $a, b < 16$). Discharging `checkLut16Linear` and the 128 unit-basis
   vectors via `by decide +kernel` proves 16-lane $\mathrm{GF}(2^8)$
   split-nibble multiplication equivalence (`vpshufb128_gf256_mul_0x9d_eq`) over
   all $2^{128}$ XMM register states in `6.10 s`.
4. **Strict two-axiom footprint (`{propext, Quot.sound}`):** Unlike
   `BvSimdTseitin` (where `omega` inside helper arithmetic proofs pulls in
   `Classical.choice`), all six exported theorems in `F2BasisSimd.lean`
   (`checkF2Linear1_sound`, `checkF2Bilinear_sound`,
   `pclmulqdq64_karatsuba_eq_schoolbook`, `pclmulqdq64_comm`,
   `vpshufb128_gf256_mul_0x9d_eq`, and
   `crc64_ecma_pclmulqdq_karatsuba_eq_schoolbook`) depend exclusively on
   `[Quot.sound, propext]` (`0` `Classical.choice`, `0` native axioms), verified
   by standalone fresh private-level kernel replay (`50,482 ms` total replay
   across all four 64/128-bit SIMD/crypto theorems; `1.85 MB` `.olean`).

#### Empirical Crossover: CDCL SAT/LRAT vs. $\mathbb{F}_2$ GMP Unit-Basis (`w = 8..64`)

| Task / Bit Width `w` | SAT AIG Gates | SAT CNF Clauses | CaDiCaL `2.1.2` + Trim | Trimmed LRAT Actions (RUP) | $\mathbb{F}_2$ Basis Evals | $\mathbb{F}_2$ Lean Compile (`-DElab.async=false`) | $\mathbb{F}_2$ Peak RSS | $\mathbb{F}_2$ `.olean` Size |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Bilinear `clmul` Karatsuba (`w = 8`) | `400` | `1,182` | `0.91 s + 0.17 s` | `47,634` (`30,606`) | `64` | **`0.30 s`** | `281.4 MB` | `24,872 B` |
| Bilinear `clmul` Karatsuba (`w = 12`) | `878` | `2,608` | `1.78 s + 0.21 s` | `65,951` (`41,270`) | `144` | **`0.51 s`** | `309.5 MB` | `24,872 B` |
| Bilinear `clmul` Karatsuba (`w = 16`) | `1,540` | `4,586` | `6.50 s + 1.08 s` | `310,209` (`196,876`) | `256` | **`0.90 s`** | `358.7 MB` | `24,888 B` |
| Bilinear `clmul` Karatsuba (`w = 20`) | `2,386` | `7,116` | `16.30 s + 2.13 s` | `578,453` (`365,898`) | `400` | **`1.50 s`** | `443.6 MB` | `24,888 B` |
| Bilinear `clmul` Karatsuba (`w = 24`) | `3,416` | `10,198` | **`TIMEOUT > 20.28 s`** | — | `576` | **`2.81 s`** | `556.8 MB` | `24,888 B` |
| Bilinear `clmul` Karatsuba (`w = 32`) | `6,028` | `18,018` | Skipped after `w=24` timeout | — | `1,024` | **`6.39 s`** | `948.4 MB` | `24,904 B` |
| Bilinear `pclmulqdq` Karatsuba (`w = 64`) | `23,836` | `71,378` | Skipped after `w=24` timeout | — | `4,096` | **`36.42 s`** | `5,110.4 MB` | `24,920 B` |
| Unary CRC-64-ECMA `clmul x 0x42f0..93` (`w = 64`) | `9,388` | `28,098` | **`TIMEOUT > 20.21 s`** | — | `64` | **`1.03 s`** | `371.9 MB` | `10,656 B` |
| Unary 128-bit 16-lane `vpshufb` $\mathrm{GF}(2^8)$ `0x9d` | — | — | Bypassed via $\mathbb{F}_2$ LUT check | — | `256` LUT + `128` | **`6.10 s`** | `791.4 MB` | `10,896 B` |

Even at $w = 8$, $\mathbb{F}_2$-bilinear GMP evaluation (`0.30 s` total Lean
compile + kernel check) is already **`3.6x` faster** than CaDiCaL solve + LRAT
trim alone (`1.09 s`, before checking `30,606` RUP steps in the kernel). By
$w = 20$, SAT generates `578,453` LRAT actions (`18.43 s` solve+trim) vs.
`1.50 s` in GMP; at $w \ge 24$ (and even for unary 64-bit constant-polynomial
CRC-64 folding), CDCL SAT times out while $\mathbb{F}_2$ GMP basis evaluation
produces a constant `10.7–24.9 KB` `.olean` certificate.

## Boundaries

- **RAT steps (`addRat` / Extended Resolution) in LRAT proofs — unsupported in
  current mechanized checkers (`known not to apply` if aggressive CaDiCaL RAT
  inprocessing triggers):** Both `Pass1GmpLrat.lean` and `BvSimdTseitin.lean`
  verify pure RUP (`addRup`), deletion (`del`), and final conflict (`addEmpty`)
  steps, rejecting `addRat` in the harvester (`lrat_rat = 0` across all 10
  nonlinear and SIMD VCs tested). If a future CaDiCaL configuration emits
  blocked-clause or bounded-variable-addition RAT steps, either disable RAT
  generation in CaDiCaL (`--no-elim` / `--lrat`) or extend `stepGmp` with the
  nested resolution-candidate loop over clauses containing the negated pivot
  literal.
- **Monolithic single-goal LRAT replay beyond `~5,000–10,000` RUP steps —
  `known not to apply` within a `180 s` per-file budget:** While `gmp_oct3_recycled`
  verifies `5,000` RUP steps in `42.05 s` (`3.86 GB` RSS), a single `15,000`-step
  `decide +kernel` invocation exceeds `180 s` (`7.83 GB` RSS) due to
  `m_whnf_core_cache` eviction and live `Expr` spine retention. Multi-lane SIMD
  or wide arithmetic VCs generating `> 10,000` LRAT steps should be decomposed
  via lane-congruence lemmas (`simdMapBinary16_comm`) or intermediate cutpoint
  lemmas rather than replayed as a single monolithic LRAT stream.
- **Variable-width arithmetic / division (`udiv`, `umod`, `sdiv`, `srem`) and
  floating-point IEEE-754 operations — `not examined` / `unsupported`:**
  `BvSimdTseitin.lean` mechanizes bitwise, shift-by-constant, barrel shift
  (`shlPow2`), ripple-carry `add`/`sub`/`neg`, shift-add `mul`, `extract`,
  `concat`, `zeroExtend`, `signExtend`, `ite`, comparisons (`eq`, `ult`, `slt`),
  x86 flags, BMI2, and saturating SIMD combinators; restoring division/remainder
  and IEEE-754 floating-point circuits were **not examined**.
- **64-bit integer multiplication equivalence (`x * y` vs. Karatsuba integer
  multiply) — `known not to apply` to both $\mathbb{F}_2$-bilinear basis and
  CDCL SAT:** Integer multiplication with carries is **not** $\mathbb{F}_2$-bilinear
  (`(a ^^^ b) * y ≠ (a * y) ^^^ (b * y)` because carries are nonlinear over
  $\mathbb{F}_2$), so `checkF2Bilinear_sound` **known not to apply** to standard
  `MUL`/`IMUL`; simultaneously, CDCL SAT bit-blasting is well-known to stall on
  64-bit multiplier equivalence without algebraic Gröbner-basis / ring-normalization
  certificates.
- **Anneal's current 51-module `foundation-lock.json` vs. full `Init.Data.BitVec`
  lemmas — scope boundary:** At `joshlf/anneal`
  `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Pass1GmpLrat.lean` compiles
  strictly within the locked 51 `Init.*` modules (`lcnf_unsafe_rec = 0`) and
  proves propositional UNSAT certificates via `rfl` through `1,000` RUP steps
  (`14.47 s`; `known not to apply` at `≥ 1,500` RUP steps via `rfl` under the
  `200,000`-heartbeat `Meta.whnf` cap without either `decide +kernel` or
  cross-declaration state splitting). Importing `BvSimdTseitin.lean` or
  `F2BasisSimd.lean` directly into Anneal's `theory/` tree requires admitting
  `Init.Data.BitVec.{Basic,Lemmas,Bitblast}` into `foundation-lock.json` (and
  admitting `decide +kernel` or splitting `rfl` checkpoints every `≤ 1,000`
  steps) plus rewriting recursive helpers in `@Nat.rec` form to eliminate LCNF
  `._unsafe_rec` entries.
- **Non-Linux or non-`x86_64` Lean `v4.34.1` binary distributions — `not
  examined`:** Presence and behavior of bundled `bin/cadical` were verified on
  `lean-4.34.1-linux-x86_64` (`CaDiCaL 2.1.2`); macOS (`darwin-aarch64`) and
  Windows (`windows-x86_64`) toolchain archives were **not examined**.

## Evidence

All experiments were executed on **2026-11-21** on Linux `7.1.6` `x86_64`
(`Intel(R) Xeon(R) CPU @ 2.60GHz`, 96 logical CPUs) inside bounded cgroup v2
scopes (`MemorySwapMax=0`) using Lean `v4.34.1` with synchronous kernel flags
`-DElab.async=false -Ddebug.skipKernelTC=false` and verified via standalone fresh
private-level kernel replay (`importModules ... (trustLevel := 0)
(loadExts := false) (level := .private)` + `baseEnv.setExporting false` +
`baseEnv.toKernelEnv.replay`).

### Primary Upstream Sources

1. **Lean 4 kernel `Nat`/GMP reduction, WHNF cache, recursion limit, and replay
   (`leanprover/lean4` `5045d0056413266e57c625dcd7c365b10e377c52`):**
   - `src/kernel/type_checker.cpp`: `reduce_nat` dispatches `Nat.add`,
     `Nat.sub`, `Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.land`, `Nat.lor`,
     `Nat.xor`, `Nat.shiftLeft`, `Nat.shiftRight`, `Nat.beq`, and `Nat.ble` to
     C++ `mpz` (`nat_lit_ext`) arithmetic; `whnf_core` uses fixed-size direct
     caching (`m_whnf_core_cache`) and `check_max_rec_depth` (`maxRecDepth =
     512` default).
   - `src/Lean/Replay.lean:180-183`: `Environment.replay` explicitly skips
     `if ci.isUnsafe || ci.isPartial then continue` before replaying kernel
     constants, explaining why `._unsafe_rec` LCNF entries pass `Replay.lean`
     yet fail `ModuleData.constants` sweeps that reject `ci.isPartial`.
   - `src/Lean/Elab/Tactic/BVDecide/` and `src/Std/Tactic/BVDecide/`:
     `External.satQuery` invokes `cadical` in binary LRAT mode; `LratCert.load`
     parses and trims LRAT proofs via `LRAT.trim`; `bv_decide` emits
     `Lean.ofReduceBool` auxiliary axioms `<thm>._native.bv_decide.ax_*`.
2. **Bundled toolchain binaries (`lean-4.34.1-linux-x86_64`):**
   - `bin/lean`: SHA-256
     `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
   - `bin/cadical` (`version 2.1.2`): SHA-256
     `8e92f427cfb72072fc605ec6d5f641443c35921b29c39ab2f027776cd533afce`.
3. **Anneal Pass-1 audit boundary (`joshlf/anneal`
   `c131b320eeeb26ef692e5afd5ec8db49ee518613`):**
   - `trusted/lean/foundation-lock.json`: 51 locked `Init.*` module digests and
     3-axiom allowlist `["Classical.choice", "Quot.sound", "propext"]`.
   - `trusted/audit/TrustedBoundary.lean:152-206` (`allowedTheoryTacticKinds`)
     and `1117-1255` (`collectRepoModuleConstants`, `validateRepoConstant`,
     `ensureReplayableConstant` rejecting `ci.isUnsafe || ci.isPartial`).
   - `theory/Anneal/PureLift/PermTree.lean`: direct `@Nat.rec` structural
     recursion pattern avoiding LCNF `._unsafe_rec` synthesis.

### Preserved Package Artifacts (`support/`)

- [`support/BvSimdTseitin.lean`](support/BvSimdTseitin.lean): 3,063-line
  `prelude` + `Init.*` mechanization (`0` `sorry`, `0` native/custom axioms) of
  8-way `OctTrie` (`withForced` strict CPS evaluation), word-parallel GMP bitset
  LRAT (`checkLratGmp_sound`), zero-trust `AigArena` + UNSAT-core Tseitin CNF
  encoder (`checkTseitinCnfTree_sound`), `BitVec w` / x86-64 flag / BMI2 / SWAR /
  SIMD bit-blaster (`checkBvUnsatCert_sound`), and 16-bit-to-$16N$-bit SIMD
  lane-congruence lifter (`simdMapBinary16_comm`, `evalBvExpr_simdVpaddsw`).
- [`support/NonlinearSimdCanaries.lean`](support/NonlinearSimdCanaries.lean):
  Compact (`174,006 B`, `lcnf_unsafe_rec = 0`) end-to-end verified theorem
  module proving 64-bit SWAR `has_zero_byte` equivalence
  (`mycroft_has_zero_byte_eq_borrow_free`), 16-bit signed-saturating `VPADDSW`
  commutativity + overflow clamps via harvested CaDiCaL LRAT, and lifted 256-bit
  AVX2 `BitVec 256` 16-lane `VPADDSW` commutativity
  (`avx2_vpaddsw256_comm_semantic`, `avx2_vpaddsw256_eval_comm`).
- [`support/F2BasisSimd.lean`](support/F2BasisSimd.lean): 966-line `prelude` +
  `Init.*` mechanization (`0` `sorry`, axioms `[Quot.sound, propext]`) of unary
  `checkF2Linear1_sound`, bilinear `checkF2Bilinear_sound`, 64-bit `pclmulqdq`
  Karatsuba vs. schoolbook equivalence and commutativity, 64-bit CRC-64-ECMA
  constant-polynomial folding, and 128-bit 16-lane `vpshufb` $\mathrm{GF}(2^8)$
  split-nibble multiplication (`0x9d`).
- [`support/Pass1GmpLrat.lean`](support/Pass1GmpLrat.lean) and
  [`support/LratBench.lean`](support/LratBench.lean): Strict 6-import
  `foundation-lock.json`-compatible `@Nat.rec` GMP stream LRAT checkers
  (`lcnf_unsafe_rec = 0` across all `231` `ModuleData.constants`, covering
  Peano-free `OctTrie` and 16-bucket `GmpDb16`) and baseline `QuadTrie` /
  `Trie Bool` / `List` / `Array` checkers (`44` `._unsafe_rec` entries).
- [`support/run_harvest_and_vcs.py`](support/run_harvest_and_vcs.py),
  [`support/run_lrat_scaling_matrix.py`](support/run_lrat_scaling_matrix.py), and
  [`support/run_f2_vs_sat_crossover.py`](support/run_f2_vs_sat_crossover.py):
  Self-contained reproduction drivers executing all builds inside
  `tempfile.TemporaryDirectory()`.
- [`support/core_mechanization_metrics.json`](support/core_mechanization_metrics.json),
  [`support/nonlinear_vc_results.json`](support/nonlinear_vc_results.json),
  [`support/lrat_scaling_results.json`](support/lrat_scaling_results.json), and
  [`support/f2_vs_sat_crossover.json`](support/f2_vs_sat_crossover.json):
  Recorded empirical measurements across all experiments.

## Revalidation

To cheaply verify whether these findings still hold on a newer Lean 4 toolchain
or modified downstream audit policy without rerunning the full multi-minute
scaling sweeps:

1. **Bundled solver & LCNF `._unsafe_rec` discriminator (< 5 s):**
   - Check that `<lean-sysroot>/bin/cadical --version` exists and returns `0`.
   - Compile `support/Pass1GmpLrat.lean` with `lean -DElab.async=false
     -Ddebug.skipKernelTC=false -o /tmp/Pass1GmpLrat.olean
     support/Pass1GmpLrat.lean` and inspect `ModuleData.constants` to confirm
     `0` constants satisfy `ci.isUnsafe || ci.isPartial` (confirming `@Nat.rec`
     still suppresses LCNF `._unsafe_rec` emission).
2. **End-to-end Tseitin + GMP LRAT + 256-bit SIMD replay check (~50 s):**
   - Compile `support/BvSimdTseitin.lean` and `support/NonlinearSimdCanaries.lean`
     in a temporary directory under `-DElab.async=false -Ddebug.skipKernelTC=false`,
     and run private-level `toKernelEnv.replay` (`support/run_harvest_and_vcs.py`),
     verifying `rc = 0` and transitive axioms `⊆ {propext, Classical.choice,
     Quot.sound}` with zero `_native.bv_decide` or `Lean.ofReduceBool` constants.
3. **$\mathbb{F}_2$-linear / bilinear GMP kernel check (~10 s fast probe or ~60 s full):**
   - Run `support/run_f2_vs_sat_crossover.py` (or compile `support/F2BasisSimd.lean`
     directly) and verify `#print axioms` on
     `F2SimdCert.pclmulqdq64_karatsuba_eq_schoolbook` and
     `F2SimdCert.vpshufb128_gf256_mul_0x9d_eq` reports `[propext, Quot.sound]`
     only.
4. **Anneal `foundation-lock.json` / `TrustedBoundary.lean` check (< 2 s):**
   - Diff `trusted/lean/foundation-lock.json` and `allowedTheoryTacticKinds` /
     `validateRepoConstant` in `trusted/audit/TrustedBoundary.lean` against
     `c131b320eeeb26ef692e5afd5ec8db49ee518613` to determine whether
     `Init.Data.BitVec.{Basic,Lemmas,Bitblast}` or `decide +kernel` have been
     admitted.
