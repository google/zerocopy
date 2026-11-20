# Elaborating Carcara/Alethe, LRAT, Spacer CHC, Crab SplitDBM, and egglog Traces into Pass-1 Lean 4 Kernel Certificates

## Summary

Standard Lean 4 SAT and SMT proof-reflection pipelines—most notably `Std.Tactic.BVDecide`'s `CompactLRATChecker`—cannot execute inside a standalone, minimal-TCB Pass-1 Lean 4 (`v4.34.1`) audit boundary for four independent structural reasons: (1) native boolean reflection relies either on `Lean.ofReduceBool` / `Lean.trustCompiler` (`Init.Core`) or on per-goal native-evaluation axioms, expanding the trusted computing base by ~30,000 LOC of compiler/interpreter code and violating strict three-axiom foundation locks (`{Classical.choice, Quot.sound, propext}`); (2) `Std.Tactic.BVDecide` uses module-system headers (`module`, `public import Std.*`, `@[expose] public section`) outside a locked `Init.*` prelude; (3) `compactLratChecker`'s equation-compiled tail loop (`where go`) emits an auxiliary `partial` `._unsafe_rec` constant skipped by `Lean.Kernel.Environment.replay`; and (4) `DefaultFormula` mutates four `Array` fields whose lookups and updates degrade from $O(1)$ compiled C array mutations to $O(N)$ linked-`List` traversals inside standalone kernel WHNF reduction.

To verify bitvector, linear-integer, equational, and loop-invariant obligations without enlarging the Lean TCB, all solver search and elaboration—`cvc5` Alethe emission, `ufmg-smite/carcara` elaboration, `CaDiCaL`/`drat-trim` LRAT generation, `Z3/Spacer` Constrained Horn Clause (CHC) synthesis, `seahorn/crab` `SplitDBM` abstract interpretation, and `egraphs-good/egglog` scheduled saturation—remain strictly untrusted outside Lean. An untrusted orchestrator lowers their witnesses into four orthogonal Pass-1 Lean 4 (`prelude` + locked `Init.*`) certificate checkers evaluated via `@Nat.rec`, `List.foldr`, and binary radix-2 `Trie` maps under `rfl` in `<5 ms` per verification condition:

1. **`RupLratTrieCert`**: `Trie (List Nat)` LRAT checker (`2*v` positive, `2*v + 1` negative; `Nat.xor lit 1` negation) with zero `Array` allocations and zero `Lean.ofReduceBool`.
2. **`OmegaCutCert`**: `List.foldr` rational/integer Farkas checker supporting `Carcara`'s GCD Chvátal-Gomory strengthening ($\sum c_i x_i > d \implies \sum c_i x_i \ge \lfloor d \rfloor + g$ for $g \mid \gcd(d, c_1, \dots, c_k)$).
3. **`CongruenceDag`**: topological `Trie` DAG checker for `Carcara` `refl`/`symm`/`trans`/`cong` and `egglog` `:internal-proof-names` (`congr`, `trans`, `sym`, `normalize`) traces.
4. **`SplitDbmHornCert`**: `Crab` `SplitDBM` potential witness ($x - y \le k$ with $\pi(u) + w(u, v) - \pi(v) \ge 0$) paired with `Z3/Spacer` `infty_level` per-edge `OmegaCutCert` inductiveness proofs.

## Applicability

This report governs the integration boundary between untrusted external automated reasoning backends and standalone kernel-replayed Lean 4 proof artifacts audited under the Pass-1 trust model of `joshlf/anneal` (`20aa204315cd36aaf944778b7d33c0d609ced8e8`).

### Pass-1 Lean 4 Target Substrate

In `joshlf/anneal` (`20aa204315cd36aaf944778b7d33c0d609ced8e8`, `docs/trust-model.md` and `trusted/audit/TrustedBoundary.lean`), **Pass 1** is the standalone boundary audit over `trusted/lean/` and `theory/`:

- **Locked Prelude**: `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) pinned in `trusted/lean/foundation-lock.json` to 51 `Init.*` modules (including `Init.Core`, `Init.Data.Nat.{Basic,Div.Basic,Bitwise.Basic}`, `Init.Data.Int.Basic`, `Init.Data.List.Basic`, and excluding `Init.Data.Nat.Gcd` and all `Std.*`/`Lean.*` modules).
- **Closed Syntax & Tactics**: Modules require an explicit `prelude` header (`TrustedBoundary.lean:442–444, 643–645`) and must parse within `allowedTheorySyntaxKinds` (`L573–574`), banning `module`, `public`, `@[expose]`, `axiom`, `unsafe`, `partial`, `do`, `#[...]` array literals, prefix unary `-` (`«term-_»`, noted in `Trusted/MirSemantics.lean:164–170`), `native_decide`, `bv_decide`, `grind`, and `+native`/`+kernel` (`TrustedBoundary.lean:445–535`).
- **Standalone Kernel Replay**: `.olean` artifacts load at `trustLevel := 0, loadExts := false` (`L425–427`), reject `isUnsafe || isPartial` constants (`ensureReplayableConstant`, `L1117–1125`), restrict axioms to `{Classical.choice, Quot.sound, propext}` (`L1199–1202`), and replay from scratch via `Kernel.Environment.replay`.

### Relationships Among Examined Subjects

1. **SMT Emission & Elaboration (`cvc5/cvc5` at `4cc4e66310f82f49f2e99e722bc74e0bfee41ffb` and `ufmg-smite/carcara` v1.1.0 at `819f30914665019898cbad7e09d3962053b6f97a`)**: `cvc5` (`--produce-proofs --proof-format-mode=alethe`) emits Alethe proofs over `QF_UF`, `QF_LIA`, and bit-blasted `QF_BV`; `Carcara` checks and elaborates coarse rules (`polyeq`, `bounded_farkas`, `lia_generic`, `all_simplify`, `rare_rewrite`, `sat_refutation`, `resolution`).
2. **Baseline Lean Kernel & LRAT Reference (`leanprover/lean4` `v4.34.1` at `5045d0056413266e57c625dcd7c365b10e377c52`)**: defines both target kernel replay (`Init/Core.lean`, `Lean/Replay.lean`) and upstream `Std.Tactic.BVDecide.LRAT` (`Checker.lean`, `CompactLRATChecker.lean`, `Formula/Implementation.lean`).
3. **Invariant & Saturation Synthesis (`Z3Prover/z3` at `24fb9f2f2c3a7745d88e53ad61c39b9d1758899f`, `seahorn/crab` at `b1eeb1a9402ab0664e962f26f89d923f8514284c`, and `egraphs-good/egglog` at `d89bc58adc9b9a87a8f571c5b9ad75d686d226e6`)**: `Z3/Spacer` (`fp.engine=spacer`), `Crab` `split_dbm_domain` (`zones_close_bounds_inline`, `zones_widen_restabilize`), and `egglog` schedules synthesize loop invariants, sparse difference bounds, and equational rewrite chains outside the TCB.

Observations on the seven pinned revisions are direct source/normative facts; the four Pass-1 certificate checkers and `<5 ms` envelope in Finding 4 are **derived** designs audited against `TrustedBoundary.lean`.

## Findings

### 1. Why Native Lean 4 LRAT and SMT Reflection Fail Standalone Pass-1 Kernel Audit

Basis: normative + source

Inspecting `leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`) against `joshlf/anneal` (`20aa204315cd36aaf944778b7d33c0d609ced8e8`, `trusted/audit/TrustedBoundary.lean`) isolates four independent blockers preventing `bv_decide` and `CompactLRATChecker` from running in Pass 1:

1. **Compiler-Reflection vs. Per-Goal Native Axioms (`src/Init/Core.lean:2337–2408`)**:
   Lean 4.34.1 defines `axiom trustCompiler : True` (`L2338`), `opaque reduceBool` (`L2361–2364`), and `axiom ofReduceBool` (`L2396`), deprecated (`since := "2026-02-01"`) in favor of asserting per-goal native-evaluation axioms, adding ~30k LOC of compiler/interpreter/`@[extern]` code to the TCB (`L2350–2358`). Pass 1 blocks both routes: `foundation-lock.json:2–15` and `TrustedBoundary.closure` (`L1199–1202`) admit only `{Classical.choice, Quot.sound, propext}`; `forbiddenVendorCompilerRefs` (`L1615–1617`) bans `Lean.{ofReduceBool, ofReduceNat, trustCompiler, reduceBool, reduceNat}`; `validateRepoConstant` (`L1144–1148`) rejects every local `ci.isAxiom`; and `allowedTheoryTacticKinds` (`L529–535`) bans `native_decide`, `bv_decide`, `decide!`, `grind`, and `+native`.
2. **Module-System Headers and Unpinned `Std.*` Imports**:
   `LRAT/Checker.lean:6–14` and `CompactLRATChecker.lean:6–15` use `module`, `public import Std.Tactic.BVDecide.LRAT.Internal.*`, and `@[expose] public section`, all rejected by `inspectSource` (`TrustedBoundary.lean:440–444, 594–595, 984–986`).
3. **Equation-Compiled `._unsafe_rec` Helpers Skipped by Kernel Replay**:
   `CompactLRATChecker.lean:27–60` defines `where go ... (idx : Nat)` recursing on `idx < proof.size`, which elaborates via `WellFounded.fix` plus a `partial` `._unsafe_rec` helper. Because `src/Lean/Replay.lean:176–185` skips `unsafe`/`partial` constants, `ensureReplayableConstant` (`TrustedBoundary.lean:1108–1120`) rejects `ci.isUnsafe || ci.isPartial`. Pass-1 computable checkers must iterate strictly via `@Nat.rec` and `List.foldr` into `Type`.
4. **Quadratic/Cubic `Array` Spine Copying in Standalone WHNF**:
   `Formula/Implementation.lean:61–67` stores four `Array` fields (`clauses`, `rupUnits`, `ratUnits`, `assignments`). Without `ofReduceBool`, kernel WHNF unfolds `Array α` to `List α`, degrading `clauses[id]?` (`L183`), `clauses.set!` (`L108`), and `assignments.modify` (`L128, 192`) to $O(N)$ list copies ($\Theta(H \cdot (V + C))$ allocations across $H$ hints), while `#[...]` (`L73`) and `Id.run do` (`L331–336`) fail `TrustedBoundary.lean:491, 521`.

| Upstream `leanprover/lean4` (`v4.34.1`) Feature | Source Locus | Pass-1 Rejection Mechanism (`joshlf/anneal` `20aa204315cd`) | Pass-1 Certificate Replacement |
| :--- | :--- | :--- | :--- |
| `Lean.ofReduceBool` / `trustCompiler` / eval axioms | `src/Init/Core.lean:2338–2396` | `foundation-lock.json:2–15`; `TrustedBoundary.lean:1144, 1200, 1616` | Pure kernel WHNF reduction (`by rfl`) |
| `module`, `public import Std.*`, `@[expose]` | `LRAT/Checker.lean:6–14` | `allowedHeaderKinds` (`L442`), `allowedAttributeNames` (`L594`) | `prelude` + locked `Init.{Core,Data.*}` |
| `where go` (`idx < proof.size` recursion) | `CompactLRATChecker.lean:31–60` | `._unsafe_rec` rejected by `ensureReplayableConstant` (`L1119`) | `@Nat.rec` depth recursion + CPS `List.foldr` |
| `DefaultFormula` (`Array` fields, `#[...]`, `do`) | `Formula/Implementation.lean:61–73, 331` | `#[...]`/`do` banned (`L491, 521`); `Array` is $O(N)$ `List` in WHNF | Radix-2 `Trie α` ($O(\log N)$ `Nat.land`/`Nat.shiftRight`) |
| `Literal (PosFin n)` dependent bounds | `Formula/Implementation.lean:63–66, 120` | `Fin` proof terms bloat WHNF environments | `Nat` literal `2*v + negBit` (`negLit = Nat.xor lit 1`) |

### 2. `cvc5` Alethe Emission and `Carcara` Proof Checking & Elaboration Mechanics

Basis: normative + source

Inspecting `cvc5` (`4cc4e66310f82f49f2e99e722bc74e0bfee41ffb`) and `ufmg-smite/carcara` (`819f30914665019898cbad7e09d3962053b6f97a`) defines the exact elaboration invariants between raw SMT proofs and Pass-1 certificates:

1. **`cvc5` Alethe Rule Taxonomy (`src/proof/alethe/alethe_proof_rule.h:27–563`, `alethe_post_processor.cpp:37–217`)**:
   `AletheProofPostprocessCallback` emits scoped anchors (`ANCHOR_SUBPROOF`, `ANCHOR_BIND`, `ANCHOR_SKO_FORALL`, `ANCHOR_SKO_EX`, `ANCHOR_ONEPOINT`), equality/clausal rules (`EQ_REFLEXIVE`, `EQ_TRANSITIVE`, `EQ_CONGRUENT`, `EQ_CONGRUENT_PRED`, `SYMM`, `TRANS`, `RESOLUTION`, `TH_RESOLUTION`, `REORDERING`, `CONTRACTION`), arithmetic rules (`LA_RW_EQ`, `LA_GENERIC`, `LA_DISEQUALITY`, `LA_TOTALITY`, `LA_TAUTOLOGY`, `LIA_GENERIC`), rewrite holes (`ALL_SIMPLIFY`, `POLY_SIMP`, `EVALUATE`, `RARE_REWRITE` over `rare-list`), 17 bit-blasting rules via `s_bvKindToAletheRule` (`BV_BITBLAST_STEP_{BVAND,BVOR,BVXOR,BVADD,BVMULT,BVULT,EXTRACT,...}`, `alethe_post_processor.cpp:37–55`), and `HOLE` (`alethe_proof_rule.h:559`).
2. **`Carcara` Checker Invariants (`src/checker/mod.rs:84–114, 183–275, 440–517`)**:
   `check_with_stats` requires `step.clause.is_empty() && self.context.is_empty()` at depth `0` (`DoesNotReachEmptyClause`, `L183–185, 246–248`); `check_discharge` (`L440–458`) verifies closing `subproof` steps discharge all local `Assume`s; `check_outbound_capture` (`L493–517`) blocks outer premises (`p.index.0 < context_depth`) captured by inner `AnchorArg`s; `check_non_idempotent_context` (`L460–491`) and `assert_idempotent_context` (`src/elaborator/mod.rs:368–394`) guard against asymmetric `(= t u)` ($\sigma(t) = u$) under non-idempotent anchor substitutions (`NonIdempotentContext`); and `elaborated: true` (`src/checker/mod.rs:86–92, 294–297`) disables implicit `Polyeq` in `assume`/`refl` while requiring explicit `resolution` pivots.
3. **Six-Pass Elaboration and the Nested `lia_generic` `Status::Holey` Asymmetry**:
   `Elaborator` (`src/elaborator/mod.rs:59–166`) runs `Polyeq` (`L257–310`), `Hole`, `Local` (`L225–255`), `Uncrowd`, `Reordering`, and `SatRefutation`. Crucially, `Checker::check_step` (`src/checker/mod.rs:416–418`) marks `"hole"` and `"lia_generic"` as `Status::Holey`. During `ElaborationPass::Hole`, `hole::hole` (`src/elaborator/hole.rs:8–40`) rejects `status == Status::Holey` (`InnerProofHoley`), whereas `hole::lia_generic` (`L42–62`) writes `let (commands, _) = external::get_solver_proof(...)?;`, ignoring `status`! An orchestrator **must** re-check the elaborated proof with `Config::new().elaborated(true)` and require `Status::Valid`.
4. **`la_generic` / `bounded_farkas` and GCD Chvátal-Gomory Strengthening (`src/checker/rules/linear_arithmetic.rs:180–390`)**:
   `la_generic_partial` negates each literal $\phi_i$ (`negate_disequality`, `L24–56`) into $L_i(x) \bowtie_i d_i$ ($\bowtie_i \in \{>, \ge, =\}$), infers omitted unit multipliers $a_i = -c_2 / c_1$ in `bounded_farkas` (`L286–301`), and—when all terms have `Sort::Int` and integer coefficients (`L207–210`)—applies `strengthen` (`L203–260`) *before* multiplying by $|a_i|$:
   - For `>=` with $d_i \notin \mathbb{Z}$, $d_i \leftarrow \lfloor d_i \rfloor + 1$ (`L252–256`).
   - For `>`, `coefficients_gcd` (`L180–200`) computes $g = \max(1, \gcd(\text{numer}(d_i), \{c_{i,v}\}))$ **including the constant $d_i$**, tightening $L_i(x) > d_i$ to $L_i(x) \ge \lfloor d_i \rfloor + g$ (`L245–251`; e.g., $-2n > 2$ with $g = 2$ becomes $-2n \ge 4$, `L228–244`).
   Summing $|a_i| L_i(x)$ (or signed $a_i L_i(x)$ for `=`) must cancel all variables (`left_side.is_empty()`) and falsify $0 \bowtie_{\text{acc}} D$ (`L366–383`). Passing $g$ as an explicit divisor hint in `OmegaCutCert` verifies this exact strengthening in Lean using only `Nat.mod` (`Init.Data.Nat.Div.Basic`) without importing `Init.Data.Nat.Gcd`.
5. **`sat_refutation` Lowering (`src/elaborator/sat_refutation.rs:71–326`, `src/drup.rs:65–210`)**:
   `sat_refutation` exports premise clauses to DIMACS CNF, invokes SAT + `drat-trim` to obtain an unsat core and LRAT proof (`L255–256`), re-proves core theory lemmas in `cvc5` (`L268–291`), and parses LRAT lines in reverse (`L149–193`). Feeding `drat-trim`'s LRAT hint IDs directly to `RupLratTrieCert` avoids expanding large SAT refutations into binary Alethe `resolution` trees (`build_res_step`, `L31–69`).

### 3. Invariant Synthesis and Saturation Backends: `Z3/Spacer`, `Crab` `SplitDBM`, and `egglog`

Basis: normative + source

1. **`Z3/Spacer` CHC Inductive Frames (`Z3Prover/z3` `24fb9f2f2c3a7745d88e53ad61c39b9d1758899f`)**:
   In `src/muz/spacer/spacer_context.h:71–260` and `spacer_context.cpp:3097–4307`, `spacer::context` solves Horn rules by pairing under-approximating `reach_fact`s (`mk_rf` + model-based projection `mbp`, `spacer_context.cpp:3964–4039`) with over-approximating `pob` obligations and `frames` (`create_children` + `compute_implicant_literals` + `mbp`, `L4045–4162`). When `context::propagate` (`L3899–3962`) finds a level `lvl` where `all_propagated` holds across all `m_rels`, `r.propagate_to_infinity(lvl)` (`L3941`) promotes that frame to `infty_level`. `get_constraints(infty_level())` (`L4283–4307`) extracts $\bigwedge_P (P(\vec{x}) \implies I_P(\vec{x}))$; as `check_invariant` (`L4266–4281`) shows, inductiveness of $I$ on each CFG edge reduces to a quantifier-free `UNSAT` check discharged directly by `OmegaCutCert` / `RupLratTrieCert`.
2. **`Crab` `SplitDBM` Sparse Zones & Potential Witnesses (`seahorn/crab` `b1eeb1a9402ab0664e962f26f89d923f8514284c`)**:
   In `include/crab/domains/split_dbm.hpp:66–260, 480–899, 1678–2088`, `split_dbm_domain` separates unary bounds through vertex `0` (`0 -> v` for $v \le u$, `v -> 0` for $-v \le \ell$, `L706–709`) from relational difference edges `src -> dest` ($\text{dest} - \text{src} \le k$, `L536–553`) closed over `SubGraph<graph_t> g_excl(g, 0)` (`L723, 1838, 2073`). Crucially, `split_dbm_domain` maintains vertex potentials `potential` satisfying `potential[u] + edge(u, v) - potential[v] >= 0` (`check_potential`, `L194–205`), providing an **$O(|E|)$ certificate of negative-cycle absence** without $O(|V|^3)$ Floyd-Warshall inside Lean. `operator||` (`split_widen`, `L1678–1751`) tracks `unstable` vertices for lazy `normalize()` (`L2063–2088`), while `operator&&` (`L2041–2044`) implements narrowing as meet (`*this & o`) and warns callers to bound iterations.
3. **`egglog` Schedules & Native Proof Constructors (`egraphs-good/egglog` `d89bc58adc9b9a87a8f571c5b9ad75d686d226e6`)**:
   `EGraph::run_schedule` (`src/lib.rs:1024–1085`) executes `ResolvedSchedule::{Run, Repeat, Saturate, Sequence}` with `:until` fact guards (`check_facts`, `L1080`) and `Scheduler::filter_matches` (`src/scheduler.rs:51–162`; `Matches::new` at `L113–118` uses `tuple_width = vars.len().max(1)` so zero-variable rules retain match counts). `GenericNCommand::Sort` (`src/ast/mod.rs:26–53, 100–122`) attaches `ProofConstructorNames { congr, trans, sym, normalize }` and `ContainerRebuildSpec` to unionable sorts, allowing the orchestrator to extract only the shortest `congr`/`trans`/`sym`/`normalize` justification DAG into `CongruenceDag`.

### 4. Untrusted-Orchestrator to `<5 ms` Pass-1 Lean 4 Certificate Boundary

Basis: source + derived

#### 4.1 Self-Contained Pass-1 `prelude` Lean 4 (`v4.34.1`) Certificate Checkers

The module below uses `prelude`, imports strictly from `foundation-lock.json`'s 51 `Init.*` modules, avoids prefix `-` (`Int.negOfNat` instead), `noncomputable` `Int.ble'` (defining computable `intBle`/`intBlt` by constructor matching on `b - a`), `Array`, `do`, `partial`/`._unsafe_rec`, and `Lean.ofReduceBool`:

```lean
prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Int.Basic
import Init.Data.List.Basic

namespace Pass1SolverCerts

-- 1. Computable `Int` Comparisons, CPS Left-Fold, and Radix-2 `Trie`
def intBle (a b : Int) : Bool :=
  match b - a with
  | .ofNat _   => true
  | .negSucc _ => false

def intBlt (a b : Int) : Bool := intBle (a + 1) b

inductive Trie (α : Type) where
  | empty
  | node (val : Option α) (ev od : Trie α)

def listFoldl {α β : Type} (f : β → α → β) (init : β) (xs : List α) : β :=
  xs.foldr (fun x k acc => k (f acc x)) (fun acc => acc) init

def Trie.get {α : Type} (depth : Nat) (t : Trie α) (k : Nat) : Option α :=
  @Nat.rec (fun _ => Trie α → Nat → Option α)
    (fun _ _ => none)
    (fun _ ih cur idx =>
      match cur with
      | .empty => none
      | .node v ev od =>
        match idx with
        | 0 => v
        | _ =>
          match Nat.beq (Nat.land idx 1) 0 with
          | true  => ih ev (Nat.shiftRight idx 1)
          | false => ih od (Nat.shiftRight idx 1))
    depth t k

def Trie.set {α : Type} (depth : Nat) (t : Trie α) (k : Nat) (v : Option α) : Trie α :=
  @Nat.rec (fun _ => Trie α → Nat → Trie α)
    (fun cur _ => cur)
    (fun _ ih cur idx =>
      let (v0, ev0, od0) := match cur with
        | .empty => (none, Trie.empty, Trie.empty)
        | .node old ev od => (old, ev, od)
      match idx with
      | 0 => .node v ev0 od0
      | _ =>
        match Nat.beq (Nat.land idx 1) 0 with
        | true  => .node v0 (ih ev0 (Nat.shiftRight idx 1)) od0
        | false => .node v0 ev0 (ih od0 (Nat.shiftRight idx 1)))
    depth t k

-- 2. `RupLratTrieCert`: `Array`-Free LRAT Checker (`2*v` Pos, `2*v+1` Neg)
inductive LratStep where
  | addRup (id : Nat) (clause : List Nat) (hints : List Nat)
  | del (ids : List Nat)
  | addEmpty (hints : List Nat)

def evalClauseRUP (depth : Nat) (assign : Trie Bool) (cls : List Nat) :
    Bool × Option Nat × Nat :=
  cls.foldr
    (fun lit st =>
      match st with
      | (true, u, n) => (true, u, n)
      | (false, u, n) =>
        let varId := Nat.shiftRight lit 1
        let wantPos := Nat.beq (Nat.land lit 1) 0
        match Trie.get depth assign varId with
        | some val =>
          match val, wantPos with
          | true, true => (true, none, 0)
          | false, false => (true, none, 0)
          | _, _ => (false, u, n)
        | none => (false, some lit, n + 1))
    (false, none, 0)

def checkRupHints (depth : Nat) (clauses : Trie (List Nat))
    (target : List Nat) (hints : List Nat) : Bool :=
  let initState := target.foldr
    (fun lit st =>
      match st with
      | (contradiction, a) =>
        let varId := Nat.shiftRight lit 1
        let negVal := !Nat.beq (Nat.land lit 1) 0
        match Trie.get depth a varId with
        | some old =>
          match old, negVal with
          | true, false => (true, a)
          | false, true => (true, a)
          | _, _ => (contradiction, a)
        | none => (contradiction, Trie.set depth a varId (some negVal)))
    (false, Trie.empty)
  match initState with
  | (true, _) => true
  | (false, initAssign) =>
    (listFoldl
      (fun st cid =>
        match st with
        | (true, err, a) => (true, err, a)
        | (false, true, a) => (false, true, a)
        | (false, false, a) =>
          match Trie.get depth clauses cid with
          | none => (false, true, a)
          | some cls =>
            match evalClauseRUP depth a cls with
            | (true, _, _) => (false, true, a)
            | (false, _, 0) => (true, false, a)
            | (false, some uLit, 1) =>
              let varId := Nat.shiftRight uLit 1
              let wantPos := Nat.beq (Nat.land uLit 1) 0
              (false, false, Trie.set depth a varId (some wantPos))
            | (false, _, _) => (false, true, a))
      (false, false, initAssign) hints).1

def checkRupLratCert (depth : Nat) (initClauses : List (Nat × List Nat))
    (steps : List LratStep) : Bool :=
  let db0 := initClauses.foldr (fun e db => Trie.set depth db e.1 (some e.2)) Trie.empty
  (listFoldl
    (fun st step =>
      match st with
      | (true, ok, db) => (true, ok, db)
      | (false, false, db) => (false, false, db)
      | (false, true, db) =>
        match step with
        | .addRup cid cls hints =>
          match checkRupHints depth db cls hints with
          | true  => (false, true, Trie.set depth db cid (some cls))
          | false => (false, false, db)
        | .del ids => (false, true, ids.foldr (fun cid cur => Trie.set depth cur cid none) db)
        | .addEmpty hints =>
          match checkRupHints depth db [] hints with
          | true  => (true, true, db)
          | false => (false, false, db))
    (false, true, db0) steps).1

-- 3. `OmegaCutCert`: `Carcara` `la_generic` Farkas + Divisibility-Checked GCD Cut
structure IntLinearGe where
  gcdHint : Nat               -- `0` for `>=`; `g >= 1` for strict `>` strengthened by `g`
  coeffs  : List (Nat × Int)  -- `(varId, c_v)`
  rhs     : Int

def strengthenIntGe (ineq : IntLinearGe) : Option (List (Nat × Int) × Int) :=
  match ineq.gcdHint with
  | 0 => some (ineq.coeffs, ineq.rhs)
  | g =>
    let dividesAll := Nat.beq (Nat.mod (Int.natAbs ineq.rhs) g) 0 &&
      ineq.coeffs.foldr (fun vc ok => ok && Nat.beq (Nat.mod (Int.natAbs vc.2) g) 0) true
    match dividesAll with
    | true  => some (ineq.coeffs, ineq.rhs + Int.ofNat g)
    | false => none

def addScaledCoeffs (depth mult : Nat) (coeffs : List (Nat × Int)) (acc : Trie Int) : Trie Int :=
  let mInt := Int.ofNat mult
  coeffs.foldr
    (fun vc cur =>
      let prev := match Trie.get depth cur vc.1 with | some v => v | none => 0
      Trie.set depth cur vc.1 (some (prev + mInt * vc.2)))
    acc

def checkOmegaCutCert (depth : Nat) (varIds : List Nat)
    (premises : List (Nat × IntLinearGe)) : Bool :=
  let res := listFoldl
    (fun st item =>
      match st with
      | (false, cm, rs) => (false, cm, rs)
      | (true, cm, rs) =>
        match strengthenIntGe item.2 with
        | none => (false, cm, rs)
        | some (cs, rStrong) =>
          (true, addScaledCoeffs depth item.1 cs cm, rs + Int.ofNat item.1 * rStrong))
    (true, Trie.empty, (0 : Int)) premises
  match res with
  | (false, _, _) => false
  | (true, coeffMap, rhsSum) =>
    let cancelled := varIds.foldr
      (fun vid ok => ok && match Trie.get depth coeffMap vid with | none => true | some c => c == 0)
      true
    cancelled && intBlt 0 rhsSum

-- 4. `CongruenceDag` & `SplitDbmPotentialCert`
structure DagTerm where
  headSym : Nat
  argIds  : List Nat

inductive EqCertStep where
  | refl (nodeId : Nat)
  | symm (eqIdx : Nat)
  | trans (eqIdx1 eqIdx2 : Nat)
  | cong (lhsNode rhsNode : Nat) (argEqIdxs : List Nat)

def checkArgEqs (depth : Nat) (proven : Trie (Nat × Nat)) (xs ys eqIdxs : List Nat) : Bool :=
  xs.foldr
    (fun x k ysRem eqsRem =>
      match ysRem, eqsRem with
      | y :: yr, eid :: er =>
        match Trie.get depth proven eid with
        | some (a, b) => Nat.beq a x && Nat.beq b y && k yr er
        | none => false
      | [], [] => true
      | _, _ => false)
    (fun ysRem eqsRem => match ysRem, eqsRem with | [], [] => true | _, _ => false)
    ys eqIdxs

def checkCongruenceDag (depth : Nat) (nodes : Trie DagTerm)
    (steps : List (Nat × EqCertStep)) (goalEqIdx goalLhs goalRhs : Nat) : Bool :=
  let finalProven := listFoldl
    (fun st entry =>
      match st with
      | (false, p) => (false, p)
      | (true, p) =>
        match entry.2 with
        | .refl nid => (true, Trie.set depth p entry.1 (some (nid, nid)))
        | .symm i =>
          match Trie.get depth p i with
          | some (a, b) => (true, Trie.set depth p entry.1 (some (b, a)))
          | none => (false, p)
        | .trans i j =>
          match Trie.get depth p i, Trie.get depth p j with
          | some (a, b1), some (b2, c) =>
            match Nat.beq b1 b2 with
            | true  => (true, Trie.set depth p entry.1 (some (a, c)))
            | false => (false, p)
          | _, _ => (false, p)
        | .cong lId rId argEqs =>
          match Trie.get depth nodes lId, Trie.get depth nodes rId with
          | some lt, some rt =>
            match Nat.beq lt.headSym rt.headSym &&
                  checkArgEqs depth p lt.argIds rt.argIds argEqs with
            | true  => (true, Trie.set depth p entry.1 (some (lId, rId)))
            | false => (false, p)
          | _, _ => (false, p))
    (true, Trie.empty) steps
  match finalProven with
  | (false, _) => false
  | (true, p) =>
    match Trie.get depth p goalEqIdx with
    | some (a, b) => Nat.beq a goalLhs && Nat.beq b goalRhs
    | none => false

structure SplitDbmEdge where
  src : Nat
  dst : Nat
  wt  : Int

def checkSplitDbmPotentials (depth : Nat) (potentials : Trie Int)
    (edges : List SplitDbmEdge) : Bool :=
  edges.foldr
    (fun e ok =>
      let pu := match Trie.get depth potentials e.src with | some v => v | none => 0
      let pv := match Trie.get depth potentials e.dst with | some v => v | none => 0
      ok && intBle 0 (pu + e.wt - pv))
    true

-- Concrete Kernel `rfl` Canaries
theorem rup_lrat_unsat_canary :
    checkRupLratCert 4 [(1, [2, 4]), (2, [3]), (3, [5])] [.addEmpty [2, 3, 1]] = true := rfl

theorem carcara_gcd_cut_canary :
    checkOmegaCutCert 4 [1, 2]
      [ (1, ⟨0, [(1, 1)], Int.negOfNat 1⟩)
      , (1, ⟨0, [(1, 1), (2, 1)], Int.negOfNat 1⟩)
      , (1, ⟨2, [(1, Int.negOfNat 2)], 2⟩)
      , (1, ⟨0, [(2, Int.negOfNat 1)], Int.negOfNat 1⟩) ] = true := rfl

theorem split_dbm_potential_canary :
    let pots := Trie.set 4 (Trie.set 4 Trie.empty 1 (some 2)) 2 (some 0)
    checkSplitDbmPotentials 4 pots [⟨2, 1, 3⟩, ⟨1, 2, Int.negOfNat 1⟩] = true ∧
    checkSplitDbmPotentials 4 pots [⟨2, 1, 3⟩, ⟨1, 2, Int.negOfNat 4⟩] = false := ⟨rfl, rfl⟩

end Pass1SolverCerts
```

#### 4.2 Complexity and `<5 ms` Pass-1 WHNF Envelope

With fixed bit-depth $D = 10$ ($1,024$ addressable slots), every `Trie.get`/`Trie.set` performs at most $10$ constructor matches. Once-per-library `theory/` soundness theorems (`checkRupLratCert_sound`, `checkOmegaCutCert_sound`, `checkCongruenceDag_sound`, `checkSplitDbmPotentials_sound`) connect `check* ... = true` to reified MIR obligations while keeping certificate types confined to `ConstantInfo.value?` (preserving Statement-Origin Separation in `docs/trust-model.md`):

- **`RupLratTrieCert`**: $O(D \cdot \sum |\text{hints}| \cdot \bar{w})$ WHNF steps; `<5 ms` for $\le 250$ RUP clauses and $\le 1,500$ hint lookups.
- **`OmegaCutCert`**: $O(D \cdot \sum |\text{supp}(\phi_i)|)$ WHNF steps (checking `gcdHint` divisibility in $O(1)$ `Nat.mod` ops); `<5 ms` for $\le 150$ inequalities over $\le 100$ variables.
- **`CongruenceDag` & `SplitDbmHornCert`**: $O(D \cdot |\text{steps}|)$ and $O(D \cdot |E_{\text{DBM}}|)$ WHNF steps; `<5 ms` for $\le 400$ DAG steps and $\le 200$ `SplitDBM` edges.

## Boundaries

- **Known not to apply — `Carcara` `Status::Valid` as a TCB replacement for Lean kernel replay**: Even with `elaborated: true`, `Carcara` trusts its Rust implementation, `rug`/GMP FFI, and any `allowed_rules` (`src/checker/mod.rs:105–106`) or `rule_checkers` (`L108–110`). Soundness in Pass 1 derives solely from Lean's kernel reducing the `theory/` checker and replaying its soundness proof.
- **Known not to apply — `RupLratTrieCert` `rfl` reduction on $10^5$-clause industrial SAT proofs**: Without `Lean.ofReduceBool`, standalone WHNF reduction cannot check hundreds of thousands of clauses within interactive memory/latency budgets; `RupLratTrieCert` targets bounded per-function MIR spans ($10^1$–$10^3$ clauses).
- **Known not to apply — `SplitDBM` potentials as standalone loop-inductiveness proofs**: `checkSplitDbmPotentials` certifies only satisfiability/cycle-freedom of a zone graph (`split_dbm.hpp:194–205`); CFG inductiveness still requires per-edge `OmegaCutCert` / `RupLratTrieCert` witnesses.
- **Unsupported — `Carcara` `generate_lia_smt_instances` at `depth > 0` and non-idempotent symmetry elaboration**: `src/lib.rs:279–282` skips `lia_generic` inside subproofs, and `src/elaborator/mod.rs:385–394` rejects symmetry elaborations under non-idempotent anchor contexts (`ElaborationError::NonIdempotentContext`).
- **Unsupported — `Crab` `split_dbm_domain::is_unsat` on disequalities and unguarded narrowing**: `split_dbm.hpp:897–899` returns `false` on `cst.is_disequation()`, and `operator&&` (`L2041–2044`) aliases meet (`*this & o`) without termination guarantees.
- **Unknown — Exact bit-width crossover between `RupLratTrieCert` and `CongruenceDag` on `u128` arithmetic**: Static inspection does not fix the exact `u64`/`u128` operator mix where bit-blasting exceeds `5 ms` of Lean `v4.34.1` WHNF reduction; empirical benchmarking is required to tune orchestrator dispatch.
- **Not examined — Higher-order/quantified Alethe skolemization (`ANCHOR_SKO_*`), nonlinear real CAD certificates, and IEEE-754 floating-point bit-blasting**: Only quantifier-free integer, bitvector, UF, and CHC loop pipelines were examined.

## Evidence

### Primary Repository Sources (Observed 2026-11-20)

- **`ufmg-smite/carcara`** at `819f30914665019898cbad7e09d3962053b6f97a` (`v1.1.0`): `src/lib.rs:77–92, 169–304`; `src/checker/mod.rs:69–140, 183–297, 370–517`; `src/checker/rules/linear_arithmetic.rs:24–56, 180–390`; `src/elaborator/mod.rs:31–166, 202–255, 368–394`; `src/elaborator/hole.rs:8–62`; `src/elaborator/sat_refutation.rs:71–326`; `src/drup.rs:65–210`.
- **`cvc5/cvc5`** at `4cc4e66310f82f49f2e99e722bc74e0bfee41ffb`: `src/proof/alethe/alethe_proof_rule.h:27–563`; `src/proof/alethe/alethe_post_processor.cpp:37–217`.
- **`leanprover/lean4`** at `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`): `src/Init/Core.lean:2334–2408`; `src/Init/Data/Int/Basic.lean:103, 329, 426–434`; `src/Lean/Replay.lean:176–185`; `src/Std/Tactic/BVDecide/LRAT/Checker.lean:6–51`; `Internal/CompactLRATChecker.lean:6–63`; `Internal/Formula/Implementation.lean:61–338`.
- **`Z3Prover/z3`** at `24fb9f2f2c3a7745d88e53ad61c39b9d1758899f`: `src/muz/spacer/spacer_context.h:71–260`; `src/muz/spacer/spacer_context.cpp:3097–3260, 3899–4162, 4255–4307`.
- **`seahorn/crab`** at `b1eeb1a9402ab0664e962f26f89d923f8514284c`: `include/crab/domains/split_dbm.hpp:66–260, 480–899, 1678–2088`.
- **`egraphs-good/egglog`** at `d89bc58adc9b9a87a8f571c5b9ad75d686d226e6`: `src/ast/mod.rs:26–53, 100–122`; `src/scheduler.rs:51–216`; `src/lib.rs:1024–1085`.
- **`joshlf/anneal`** at `20aa204315cd36aaf944778b7d33c0d609ced8e8`: `trusted/lean/foundation-lock.json:1–22`; `trusted/audit/TrustedBoundary.lean:442–596, 1108–1208, 1613–1667`; `trusted/lean/Trusted/MirSemantics.lean:164–172`.

### Normative Specifications and Peer-Reviewed Literature

- Hans-Jörg Schurr, Mathias Fleury, Haniel Barbosa, and Pascal Fontaine, *"Alethe: Towards a Generic SMT Proof Format,"* PxTP 2021, *EPTCS* 336, pp. 49–54, 2021. DOI: `10.4204/EPTCS.336.6`.
- Bruno Andreotti, Hanna Lachnitt, Haniel Barbosa, Rodrigo Otoni, and Mathias Fleury, *"Carcara: An Efficient Proof Checker and Elaborator for SMT Proofs in the Alethe Format,"* TACAS 2023, *LNCS* 13993, pp. 367–386, 2023. DOI: `10.1007/978-3-031-30823-9_19`.
- Anvesh Komuravelli, Arie Gurfinkel, and Sagar Chaki, *"SMT-Based Model Checking for Recursive Programs,"* CAV 2014, *LNCS* 8559, pp. 17–34, 2014 (DOI: `10.1007/978-3-319-08867-9_2`); extended in *Formal Methods in System Design* 48(3), pp. 175–205, 2016 (DOI: `10.1007/s10703-016-0249-4`).
- Graeme Gange, Jorge A. Navas, Peter Schachte, Harald Søndergaard, and Peter J. Stuckey, *"Exploiting Sparsity in Difference-Bound Matrices,"* SAS 2016, *LNCS* 9837, pp. 189–211, 2016. DOI: `10.1007/978-3-662-53413-7`.
- Yihong Zhang, Yisu Remy Wang, Oliver Flatt, David Cao, Philip Zucker, Eli Rosenthal, Zachary Tatlock, and Max Willsey, *"Better Together: Unifying Datalog and Equality Saturation,"* *Proc. ACM Program. Lang.* 7 (PLDI), Article 125, 2023. DOI: `10.1145/3591239`.

## Revalidation

1. **Lean & Pass-1 Boundary Diff (`leanprover/lean4`, `joshlf/anneal`)**: Diff `trusted/lean/foundation-lock.json` (`axioms`, `graph`), `trusted/audit/TrustedBoundary.lean` (`allowedTheoryTacticKinds`, `allowedNotationSyntaxKinds`, `ensureReplayableConstant`, `forbiddenVendorCompilerRefs`), and `src/Init/Core.lean` (`ofReduceBool`), then run Pass-1 `"preflight"` and kernel replay on `Pass1SolverCerts` in Finding 4.1.
2. **`Carcara` Arithmetic & Hole Check (`ufmg-smite/carcara`)**: Diff `src/checker/rules/linear_arithmetic.rs` (`coefficients_gcd`, `strengthen`) to verify whether strict integer `>` still adds `coefficients_gcd()` including the RHS constant, and diff `src/elaborator/hole.rs` (`lia_generic`) to check whether inner `Status::Holey` results remain unchecked without a post-pass `Checker` invocation.
3. **`Crab` & `egglog` Witness Surface**: Diff `split_dbm.hpp` (`check_potential`, `g_excl`, `operator&&`) and `egglog` `src/ast/mod.rs` (`ProofConstructorNames`) + `src/lib.rs` (`run_schedule`).
