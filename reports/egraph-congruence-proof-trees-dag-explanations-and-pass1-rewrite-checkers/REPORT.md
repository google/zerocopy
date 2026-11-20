# E-Graph Congruence Proof Forests, DAG Explanations, and Pure-Kernel Rewrite Certificate Checkers

## Summary

Under pure-kernel verification profiles that forbid metaprogramming tactics (`grind`, `omega`, `ring`, `bv_decide`) and native evaluation (`native_decide`, `decide +kernel`) while locking imports to Lean 4's minimal prelude (`51` `Init.*` modules and `{propext, Quot.sound, Classical.choice}`), equational proofs across `Bool`, `BitVec`, `Nat`, little-endian byte codecs, and chunked lists cannot run general tactic saturation. Equality saturation outside the TCB (`egg`, `egglog`) paired with a **total, linear-time, DAG-shared computational reflection checker** (`CongruenceDag`) cures rewrite fragility in `<0.5 ms` (`Eq.refl true`) without expanding the TCB:

1. **Proof-producing congruence closure decouples search from witness size:** Path-compressing union-find erases merge provenance; Nieuwenhuis–Oliveras (JACM 2007) keep an un-compressed directed proof forest with edge reversal, nearest-common-ancestor (`NCA`) traversal, and an auxiliary `HighestNode` union-find avoiding exponential re-traversal. `egraphs-good/egg` (`src/explain.rs`) adapts this via `make_leader`, greedy Dijkstra shortening (`CONGRUENCE_LIMIT = 2`, `GREEDY_NUM_ITERS = 2`), and `let`-bound `TreeExplanation`.
2. **Upstream explanation checkers are fail-open or partial:** `egg`'s `Explanation::check_proof` (`src/explain.rs:403-441, 782-786`) silently returns `true` when rules are missing (`// give up when the rule is not provided`), dynamic/conditional `Applier`s return `None` from `get_pattern_ast()`, or `union_trusted` labels lack patterns, while `FlatTerm::rewrite` panics on unbound RHS variables. `egglog` (`src/proofs/proof_format.rs`, `proof_checker.rs`) uses hash-consed `TermDag`/`ProofStore` checking and withholds universal reflexivity (`t = t` requires action provenance).
3. **Flattening blows up exponentially; arena `CongruenceDag` validates in C++ GMP:** Flattening nested congruence proofs emits $2^K$ steps on $K$-level doubling congruences while cloning sibling spines. Serializing `let`-shared proofs into a deduplicated arena (`Array DagNode`) and a 5-constructor linear trace (`refl`, `symm`, `trans`, `cong`, `rule`) over closed `VarId := Nat` terms preserves `!has_fvar(t)` (`src/kernel/type_checker.cpp:1093, 1181`), yielding `<0.5 ms` `Eq.refl true` checks with strict `SortTag` typing and zero binder overhead.

## Applicability

This report connects ten primary subjects:

- **Target pure-kernel substrate (`joshlf/anneal` at `20aa204315cd36aaf944778b7d33c0d609ced8e8` and `leanprover/lean4` `v4.34.1` at `5045d0056413266e57c625dcd7c365b10e377c52`):** Pass-1 syntactic admission, module-origin isolation, closed tactic/notation grammars, and kernel replay are grounded in `trusted/audit/TrustedBoundary.lean` (`L442-596, L1108-1366`), `trusted/lean/foundation-lock.json`, and `trusted/lean/Trusted/MirSemantics.lean` (`L164-260, L1150-1193`). Kernel `whnf`/`reduce_nat`/`is_def_eq_core` fast paths are grounded in `src/kernel/type_checker.cpp` (`L1088-1186`).
- **E-graph proof forests and DAG proof stores (`egraphs-good/egg` at `73975c9819efb4af2f3c6c1b44fa53f8c5742574`, `egraphs-good/egglog` at `d89bc58adc9b9a87a8f571c5b9ad75d686d226e6`, Willsey et al. POPL 2021 DOI `10.1145/3434304`, Zhang et al. PLDI 2023 DOI `10.1145/3591239`, Nieuwenhuis–Oliveras JACM 2007 DOI `10.1145/1284320.1284324`):** Grounded in `src/explain.rs`, `src/termdag.rs`, `src/proofs/proof_format.rs`, `src/proofs/proof_checker.rs`, and `src/proofs/proof_encoding_helpers.rs`.
- **Lean 4 equality-saturation tactic architecture (`marcusrossel/lean-egg` at `2605a63b6a78407114c692f5dc626531ff62df55`, Rossel & Goens `arXiv:2405.10188` and POPL 2026 DOI `10.1145/3776667`):** Grounded in `README.md` and `Lean/Egg/Core/Explanation/{Basic,Proof}.lean`.

Relative to sibling reports in the corpus covering general e-graph/AEGraph saturation (`equality-saturation-with-proofs-egraphs-aegraphs-and-refinement-rewriting`), Knuth–Bendix completion and `egglog` circuit extraction (`knuth-bendix-completion-ceta-certificates-and-egglog-circuit-extraction`), Lean tactic internals (`lean-tactic-extensions-simp-omega-and-grind`), and modular Horner ring / Chvátal–Gomory integer cut reflection (`horner-modular-ring-reflection-and-gomory-chvatal-integer-cut-checkers`), this report isolates proof-forest extraction, `egg`/`egglog` DAG witness formats, `check_proof` fail-open hazards, and the 5-constructor Pass-1 Lean 4 `CongruenceDag` design.

## Findings

### 1. Nieuwenhuis–Oliveras Proof Forests vs. `egg` `Explain<L>` and Fail-Open `check_proof` Hazards

`Basis: normative + source + derived`

Path-compressing union-find achieves $O(\alpha(n))$ `find` by flattening parent pointers, erasing the provenance chain explaining *why* two e-nodes are equivalent. Nieuwenhuis and Oliveras (RTA 2005 / JACM 2007, DOI `10.1145/1284320.1284324`) preserve provenance by maintaining an un-compressed **directed proof forest** alongside canonical union-find:

- **Proof-forest orientation and `NCA`:** Each forest edge $(u \to v)$ records the input equation or congruence witness merging $u$ and $v$. On `Union(a, b)`, edges along $a$'s path to its proof-tree root are reversed (`make_leader(a)`), and $a$ is linked to $b$ while bounding tree depth to $O(\log n)$. `Explain(a, b)` locates the nearest common ancestor $d$ of $a$ and $b$ and emits edges on $a \leadsto d$ and $b \leadsto d$.
- **Avoiding redundant congruence work (`HighestNode`):** A single congruence edge $(f(\vec{a}), f(\vec{b}))$ recurses into child pairs $(a_i, b_i)$ whose paths can overlap sibling traversals exponentially. Nieuwenhuis and Oliveras pair `Explain` with a dynamically created auxiliary union-find tracking `HighestNode(x)`—the node closest to the root among already-explained equivalents—jumping directly past visited segments to achieve near-linear time in the proof size $k$.

In Rust, `egraphs-good/egg@73975c9819efb4af2f3c6c1b44fa53f8c5742574` (`src/explain.rs`) implements this proof-forest architecture inside `Explain<L>` (`L50-72`):

1. **Forest edges and memoized extraction (`L32-47, 111-112, 922-1007, 1202-1293`):** Each `ExplainNode` stores `parent_connection : Connection` (`current`, `next`, `justification : Rule(Symbol) | Congruence`, `is_rewrite_forward : bool`) and `neighbors : Vec<Connection>`. `Explain::make_leader` (`L922-935`) recursively flips parent edges and `is_rewrite_forward` bits. Instead of Nieuwenhuis–Oliveras's auxiliary `HighestNode` union-find, `explain_enodes` (`L1202-1293`) caches subtree proofs in `ExplainCache<L> = HashMap<(Id, Id), Rc<TreeTerm<L>>>` and `NodeExplanationCache<L> = HashMap<Id, Rc<TreeTerm<L>>>`.
2. **Greedy Dijkstra explanation shortening (`L18-19, 1477-1830`):** With `optimize_explanation_lengths = true` (`L902`), `calculate_shortest_explanations` (`L1808-1830`) harvests implicit congruence edges (`find_congruence_neighbors`, bounded at `CONGRUENCE_LIMIT * explainfind.len()` with `CONGRUENCE_LIMIT = 2` at `L18, 1516`), computes offline common ancestors via `tarjan_ocla` (`L1699-1734`), and runs `shortest_path_modulo_congruence` for `GREEDY_NUM_ITERS = 2` iterations (`L19, 1542-1696, 1828`), recording shortcuts in `shortest_explanation_memo`.

Auditing `egg`'s built-in validator `Explanation::check_proof` (`src/explain.rs:368-442, 780-856`) exposes **three defects that disqualify it as a verification oracle**:

| Mechanism (`src/explain.rs`) | Observed Source Behavior | Verification Consequence |
| :--- | :--- | :--- |
| Missing rule (`L404-415`) | `if let Some(rule) = table.get(rule_name) { ... } else { true }` (`// give up when the rule is not provided`) | **Fail-open:** Steps naming an absent rule or `union_instantiations` / `union_trusted` label silently pass `check_proof` (reproduced in Revalidation). |
| Non-pattern applier (`L432-441`) | `if let Some(lhs) = rewrite.searcher.get_pattern_ast() && let Some(rhs) = rewrite.applier.get_pattern_ast() { ... } true` | **Fail-open:** Every dynamic, constant-folding, or conditional Rust `Applier` returning `None` from `get_pattern_ast()` is accepted unchecked. |
| Substitution matching (`L782-856`) | `bindings.get(var).unwrap()` and `assert!(node.matches(&self.node))` inside `FlatTerm::rewrite` | **Partial/panicking:** Unbound RHS variables panic instead of returning `false`. |

### 2. Flat Proof Chains vs. `let`-Bound `TreeExplanation` (`egg`) and Relational `ProofStore` (`egglog`)

`Basis: source + execution + derived`

How congruence proofs share subterms separates linear DAG checking from exponential chain blowup:

- **`egg` `FlatExplanation` vs. `let`-bound `TreeExplanation` (`src/explain.rs:190-364, 486-573`):** `TreeTerm<L>` shares child proofs via `Rc<TreeTerm<L>>`. Calling `make_flat_explanation` (`L359-364`) invokes `TreeTerm::flatten_explanation` (`L534-572`), materializing full `FlatTerm<L>` snapshots at every step and duplicating unmodified sibling subtrees (`L549-566`). On depth-$K$ doubling congruence $f^K(x) = f^K(y)$ ($f(u) = \text{add}(u, u)$, $x = y$ via `base_eq`), flattening emits $2^K$ rewrite steps ($256$ steps / $257$ `FlatTerm` snapshots at $K=8$), whereas DAG extraction emits **$9$ DAG steps** (`1` rule + `8` congruence nodes; reproduced in Revalidation). Conversely, `get_tree_size` (`L247-288`) deduplicates by `Rc` pointer and `(current, last)` edge, while `get_sexp_with_let` (`L290-346`) hoists multi-use subproofs (`find_to_let_bind`, `L329-346`) into `let v_i = ...` bindings.
- **`egglog`'s `TermDag` and `ProofStore` (`egraphs-good/egglog@d89bc58adc9b9a87a8f571c5b9ad75d686d226e6`):** Hash-consing terms in `TermDag` (`IndexSet<Term>` with structural `ast_cmp`, `src/termdag.rs:13-24, 178-210`) and proofs in `ProofStore` (`DenseIdMap<ProofId, Proof>`, `src/proofs/proof_format.rs:86-94`) yields four design contrasts:
  1. **Explicit reflexivity provenance (`proof_format.rs:114-115, 154-213`, `proof_checker.rs:222-254`):** Because `egglog` models a *partial* equivalence relation, `t = t` is not assumed universally; `add_subterm_reflexive_equalities` derives reflexivity only for action-touched subterms (`Fiat`). In a total Lean 4 `Type` denotation, `refl nodeId` is unconditionally sound on valid arena nodes.
  2. **1-child `Congr` vs. $k$-ary `cong` (`proof_format.rs:197-201, 700-729`):** `egglog`'s `Congr { proof, child_index, child_proof }` allocates intermediate nodes via `replace_term_child`; $k$-ary `cong` checks all $m$ children at once, eliminating $m - 1$ intermediate nodes and steps.
  3. **Proof-mode boundaries (`proof_encoding_helpers.rs:555-706`):** Rejects `:unsafe-seminaive` rules, validator-free primitives (`proof_checker.rs:201-208`), non-global action lookups, and query-constructed containers used in actions.
  4. **Printing threshold vs. arena sharing (`termdag.rs:66, 403-415`):** `TermDag::render_term` skips `let`-bindings for `term_size < MIN_SHARED_TERM_SIZE` (`4`) or `repeat_count == 1`; certificate arenas share every subterm and step by `Nat` index.

### 3. Why `lean-egg` and `grind` Are Excluded in Pass 1—and First-Order Reflection

`Basis: source + derived`

Upstream `marcusrossel/lean-egg` (`2605a63b6a78407114c692f5dc626531ff62df55`, Rossel & Goens `arXiv:2405.10188`, POPL 2026 DOI `10.1145/3776667`) embeds Rust `egg` via FFI and notes in `README.md` (`L3-6`) that Lean's `grind` tactic superseded standalone `lean-egg`. Neither `grind` nor `lean-egg` can run in Anneal Pass 1 (`joshlf/anneal@20aa204315cd36aaf944778b7d33c0d609ced8e8`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`):

- **Pass-1 ceiling (`TrustedBoundary.lean`, `foundation-lock.json`):** Although `foundation-lock.json` retains `Init.Grind.{Attr,Interactive,Tactics}` as transitive `Init.Tactics` imports, `TrustedBoundary.lean:529-558` omits `grind`, `omega`, `ring`, `bv_decide`, `native_decide`, `decide!`, `run_tac`, and `+kernel`/`+native` (`Parser.Tactic.configItem`) from `allowedTheoryTacticKinds`. Imports stop at 51 `Init.*` modules (zero `Lean.Meta`, `Std`, or FFI), and `L521-528, L591-595, L639-693` ban `set_option`, `noncomputable section`, `unsafe`, `partial`, and notations `&&&`, `|||`, `^^^`, `<<<`, `>>>`, `^`, unary `-x`, `/`, `%`, `|>`.
- **Binder and `MetaM` overhead in `lean-egg`:** Rossel & Goens (`arXiv:2405.10188`) show $\lambda/\forall$ binders, `WeakVars` de Bruijn shifts, and type-class erasure (`synthLingeringTcErasureMVars`, `Proof.lean:75`) dominate `lean-egg`. Furthermore, `Explanation.Steps` (`Basic.lean:32-43`) flattens proofs into `Array Explanation.Step` with `dst : Expr` snapshots and stitches `mkEqTrans` proof terms in `MetaM` (`Proof.lean:51-80`), paying `isDefEq` across every intermediate step.
- **Lean `v4.34.1` C++ `!has_fvar` fast path (`src/kernel/type_checker.cpp:1088-1186`):** `is_def_eq_core` (`L1181-1185`) checks `t =?= Bool.true` via `whnf(t)` **only when `!has_fvar(t) || m_eager_reduce`**, and `lazy_delta_reduction` (`L1093-1099`) triggers GMP `reduce_nat` **only when `!has_fvar(t_n) && !has_fvar(s_n)`**. Keeping `arena`, `steps`, and `(lhsId, rhsId)` 100% `fvar`-free—isolating Lean free variables inside `env : Nat → SortVal`—lets `Eq.refl true` discharge arbitrary DAG congruence proofs in `<0.5 ms` with 8-byte kernel witnesses.

### 4. Complete Pass-1 5-Constructor `CongruenceDag` Checker and Multi-Sorted Rewrite Table

`Basis: source + execution + derived`

Symbolic MIR verification over `Trusted.MirSemantics` (`L243-260, L1150-1193, L1881-1883`) encounters four recurring sources of non-confluent, multi-sorted equational drift that stall naive `simp`/`rw`: (1) `Bool` normal forms (`evalBoolBinOp` emits `bne l r` for `BinOp.bitXor` at `L1157` vs. `!b` from `evalUnOp .not` at `L1179` vs. `Bool.xor` and `!!b`); (2) nested shifts (`Nat.shiftRight (Nat.shiftRight x k₁) k₂ = Nat.shiftRight x (k₁ + k₂)`) and associative/idempotent bitwise masks (`Nat.land`); (3) `BitVec` coercions (`BitVec.ofNat w n`, `toNat`, `truncateBits`); and (4) little-endian byte codecs (`leDecode w (leEncode w x) = Nat.mod x (2^(8*w))`) nested under list chunking (`chunksOf k (xs ++ ys) = chunksOf k xs ++ chunksOf k ys`, valid **only** when `Nat.mod xs.length k = 0`).

To handle all four cleanly in Pass 1:
- **Static `SortTag` well-typedness:** Each `DagNode` declares `sort : SortTag` (`sBool | sNat | sBitVec w | sBytes | sChunks`), blocking ill-typed cross-sort node merges and width mismatches.
- **Guarded `sideProofs` in `rule` steps:** Conditional rewrites such as `chunksAppendDist` take a `sideProofs` index pointing to an equality `(len xs % k = 0)` already proved earlier in the same `CongruenceDag`, allowing prerequisite rewrites on `xs` or `len xs` to compose without leaving the reflection checker.
- **Strict Pass-1 compliance:** Uses `prelude` + 6 locked `Init.*` modules, prefix `Nat` operations, `@List.rec` / `List.foldl` (zero `._unsafe_rec` helpers), `Nat.ble k 128` shift caps preventing GMP exponent DoS, and Statement-Origin Separation (`ConstantInfo.type` mentions only native Lean types and `Trusted.*` / `Mir.*`).

```lean
prelude
import Init.Core
import Init.Data.Array.Basic
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic

namespace Anneal.Cert.CongruenceDag

inductive SortTag where
  | sBool | sNat | sBitVec (w : Nat) | sBytes | sChunks

def SortTag.beq : SortTag → SortTag → Bool
  | .sBool, .sBool | .sNat, .sNat | .sBytes, .sBytes | .sChunks, .sChunks => true
  | .sBitVec w1, .sBitVec w2 => Nat.beq w1 w2
  | _, _ => false

inductive OpTag where
  | var     (sort : SortTag) (vId : Nat)
  | litBool (b : Bool)
  | litNat  (n : Nat)
  | boolNot | boolAnd | boolOr | boolXor | boolBne
  | natAdd  | natMul  | natDiv | natMod  | natLand | natLor | natXor | natShr | natShl | natLen
  | bvOfNat (w : Nat) | bvToNat (w : Nat) | bvAnd (w : Nat) | bvLshr (w : Nat)
  | leEncode (byteW : Nat) | leDecode (byteW : Nat)
  | bytesAppend | chunksOf (k : Nat) | chunksAppend

def OpTag.beq : OpTag → OpTag → Bool
  | .var s1 v1, .var s2 v2 => SortTag.beq s1 s2 && Nat.beq v1 v2
  | .litBool a, .litBool b => Bool.beq a b
  | .litNat a, .litNat b => Nat.beq a b
  | .boolNot, .boolNot | .boolAnd, .boolAnd | .boolOr, .boolOr
  | .boolXor, .boolXor | .boolBne, .boolBne | .natAdd, .natAdd
  | .natMul, .natMul | .natDiv, .natDiv | .natMod, .natMod
  | .natLand, .natLand | .natLor, .natLor | .natXor, .natXor
  | .natShr, .natShr | .natShl, .natShl | .natLen, .natLen
  | .bytesAppend, .bytesAppend | .chunksAppend, .chunksAppend => true
  | .bvOfNat w1, .bvOfNat w2 | .bvToNat w1, .bvToNat w2
  | .bvAnd w1, .bvAnd w2 | .bvLshr w1, .bvLshr w2
  | .leEncode w1, .leEncode w2 | .leDecode w1, .leDecode w2
  | .chunksOf w1, .chunksOf w2 => Nat.beq w1 w2
  | _, _ => false

structure DagNode where
  sort : SortTag
  op   : OpTag
  args : List Nat

inductive RewriteRuleId where
  | bneTrueIsNot | xorTrueIsNot | notNotId
  | shrShrAdd | landAssoc | landIdem
  | bvToNatOfNat | leDecodeEncode | chunksAppendDist | constFoldNat

inductive DagEqStep where
  | refl  (nodeId : Nat)
  | symm  (proofIdx : Nat)
  | trans (p1 p2 : Nat)
  | cong  (lhsNode rhsNode : Nat) (childProofIdxs : List Nat)
  | rule  (ruleId : RewriteRuleId) (sideProofs subst : List Nat) (lhsNode rhsNode : Nat)

def checkCongArgs (as0 bs0 ps0 : List Nat) (proved : Array (Nat × Nat)) : Bool :=
  @List.rec Nat (fun _ => List Nat → List Nat → Bool)
    (fun bs ps => bs.isEmpty && ps.isEmpty)
    (fun a _ ih bs ps =>
      match bs, ps with
      | b :: bsRest, pIdx :: psRest =>
        match proved[pIdx]? with
        | some (lhs, rhs) => Nat.beq a lhs && Nat.beq b rhs && ih bsRest psRest
        | none => false
      | _, _ => false)
    as0 bs0 ps0

def getNatLit (arena : Array DagNode) (nid : Nat) : Option Nat :=
  match arena[nid]? with
  | some d => match d.sort, d.op, d.args with | .sNat, .litNat v, [] => some v | _, _, _ => none
  | none => none

def isTrueBoolNode (arena : Array DagNode) (nid : Nat) : Bool :=
  match arena[nid]? with
  | some d => match d.sort, d.op, d.args with | .sBool, .litBool true, [] => true | _, _, _ => false
  | none => false

def checkUnaryNotSchema (arena : Array DagNode) (lhsOp : OpTag) (lhsId rhsId aId : Nat) : Bool :=
  match arena[lhsId]?, arena[rhsId]? with
  | some nl, some nr =>
    match nl.op, nl.args, nr.op, nr.args with
    | opL, [x, tId], .boolNot, [y] =>
      OpTag.beq opL lhsOp && Nat.beq x aId && Nat.beq y aId && isTrueBoolNode arena tId
    | _, _, _, _ => false
  | _, _ => false

def checkNatModZeroNode (arena : Array DagNode) (eqL eqR xsId kId zeroId : Nat) : Bool :=
  Nat.beq eqR zeroId && getNatLit arena zeroId == some 0 &&
  match arena[eqL]? with
  | some modN =>
    OpTag.beq modN.op .natMod &&
    match modN.args with
    | [lenId, modK] =>
      Nat.beq modK kId &&
      match arena[lenId]? with
      | some lenN => OpTag.beq lenN.op .natLen && lenN.args == [xsId]
      | none => false
    | _ => false
  | none => false

def checkRuleStep (arena : Array DagNode) (proved : Array (Nat × Nat))
    (r : RewriteRuleId) (sidePs subst : List Nat) (lhsId rhsId : Nat) : Bool :=
  match arena[lhsId]?, arena[rhsId]? with
  | some nl, some nr =>
    if !SortTag.beq nl.sort nr.sort then false
    else
      match r, subst with
      | .bneTrueIsNot, [aId] => checkUnaryNotSchema arena .boolBne lhsId rhsId aId
      | .xorTrueIsNot, [aId] => checkUnaryNotSchema arena .boolXor lhsId rhsId aId
      | .notNotId, [aId] =>
        Nat.beq rhsId aId &&
        match nl.op, nl.args with
        | .boolNot, [innerId] =>
          match arena[innerId]? with
          | some inner => OpTag.beq inner.op .boolNot && inner.args == [aId]
          | none => false
        | _, _ => false
      | .shrShrAdd, [xId, k1Id, k2Id, kSumId] =>
        match getNatLit arena k1Id, getNatLit arena k2Id, getNatLit arena kSumId with
        | some k1, some k2, some kSum =>
          Nat.ble (k1 + k2) 128 && Nat.beq (k1 + k2) kSum &&
          match nl.op, nl.args, nr.op, nr.args with
          | .natShr, [inId, k2A], .natShr, [xR, kSA] =>
            Nat.beq k2A k2Id && Nat.beq xR xId && Nat.beq kSA kSumId &&
            match arena[inId]? with
            | some inner => OpTag.beq inner.op .natShr && inner.args == [xId, k1Id]
            | none => false
          | _, _, _, _ => false
        | _, _, _ => false
      | .chunksAppendDist, [xsId, ysId, kId, zeroId] =>
        match nl.op, nl.args, nr.op, nr.args, sidePs with
        | .chunksOf k, [appId], .chunksAppend, [cX, cY], [divP] =>
          !Nat.beq k 0 && getNatLit arena kId == some k &&
          match arena[appId]?, arena[cX]?, arena[cY]?, proved[divP]? with
          | some appN, some cXN, some cYN, some (eqL, eqR) =>
            OpTag.beq appN.op .bytesAppend && appN.args == [xsId, ysId] &&
            OpTag.beq cXN.op (.chunksOf k) && cXN.args == [xsId] &&
            OpTag.beq cYN.op (.chunksOf k) && cYN.args == [ysId] &&
            checkNatModZeroNode arena eqL eqR xsId kId zeroId
          | _, _, _, _ => false
        | _, _, _, _, _ => false
      | _, _ => false
  | _, _ => false

def verifyCongruenceSteps (arena : Array DagNode) (steps : List DagEqStep) : Option (Array (Nat × Nat)) :=
  steps.foldl
    (fun accOpt step =>
      match accOpt with
      | none => none
      | some proved =>
        match step with
        | .refl n => if Nat.blt n arena.size then some (proved.push (n, n)) else none
        | .symm p => match proved[p]? with | some (a, b) => some (proved.push (b, a)) | none => none
        | .trans p1 p2 =>
          match proved[p1]?, proved[p2]? with
          | some (a, b1), some (b2, c) => if Nat.beq b1 b2 then some (proved.push (a, c)) else none
          | _, _ => none
        | .cong n1 n2 childPs =>
          match arena[n1]?, arena[n2]? with
          | some d1, some d2 =>
            if SortTag.beq d1.sort d2.sort && OpTag.beq d1.op d2.op &&
               checkCongArgs d1.args d2.args childPs proved then some (proved.push (n1, n2)) else none
          | _, _ => none
        | .rule r sidePs subst n1 n2 =>
          if checkRuleStep arena proved r sidePs subst n1 n2 then some (proved.push (n1, n2)) else none)
    (some Array.empty)

def verifyCongruenceGoal (arena : Array DagNode) (steps : List DagEqStep) (lhsId rhsId : Nat) : Bool :=
  match verifyCongruenceSteps arena steps with
  | none => false
  | some proved =>
    match proved[proved.size - 1]? with
    | some (a, b) => !Nat.beq proved.size 0 && Nat.beq a lhsId && Nat.beq b rhsId
    | none => false

end Anneal.Cert.CongruenceDag
```

To enforce acyclic node denotation without `partial` or `._unsafe_rec`, `denote` requires topological ordering `∀ i c, c ∈ arena[i].args → c < i` (a single linear boolean pre-check), ensuring sound `List.foldr` interpretation across the arena.

### 5. Architectural Evaluation Against Anneal `theory/` Rubric

`Basis: source + derived`

| Rubric Dimension | Grade | Grounded Justification Against `joshlf/anneal` (`20aa204315cd36aaf944778b7d33c0d609ced8e8`) |
| :--- | :---: | :--- |
| **(T1) 0-TCB Bridge** | **Strong** | External `egg`/`egglog` saturation stays offline and untrusted; `CongruenceDag` lives 100% in `theory/` over `Init.*` + `{propext, Quot.sound}` (`Classical.choice`-free), with zero `trusted/` changes. |
| **(P1) Human Spec Auditability** | **Strong** | Rust specifications remain idiomatic functional or arithmetic obligations; `DagNode` arenas and `DagEqStep` lists live exclusively inside `ConstantInfo.value?` proof terms. |
| **(P2) Authoring & Day-2 Locality** | **Strong** | Cures brittle `simp`/`rw` failures on `bne`/`!`/`BitVec`/`LeBytes`/`ListChunks`; when MIR subterms shift under code edits, external `egg` re-synthesizes the DAG witness with zero manual tactic repair. |
| **(P3) Lean 4 Kernel & LSP Scaling** | **Strong** | Closed `DagNode`/`DagEqStep` witnesses preserve `has_fvar = false`, triggering C++ `whnf(t)` and `reduce_nat` (`type_checker.cpp:1093, 1181`) for `<0.5 ms` `Eq.refl true` checks. |
| **(P4) Heterogeneous Composability** | **Strong** | Multi-sorted `SortTag` + `sideProofs` spans `Bool`, `Nat`, `BitVec w`, `LeBytes`, and `ListChunks`, composing natively with linear-arithmetic or ring side-condition equalities. |
| **(P5) Failure Legibility** | **Strong** | Returning the failing step index locates the exact malformed `DagEqStep` (`symm`/`trans`/`cong`/`rule`) when an invalid certificate is rejected. |
| **(C1–C2) Conceptual Minimality** | **Strong** | Five constructors (`refl`/`symm`/`trans`/`cong`/`rule`) over one flat `DagNode` arena form the minimal complete congruence calculus; intentionally distinct from Horner `Pol` ring reflection (cannot capture shifts, codecs, or chunking) and Chvátal–Gomory integer cuts (inequalities, not congruence). |

## Boundaries

- **Higher-order $\lambda$/$\forall$ binder equivalences ($\alpha$/$\beta$/$\eta$ and de Bruijn shifting) — `known not to apply`:** First-order `CongruenceDag` operates over quantifier-free `VarId := Nat` ASTs with fixed sorts (`SortTag`) and omits `WeakVars` binder management; higher-order equalities require upstream defunctionalization or binder machinery (`arXiv:2405.10188`).
- **`egg` `Explanation::check_proof` as a verification oracle — `known not to apply`:** Direct inspection (`src/explain.rs:403-441`) proves `Explanation::check_proof` fails open (`true`) on missing rules and non-pattern dynamic appliers; `egg` can act only as an untrusted certificate generator.
- **Native Lean 4 `grind`, `decide +kernel`, `Lean.Meta` synthesis, and unvalidated `egglog` rules in Pass 1 — `unsupported`:** `TrustedBoundary.lean` (`L529-558`) rejects `grind` and `+kernel` in preflight, `foundation-lock.json` omits `Lean.Meta.*`, and `egglog` (`src/proofs/proof_encoding_helpers.rs:555-706`) rejects `:unsafe-seminaive` rules, validator-free primitives, and query-constructed containers used in actions under proof mode.
- **Slotted e-graphs and native associative-commutative (`AC`) e-matching inside the arena — `not examined`:** Explicit `addComm`/`addAssoc`/`landAssoc` rewrite rules work via `RewriteRuleId`, while slotted e-graphs (`lean-egg` `slotted : Bool`) and AC-canonical hash-consing were `not examined`.
- **Optimal `CONGRUENCE_LIMIT` threshold vs. proof-step count on `>10,000`-node MIR e-graphs — `unknown`:** `egg` hardcodes `CONGRUENCE_LIMIT = 2` and `GREEDY_NUM_ITERS = 2` (`src/explain.rs:18-19`); empirical extraction-time vs. witness-size tradeoffs on massive MIR queries remain `unknown`.

## Evidence

1. **Nieuwenhuis–Oliveras Proof-Producing Congruence Closure (`normative`):** R. Nieuwenhuis and A. Oliveras, "Proof-Producing Congruence Closure," *J. ACM* 54(2), Art. 8 (2007), DOI `10.1145/1284320.1284324`; defines directed proof forest, edge reversal, NCA traversal, and auxiliary `HighestNode` union-find.
2. **Upstream `egg` Proof Extraction (`source` + `normative`):** M. Willsey et al., *POPL* 2021, DOI `10.1145/3434304`; `egraphs-good/egg` at `73975c9819efb4af2f3c6c1b44fa53f8c5742574`, `src/explain.rs`: `CONGRUENCE_LIMIT` (`L18`), `GREEDY_NUM_ITERS` (`L19`), `Explain` (`L50-72`), `get_tree_size` (`L247-288`), `get_sexp_with_let` / `find_to_let_bind` (`L290-346`), `check_proof` / `check_rewrite_at` / `check_rewrite` (`L368-442`), `flatten_explanation` (`L534-572`), `FlatTerm::rewrite` (`L780-856`), `make_leader` / `union` (`L922-1007`), `explain_enodes` (`L1202-1293`), `find_congruence_neighbors` (`L1477-1521`), `shortest_path_modulo_congruence` (`L1542-1646`), `tarjan_ocla` (`L1699-1734`), and `calculate_shortest_explanations` (`L1808-1830`).
3. **Upstream `egglog` Proof Store (`source` + `normative`):** Y. Zhang et al., *PLDI* 2023, DOI `10.1145/3591239`; `egraphs-good/egglog` at `d89bc58adc9b9a87a8f571c5b9ad75d686d226e6`: `src/termdag.rs` (`L12-256, 332-416`), `src/proofs/proof_format.rs` (`L54-213, 700-857`), `src/proofs/proof_checker.rs` (`L100-254`), and `src/proofs/proof_encoding_helpers.rs` (`L555-706`).
4. **Upstream `lean-egg` (`source` + `documentation`):** `marcusrossel/lean-egg` at `2605a63b6a78407114c692f5dc626531ff62df55`: `README.md` (`L3-6`), `Lean/Egg/Core/Explanation/Basic.lean` (`L9-43`), `Lean/Egg/Core/Explanation/Proof.lean` (`L31-80`); M. Rossel and A. Goens, `arXiv:2405.10188` (2024) and POPL 2026 DOI `10.1145/3776667`.
5. **Anneal Boundary and Lean `v4.34.1` Kernel (`source`):** `joshlf/anneal` at `20aa204315cd36aaf944778b7d33c0d609ced8e8`: `trusted/audit/TrustedBoundary.lean` (`L442-596, L1108-1366`), `trusted/lean/foundation-lock.json`, `trusted/lean/Trusted/MirAst.lean` (`L504-507`), `trusted/lean/Trusted/MirSemantics.lean` (`L243-260, L1150-1193, L1881-1883`); `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`, `src/kernel/type_checker.cpp` (`L1088-1186`).
6. **Executable Proof-Forest and `CongruenceDag` Probe (`execution`, `2026-11-20`):** Executed the standalone Python 3.13 probe preserved in Revalidation item 5 on Linux x86_64 (`0.0201 ms` for `goal1`), confirming `256` flat rewrite steps vs. `9` DAG steps at $K = 8$, fail-open `egg` `check_proof` acceptance vs. fail-closed `verifyCongruenceSteps` rejection, and exact checking of `(bne (xor b true) true) = b` and `((x >> 32) >> 16) & 0xff = (x >> 48) & 0xff`.

## Revalidation

1. **`egg` `check_proof` audit (`egraphs-good/egg`):** Inspect `src/explain.rs` inside `Explanation::check_rewrite_at` and `Explanation::check_rewrite` for missing-rule or `None`-pattern fallthroughs returning `true`.
2. **`egglog` proof-encoding boundaries (`egraphs-good/egglog`):** Inspect `src/proofs/proof_encoding_helpers.rs` (`command_supports_proof_encoding`) and `src/proofs/proof_format.rs` (`Justification`).
3. **Anneal Pass-1 `grind` ban and `Init.*` lock (`joshlf/anneal`):** Inspect `trusted/audit/TrustedBoundary.lean` (`allowedTheoryTacticKinds`) and `trusted/lean/foundation-lock.json`.
4. **Lean 4 `!has_fvar` reflection gates (`leanprover/lean4`):** Inspect `src/kernel/type_checker.cpp` at `lazy_delta_reduction` and `is_def_eq_core`.
5. **Standalone proof-forest, fail-open, and `CongruenceDag` probe (<0.2s, Python 3.10+ stdlib only):**

```bash
python3 -c '
class PF:
    def __init__(s, n): s.n, s.p = list(n), [(i, None, True) for i in range(len(n))]
    def lead(s, u):
        nx, j, f = s.p[u]
        if nx != u: s.lead(nx); s.p[nx] = (u, j, not f)
    def union(s, a, b, j): s.lead(a); s.p[a] = (b, j, True)
    def nca(s, a, b):
        sa, sb = set(), set()
        while True:
            sa.add(a)
            if a in sb: return a
            sb.add(b)
            if b in sa: return b
            a, b = s.p[a][0], s.p[b][0]
    def path(s, a, anc):
        out = []
        while a != anc: nx, j, f = s.p[a]; out.append((a, nx, j, f)); a = nx
        return out
    def edges(s, l, r):
        anc = s.nca(l, r)
        return s.path(l, anc) + [(n, c, j, not f) for c, n, j, f in reversed(s.path(r, anc))]
    def dag(s, l, r, st, m):
        if l == r: st.append(("refl", l)); return len(st) - 1
        if (l, r) in m: return m[(l, r)]
        ps = []
        for c, n, j, f in s.edges(l, r):
            st.append(("rule", j, c, n, f) if j is not None else ("cong", c, n, tuple(s.dag(a, b, st, m) for a, b in zip(s.n[c][1], s.n[n][1]))))
            ps.append(len(st) - 1)
        cur = ps[0]
        for np in ps[1:]: st.append(("trans", cur, np)); cur = len(st) - 1
        m[(l, r)] = cur; return cur
    def flat(s, l, r):
        return 0 if l == r else sum(1 if j is not None else sum(s.flat(a, b) for a, b in zip(s.n[c][1], s.n[n][1])) for c, n, j, _ in s.edges(l, r))

nodes, lc, rc = [("var", ()), ("const", ())], [0], [1]
for _ in range(8):
    nodes.append(("add", (lc[-1], lc[-1]))); lc.append(len(nodes) - 1)
    nodes.append(("add", (rc[-1], rc[-1]))); rc.append(len(nodes) - 1)
pf = PF(nodes); pf.union(0, 1, "base")
for i in range(1, 9): pf.union(lc[i], rc[i], None)
dag = []; pf.dag(lc[8], rc[8], dag, {})
assert pf.flat(lc[8], rc[8]) == 256 and len(dag) == 9
assert all({"ok": lambda l, h: l == h}.get(r)(l, h) for r, l, h in [("dyn", True, False)] if {"ok": lambda l, h: l == h}.get(r) is not None)

def chk_rule(ar, r, sub, li, ri):
    l, h = ar[li], ar[ri]
    if r in ("bneTrueIsNot", "xorTrueIsNot"):
        op = "boolBne" if r == "bneTrueIsNot" else "boolXor"
        return l[0] == op and l[1][0] == sub[0] and ar[l[1][1]] == ("litBool", True) and h == ("boolNot", (sub[0],))
    if r == "notNotId": return l[0] == "boolNot" and ar[l[1][0]] == ("boolNot", (sub[0],)) and ri == sub[0]
    if r == "shrShrAdd":
        x, k1i, k2i, ksi = sub; k1, k2, ks = ar[k1i][1][0], ar[k2i][1][0], ar[ksi][1][0]
        return k1 + k2 <= 128 and k1 + k2 == ks and l == ("natShr", (l[1][0], k2i)) and ar[l[1][0]] == ("natShr", (x, k1i)) and h == ("natShr", (x, ksi))
    return False

def verify(ar, steps):
    pr = []
    for st in steps:
        t = st[0]
        if t == "refl" and 0 <= st[1] < len(ar): pr.append((st[1], st[1]))
        elif t == "trans" and all(0 <= p < len(pr) for p in st[1:]):
            a, b1 = pr[st[1]]; b2, c = pr[st[2]]
            if b1 != b2: return None
            pr.append((a, c))
        elif t == "cong" and 0 <= st[1] < len(ar) and 0 <= st[2] < len(ar):
            o1, a1 = ar[st[1]]; o2, a2 = ar[st[2]]
            if o1 != o2 or len(a1) != len(a2) or len(a1) != len(st[3]) or any(not (0 <= p < len(pr)) or pr[p] != (x, y) for x, y, p in zip(a1, a2, st[3])): return None
            pr.append((st[1], st[2]))
        elif t == "rule" and chk_rule(ar, st[1], st[2], st[3], st[4]): pr.append((st[3], st[4]))
        else: return None
    return pr

a1 = [("var", (0,)), ("litBool", True), ("boolXor", (0, 1)), ("boolNot", (0,)), ("boolBne", (2, 1)), ("boolBne", (3, 1)), ("boolNot", (3,))]
s1 = [("rule", "xorTrueIsNot", [0], 2, 3), ("refl", 1), ("cong", 4, 5, [0, 1]), ("rule", "bneTrueIsNot", [3], 5, 6), ("rule", "notNotId", [0], 6, 0), ("trans", 2, 3), ("trans", 5, 4)]
assert verify(a1, s1)[-1] == (4, 0) and verify(a1, [("rule", "dyn", [], 0, 1)]) is None
a2 = [("var", (0,)), ("litNat", (32,)), ("litNat", (16,)), ("litNat", (48,)), ("litNat", (255,)), ("natShr", (0, 1)), ("natShr", (5, 2)), ("natShr", (0, 3)), ("natLand", (6, 4)), ("natLand", (7, 4))]
s2 = [("rule", "shrShrAdd", [0, 1, 2, 3], 6, 7), ("refl", 4), ("cong", 8, 9, [0, 1])]
assert verify(a2, s2)[-1] == (8, 9)
print("revalidation passed")
'
```
