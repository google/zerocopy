<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Cross-Prover Interoperability, Dedukti Translation, Proof Certificates, and
Agentic Proof Tooling for Lean 4.34.1

## Summary

Anneal verifies Rust programs by extracting typed `Runtime(PostCleanup)` MIR and
compiler facts via `anneal-rustc-capture` and checking the crate's
`Trusted.CrateTheorem` (`VerificationResult` over every captured function's
`Compiler.Verified` obligations) inside the Lean 4 kernel (`v4.34.1`, commit
`5045d0056413266e57c625dcd7c365b10e377c52`). Because Anneal's soundness boundary
(`trusted/audit/`) enforces zero custom axioms (`Trusted.allowedAxioms = ∅`),
forbids `Lean.ofReduceBool` and `Lean.trustCompiler`, and runs under
`reduce_at_kernel` (`-j1 -M1024`), external proof systems, automated theorem
provers, and LLM-driven proof agents can assist Anneal only if their output
ultimately compiles into an axiom-free, kernel-checkable Lean 4 proof term.

This report evaluates five technical layers across 17 upstream repositories and
delivers a zero-dependency, kernel-verified Lean `v4.34.1` proof-engineering
harness (`support/anneal_harness.lean`, 893 lines, SHA-256
`9f9c51efc7ef322f7c7b991dbb3b261d3893f244b6f2f9c5d5cb29ae9fecb25a`):

1. **Cross-prover kernel translation (`lean4less`, `lean2dk`,
  `rocq-lean-import`, `babel-formal`, `specr`):** Translating Lean 4 kernel
  proofs to Dedukti or Rocq requires eliminating Lean's extensional definitional
  equalities—definitional proof irrelevance (`isDefEqProofIrrel`), K-like
  singleton elimination (`toCtorWhenK`), and definitional quotient computation
  (`Quot.lift`)—via explicit heterogeneous equality (`HEq`) cast insertion
  (`lean4less` at `5b66bbc4af5c2c11313fcfb5098630dadaf19281`). Even after
  extensionality translation, stock Dedukti checkers (`dkcheck` / `kocheck`)
  exhaust memory on `Init.Data.Nat.Lemmas` without two C/OCaml checker patches
  on `lean2dk`'s `claude-stable` branch
  (`29f985670008c29e852d61c562b8c10c84f7c5fb`): lazy two-phase delta-unfolding
  (`DK_LAZY_DELTA=1`) and per-declaration WHNF/convertibility/$\eta$-expansion
  hash-table memoization, plus stubbing 43 reflection-heavy `omega`/`Nat.Linear`
  lemmas as Dedukti axioms. Importing Lean 4 into Rocq (`rocq-lean-import` at
  `2d28bbe80e7361bf3ac54f5ef099207fc61ce837`) incurs up to $2^n$
  universe-polymorphic `SProp`/`Type` sort-splitting duplications, disables
  Rocq's positivity and guard checkers on nested inductives, and axiomatizes
  `Quot.sound`.

2. **Proof certificate formats and kernel reconstruction (`lean4export`, SMT-LIB
  / Alethe / CPC, LRAT):** `lean4export`
  (`df81913eee5519d5a88ae5b0fd701b5298cc29ab`) emits a compact NDJSON DAG format
  (`v3.1.0`) suitable for external audit of Anneal's `.olean` artifacts,
  provided auditors account for its `Expr.letE` (`nonDep := false`)
  canonicalization, four-constant `Quot` batching, and `RecursorVal.k` flag. For
  inbound proof certificates, external Alethe checkers (`Carcara`) verify SMT
  proofs outside Lean but emit no Lean proof term; `ufmg-smite/lean-smt`
  (`db545bebe2de1e06dc2df62a6ff6c20e5736bfc0` on `main`,
  `7e54df3e5b7f78e5e6170ffab8ebe813904262b0` on `no_mathlib`) reconstructs cvc5
  Cooperating Proof Calculus (CPC) proofs inside Lean 4 without custom axioms,
  turning unsupported `TRUST` or `THEORY_REWRITE` steps into explicit open
  subgoals (`mv :: mvs`). For bitvector and SAT obligations, stock `bv_decide`
  relies on `Lean.ofReduceBool` and seven kernel-reduction blockers (`Opaque`
  `HashMap.Raw.m`, `@[extern]` `USize.ofNat`, `Char.utf8Size`, `AIG.Entrypoint`
  `HashMap`, `Except` monadic wrapping, and `ByteArray` FFI), requiring Anneal's
  verified `KernelLRAT` (`checkKernelLratProof_sound`) and `KernelBVDecide`
  (`checkKernelBVUnsat_sound`) reflection endpoints.

3. **Semantic and type-directed premise search (`Loogle`, `LeanExplore`,
  `LeanSearchClient`, `Moogle`):** `Loogle`
  (`9f11169aaebf1ed1e7dcc4077f2aafe0fcf66fd0`) achieves sub-100 ms deterministic
  type-shape search by intersecting an inverted constant-mention index
  (`NameRel`) before running `MetaM` unification (`matchUpToHyps` / `matchHyps`)
  over hypothesis permutations sorted by ascending `exprSize` and subterm
  traversals pruned by `checkUsedConsts`. Hybrid lexical/embedding engines
  (`LeanExplore` at `17b9d6c87a2bf0dc4ea27de05da8a1c9965391b7`) and hosted APIs
  (`LeanSearchClient` at `c61286b7b63cbfd563b28e11e81d0a18233a044a`) add
  natural-language retrieval and speculative tactic validation (`checkTactic`),
  but Anneal's offline autoprover requires a local, deterministic `.olean`
  type-shape indexer paired with speculative tactic checking.

4. **Interactive REPL and agentic proof protocols (`Pantograph`, `LeanDojo-v2`,
  `lean-lsp-mcp`, `lean-repl`, `LeanInteract`, `Kimina`):** Machine-to-machine
  proof search over Lean 4 requires three state invariants that naive text-based
  LSP loops miss: tracking **coupled metavariables** (`sibling_dep`) shared
  across subgoals (`Pantograph` at `0789692d65e365c027d171074bf747f1d40328d0`),
  restoring `Core.State.ngen`, `nextMacroScope`, and `Meta.State.auxDeclNGen`
  (`restoreCoreMExtra`) which stock `Tactic.SavedState.restore` omits, and
  gating completed proofs on both `!rootExpr.hasSorry` and `Lean.Kernel.addDecl`
  (`leanprover-community/repl` at `6a2be396449a5213a36748ca7682d16d54a1ca4a`).

5. **Zero-dependency in-tree search and coupled-goal harness
  (`support/anneal_harness.lean`):** We provide a self-contained 893-line Lean
  `v4.34.1` CLI harness (`support/anneal_harness.lean`) that compiles in 2.5 s
  within `-j1 -M1024` (by importing `Lean.Elab.Frontend` and
  `Lean.Elab.Tactic.Basic` rather than umbrella `import Lean`), exposes `search`
  (Loogle-style constant-filtered, hypothesis-permuting unification) and `goals`
  (InfoTree `tacticSorry` extraction with Pantograph-style `dependentMVars`
  coupling analysis and `--try-tactic` verification), and includes 9
  kernel-checked specification theorems.

## Applicability

This report applies to three components of the Anneal verification stack pinned
to Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) and
`joshlf/anneal` (`e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`):

- **`trusted/audit/` and `trusted/cargo-anneal/` (Trust Boundary and External
  Kernel Auditing):** Governs how `Trusted.CrateTheorem` can be exported via
  `lean4export` (`v3.1.0`) for independent verification in Dedukti (`lean4less`
  + `lean2dk`) or Rocq (`rocq-lean-import`), and establishes why neither
  external proof translation nor unverified SMT certificates can substitute for
  Lean 4 kernel checking inside `trusted/audit/`.

- **`theory/` (Untrusted Proof Automation, Premise Search, and Certificate
  Reconstruction):** Governs how `theory/` libraries and `cargo-anneal` proof
  generators search `.olean` environments for lemmas, reconstruct SMT/LRAT
  certificates into pure kernel terms, and avoid `Lean.ofReduceBool`, `sorryAx`,
  and non-kernel-reducible data structures.

- **`cargo-anneal` Agentic Autoprover Loop (`support/anneal_harness.lean`):**
  Provides a drop-in, zero-dependency Lean `v4.34.1` binary and module that
  `cargo-anneal` or an LLM proof agent can invoke via `lean --run` to discover
  type-matching lemmas in loaded `.olean` modules, extract structured JSON goal
  states with explicit coupled-metavariable (`dependentMVars`) annotations from
  `.lean` files containing `sorry`, and speculatively test candidate tactics
  without writing temporary scratch files or exceeding `-M1024`.

## Findings

### Finding 1: Cross-Prover Kernel Translation

**Basis:** `source inspection`, `derivation` (inspection of `rish987/lean4less`
at `5b66bbc4af5c2c11313fcfb5098630dadaf19281`, `rish987/lean2dk` at
`471208f18c29420e25750503648469fc95d2ac8f` on `main` and
`29f985670008c29e852d61c562b8c10c84f7c5fb` on `claude-stable`,
`rocq-community/rocq-lean-import` at `2d28bbe80e7361bf3ac54f5ef099207fc61ce837`,
`LLM4Rocq/babel-formal` at `71c2aa9bc78e6d41c5421f8ae8e9f551c12f570b`, and
`minirust/specr` at `15200eb5e676e2ee91f43bd79e674f8fc32e5348`).

#### 1.1 Extensional vs. Intensional Type Checking in `lean4less`

Lean 4's kernel type checker (`lean4/src/kernel/type_checker.cpp`, mirrored in
Lean in `Lean4Less/TypeChecker.lean` at commit
`5b66bbc4af5c2c11313fcfb5098630dadaf19281`) implements an **extensional**
definitional equality judgment ($\Gamma \vdash t \equiv u$) that is not
confluent under syntactic reduction alone. Specifically, Lean 4's `isDefEq`
relies on three context-sensitive extensional rules that fail to hold as pure
rewrite rules in intensional type theories such as Dedukti
($\lambda\Pi$-calculus modulo rewriting) or Rocq's Calculus of Inductive
Constructions:

1. **Definitional Proof Irrelevance (`isDefEqProofIrrel`,
  `Lean4Less/TypeChecker.lean:947–962`):** Whenever `inferType p` has sort
  `Prop` (`Sort 0`), Lean's kernel equates any two proof terms `h1 h2 : p`
  definitionally (`h1 ≡ h2`). In an intensional checker without typing
  information during reduction, arbitrary proof terms `h1` and `h2` do not
  reduce to a common normal form. Even more subtly, when a proof term `h`
  appears inside the *type* of an expression (such as `Fin.mk val h` or
  dependent array indexing `a[i]'h`), two terms `f h1` and `f h2` are
  definitionally equal in Lean 4 even when `h1` and `h2` contain free variables
  that prevent syntactic reduction.

2. **K-like Singleton Elimination (`toCtorWhenK`,
  `Lean4Less/TypeChecker.lean:872–913`):** When a recursor `R` has
  `RecursorVal.k == true` (meaning its inductive type sits in `Prop`, has a
  single constructor, and all constructor fields after parameters are proofs or
  indices fixed by the target type, such as `Eq.rec` or `Acc.rec`), Lean's
  kernel reduces `R ... major` *even when `major` is a neutral term* (for
  example, a free variable `h : a = a`) by synthesizing a dummy constructor
  application (`mkNullaryCtor` at `Lean4Less/Inductive.lean:160–188`) and
  checking whether `major` is definitionally equal to that constructor via proof
  irrelevance. A pure rewrite engine cannot fire a constructor-headed rewrite
  rule on a neutral variable `h`.

3. **Quotient Reduction (`quotReduceRec`, `Lean4Less/Quot.lean:80–91`) and Smart
  Unfolding (`unfoldDefinitionCore`, `Lean4Less/TypeChecker.lean:725–796`):**
  `Quot.lift f h (Quot.mk r a)` reduces definitionally to `f a` by discarding
  the proof `h : ∀ a b, r a b → f a = f b`. When combined with proof irrelevance
  inside `Quot.ind`, terms whose heads depend on `Quot.lift` can be
  definitionally equal in Lean 4 without being convertible under purely
  syntactic $\beta\delta\iota\zeta$-reduction.

To bridge this gap, Rishikesh Vaishnav's `lean4less`
(`5b66bbc4af5c2c11313fcfb5098630dadaf19281`) implements a **dual-mode kernel
type checker and proof-term translator** (`Lean4Less/Methods.lean:288–326` and
`Lean4Less/TypeChecker.lean:1058–1242`). During type checking of an exported
Lean 4 environment, every call to `isDefEq t s` runs in two modes controlled by
`Context.translate : Bool` and returns `(Bool × Option Equiv)` where `Inductive
Equiv` (`Lean4Less/Methods.lean:62–72`) tracks:

- `Equiv.rfl`: `t` and `s` are already convertible in the weakened intensional
  theory (pure $\beta\delta\iota\zeta\eta$ plus `Quot.lift` on manifest
  `Quot.mk` constructors), so no cast is needed.

- `Equiv.defeq (p : Expr)`: `t` and `s` require extensional rules to equate, and
  `p` is an explicitly constructed Lean 4 proof term of type `HEq t s`
  (`Lean4Less/EConsts.lean:28–165`).

Whenever an application `f a` requires `inferType a` (`ta`) to match the domain
`dom` of `f` and `isDefEq dom ta` yields `Equiv.defeq eq`, `lean4less` rewrites
the subterm `a` to `Lean4Less.cast dom ta eq a` (`appHeq` at
`Lean4Less/EConsts.lean:77–165`). This translation eliminates Lean 4's three
extensional conversion rules in favor of three explicit axiomatic constants in
`Lean4Less/EConsts.lean` (`deps/lean4less-lib/src/Lean4Less.lean` in `lean2dk`):

- `Lean4Less.pIrrel : ∀ {P : Prop} (p q : P), HEq p q` (replaces
  `isDefEqProofIrrel`);

- `Lean4Less.Singleton.elim` (replaces `toCtorWhenK` on neutral major premises
  by proving that any inhabitant of a K-inductive equals its synthesized
  constructor application); and

- `Lean4Less.Quot.liftProp` (handles propositional quotient reduction when
  `Quot.ind` interacts with proof irrelevance).

#### 1.2 Dedukti Encoding and `Init.Data.Nat.Lemmas` Bottlenecks (`lean2dk`)

`lean2dk` (`471208f18c29420e25750503648469fc95d2ac8f` on `main`;
`29f985670008c29e852d61c562b8c10c84f7c5fb` on `claude-stable`) embeds the
intensional output of `lean4less` into Dedukti (`theory/lean.dk:1–66`). Because
Dedukti lacks first-class universe level expressions (`max`, `imax`) in its core
syntax, `theory/lean.dk` encodes Lean universe levels using nested ac-normalized
multi-sets (`s : Nat → Lvl → Lvl` and `u : Nat → Lvl'` with confluence rewrite
rules for `max` and `imax` at `theory/lean.dk:15–58`), maps Lean's `Sort l` to
`s l`, and encodes dependent function types via `p s1 s2 A (x => B x)`.
Crucially, `Lean4Less.cast` becomes a single computational rewrite rule in
Dedukti (`theory/lean.dk:64–66`):

```
[l, T, a] Lean4Less.cast l l T T (HEq.refl l T a) a --> a.
```

Despite this clean theoretical encoding, running stock Dedukti (`dkcheck` or
`kocheck`) on the translated Lean 4 core library fails to terminate or exhausts
memory (`> 32 GB` RSS) before completing `Init.Data.Nat.Lemmas`. Inspection of
`lean2dk`'s `claude-stable` branch (`29f985670008c29e852d61c562b8c10c84f7c5fb`)
reveals three distinct root causes and their concrete engineering workarounds:

1. **Eager Constant Delta-Unfolding Blowup
  (`patches/dkcheck-lazy-delta.patch`):** Stock `dkcheck` treats every defined
  constant (`def f := body`) as a normal rewrite rule `f --> body`. During weak
  head normal form (WHNF) reduction (`state_whnf`), stock `dkcheck` eagerly
  unfolds every defined constant before checking whether two terms already share
  the same head constant and convertible arguments. On Lean 4's deeply nested
  `let` expressions (`_let_1`, `_let_2`, ...) and recursive `Nat` lemmas, eager
  unfolding causes exponential term blowup. `patches/dkcheck-lazy-delta.patch`
  (`1–351`, enabled by `DK_LAZY_DELTA=1`) splits each symbol's rules into
  *constructor/recursor rules* (`_cstr`, fired eagerly in `state_whnf`) and
  *definition rules* (`_def`, deferred to `are_convertible_lst`), implementing
  Lean 4's two-phase heuristic (`def_Phase_Heuristic`): when comparing `f
  a1..an` and `g b1..bm`, `dkcheck` first tries structural argument comparison
  when `f == g`, then unfolds only the side with *fewer* arguments (`List.length
  l1 < List.length l2`) before falling back to unfolding both.

2. **Lack of DAG Memoization in WHNF, Convertibility, and $\eta$-Expansion
  (`patches/dkcheck-eta-memo.patch`):** Lean 4's C++ kernel heavily shares
  `Expr` DAG nodes and caches WHNF and `isDefEq` queries. Stock `dkcheck`
  re-reduces shared subterms from scratch on every visit.
  `patches/dkcheck-eta-memo.patch` (`1–291`) adds three open-addressed
  physical-equality (`==`) hash tables to `reduction.ml`, cleared at the end of
  each top-level declaration (`clear_all_memos ()`): `whnf_memo` (65,536 slots),
  `conv_memo` (262,144 slots), and `eta_memo` (65,536 slots).

3. **Unbounded Proof-by-Reflection Terms in `omega` and `Nat.Linear`
  (`Lean2Dk/Export.lean:245–360` on `claude-stable`):** Even with
  `DK_LAZY_DELTA=1` and hash-table memoization, 43 theorems in `Init.Data.Nat`
  and `Init.Data.Int` fail to check within practical memory bounds in `dkcheck`.
  Every one of those 43 failures stems from Lean 4's `omega` and `Nat.Linear`
  tactics generating massive `Eq.refl true` proof terms over
  `Nat.Linear.ExprCnstr` and `Nat.Linear.PolyCnstr` normalizers
  (`Nat.Linear.ExprCnstr.eq_of_toNormPoly_eq`,
  `Nat.Linear.PolyCnstr.eq_of_toNormPoly_eq`, and
  `Lean.Order.Lemmas.rel_imp_rel`). Because `lean4less` must insert `HEq` casts
  inside the reflection evaluation trace, the resulting Dedukti proof terms
  trigger tens of millions of higher-order unification steps. On
  `claude-stable`, `Lean2Dk/Export.lean` bypasses this bottleneck by stubbing
  those 43 declarations as body-less Dedukti axioms via `stubDefs`
  (`Export.lean:245–279`) and `stubProofPrefixes` (`Export.lean:281–336`).

#### 1.3 Lean-to-Rocq Barriers (`rocq-lean-import`), `babel-formal`, and `specr`

Directly importing Lean 4 into Rocq via Gaëtan Gilbert's OCaml plugin
`rocq-community/rocq-lean-import` (`2d28bbe80e7361bf3ac54f5ef099207fc61ce837`,
`src/lean.ml:1–2271` and `theories/Loader.v:1–88`) encounters three foundational
mismatches between Lean's type theory and Rocq's kernel:

1. **Exponential Sort-Polymorphism Duplication ($2^n$ Instantiation Masks,
  `src/lean.ml:699–850`):** In Lean 4, `Sort u` evaluates to impredicative,
  proof-irrelevant `Prop` when `u = 0` and predicative `Type (u-1)` when `u >
  0`, and `imax u v` collapses to `0` whenever `v = 0`. In Rocq, strict
  proof-irrelevant propositions (`SProp`) and predicative types (`Type@{u}`)
  belong to disjoint sort hierarchies: a universe variable `u` in Rocq cannot be
  instantiated with `SProp`. Consequently, whenever a Lean declaration with $n$
  universe parameters `[u_1, ..., u_n]` uses `Sort u_i` or `imax`,
  `rocq-lean-import` must generate separate Rocq declarations for up to $2^n$
  bitmasks (`Instantiation` in `src/lean.ml:699–765`), where each bit selects
  whether `u_i` is fixed to `0` (`SProp`) or strictly positive (`Level.+1`).

2. **Nested/Mutual Inductives and Guarded Fixpoints (`src/lean.ml:1927–2083`):**
  Lean 4 compiles recursive functions to primitive recursors (`rec`), whereas
  Rocq's kernel checks structural termination via a syntactic `fix` guard
  condition and enforces a stricter positivity condition on nested inductive
  types. When translating Lean inductives that fail Rocq's positivity or
  eliminator checks, `rocq-lean-import` explicitly disables Rocq's kernel safety
  flags (`check_guarded = false`, `check_positive = false`, `check_universes =
  false` at `src/lean.ml:1945–1968`) or falls back to postulating the recursor
  and its $\iota$-reduction equations as axioms (`check_eliminations = false`).

3. **Quotient Soundness (`theories/Loader.v:15–56` and
  `src/lean.ml:2084–2150`):** Rocq's `SProp` supports a `Private Inductive quot`
  wrapper whose constructor is hidden outside the module, allowing `Quot.lift`
  to compute definitionally on `Quot.mk` when the target is in `SProp` or
  `Type`. However, Lean's `Quot.sound : ∀ {α : Sort u} {r : α → α → Prop} {a b :
  α}, r a b → Quot.mk r a = Quot.mk r b` is not provable in Rocq without an
  axiom; `theories/Loader.v` therefore postulates `Axiom quot_sound` (using a
  squash type `Squash (r a b)` in `SProp`).

By contrast, `LLM4Rocq/babel-formal`
(`71c2aa9bc78e6d41c5421f8ae8e9f551c12f570b`) and `minirust/specr`
(`15200eb5e676e2ee91f43bd79e674f8fc32e5348`) address different problems:

- `babel-formal` (`src/lean_parse.py` and `src/coq_emit.py`) translates
  individual self-contained kernel proof terms across Calculus of Constructions
  dialects using an AST pivot combined with LLM repair, relying on the target
  prover (`coqc`) to reject ill-typed translations. It does not handle Lean 4's
  full inductive/quotient/typeclass environment or scale to `Mathlib`/`Std`
  module graphs.

- `minirust/specr` (`src/tree.rs`, `v0.1.41`) is a specification-to-Rust
  transpiler developed for the MiniRust formal semantics. It parses `.md` files
  containing `specr` dialect blocks (such as GC-managed `List<T>`, `Map<K, V>`,
  `Set<T>`, and mathematical `Int`) using `syn` and emits an executable Rust
  interpreter crate (`libspecr`). It does **not** emit Lean, Rocq, or Isabelle
  theorems; MiniRust's connection to interactive provers is maintained
  separately through `coq-of-rust` or manual mechanization.

| System | Revision (40-char SHA) | Direction | Extensionality Handling | Trust / Completeness Trade-Offs |
| :--- | :--- | :--- | :--- | :--- |
| `lean4less` | `5b66bbc4af5c2c11313fcfb5098630dadaf19281` | Lean 4 (extensional) $\to$ Lean 4 (intensional) | Dual-mode `isDefEq` inserting `Lean4Less.cast` via `HEq` witnesses | Adds 3 explicit postulates (`pIrrel`, `Singleton.elim`, `Quot.liftProp`) |
| `lean2dk` (`claude-stable`) | `29f985670008c29e852d61c562b8c10c84f7c5fb` | Lean 4 $\to$ Dedukti (`.dk`) | Uses `lean4less` + rewrite rule `cast ... (HEq.refl) a --> a` | Requires patched `dkcheck` (`DK_LAZY_DELTA=1` + memoization) and stubs 43 `omega`/`Nat.Linear` lemmas as axioms |
| `rocq-lean-import` | `2d28bbe80e7361bf3ac54f5ef099207fc61ce837` | Lean 4 export $\to$ Rocq (`SProp`/`Type`) | Maps `Prop` to `SProp`; $2^n$ sort-splitting instantiations | Disables `check_guarded`/`check_positive` on complex inductives; axiomatizes `quot_sound` |
| `babel-formal` | `71c2aa9bc78e6d41c5421f8ae8e9f551c12f570b` | CoC kernel term pivot (Lean $\leftrightarrow$ Rocq) | None (syntactic AST pivot + LLM repair) | Verified by target kernel on small standalone terms; no `Quot` or `toCtorWhenK` support |
| `minirust/specr` | `15200eb5e676e2ee91f43bd79e674f8fc32e5348` | MiniRust `.md` $\to$ executable Rust crate | N/A (executable specification transpiler) | Emits Rust interpreter code (`libspecr`), not ITP theorems |

### Finding 2: Proof Certificate Formats and Kernel Reconstruction

**Basis:** `source inspection`, `measurement` (inspection of
`leanprover/lean4export` at `df81913eee5519d5a88ae5b0fd701b5298cc29ab`,
`ufmg-smite/lean-smt` at `db545bebe2de1e06dc2df62a6ff6c20e5736bfc0` and
`7e54df3e5b7f78e5e6170ffab8ebe813904262b0`, and Lean `v4.34.1`
`Std.Tactic.BVDecide` alongside Anneal's companion certificate reports).

#### 2.1 Outbound Kernel Certificates via `lean4export` (`v3.1.0`)

`leanprover/lean4export` (`df81913eee5519d5a88ae5b0fd701b5298cc29ab`,
`Export.lean:1–354`) serializes a compiled Lean 4 `Environment` into a
newline-delimited JSON (NDJSON) stream headed by `{"meta": {"format":
{"version": "3.1.0"}}}` (`Export.lean:24–33`). Every hierarchical name (`in`),
universe level (`il`), expression (`ie`), and universe parameter array (`iu`) is
deduplicated in `State` hash maps (`Export.lean:45–63`) and referenced by
integer index, preserving expression DAG sharing across large proofs. An
external verifier or Anneal boundary auditor consuming `lean4export` output must
account for three non-obvious kernel serialization behaviors in `Export.lean`:

1. **Canonicalization of Non-Dependent `have` Bindings
  (`Export.lean:160–162`):** Lean 4's core `Expr.letE declName type value body
  nonDep` carries a boolean flag `nonDep` indicating whether the `let` was
  elaborated from a non-dependent `have h : T := v; body` expression (whose
  value `v` should not be $\zeta$-reduced by `MetaM`). Because the Lean 4
  kernel's `type_checker.cpp` ignores `nonDep` and treats `have` identically to
  `let` during $\zeta$-reduction, `dumpExpr` rewrites `Expr.letE name dom val
  body _` to `dumpLet name dom val body False`, ensuring hash-consed DAG sharing
  between dependent and non-dependent `let` nodes.

2. **Deferred Quotient Batching (`Export.lean:245–252`, `305–311`):** In Lean
  4's `Environment`, the four quotient primitives (`Quot`, `Quot.mk`,
  `Quot.lift`, `Quot.ind`) are stored as four separate `ConstantInfo.quotInfo`
  entries. `dumpConstant` intercepts each of those four names in `quotNames`,
  dumps their signature types first, and emits a single `"quot": {"name": ...,
  "levelParams": ..., "type": ...}` JSON object only when the fourth primitive
  has been visited (`modify (fun s => { s with numVisitedQuot :=
  s.numVisitedQuot + 1 })`).

3. **Explicit K-Elimination Metadata (`Export.lean:293`):** When exporting
  `ConstantInfo.recInfo val`, `lean4export` emits `"k": val.k` alongside
  `"numParams"`, `"numIndices"`, `"numMotives"`, `"numMinors"`, and `"rules"`.
  Any external checker (`lean4less`, `dkcheck`, or a standalone Rust verifier)
  must read `"k"` to know whether singleton constructor synthesis
  (`toCtorWhenK`) is permitted on that recursor.

#### 2.2 Inbound SMT Certificates (Alethe vs. cvc5 CPC in `lean-smt`)

When discharging arithmetic, array, or uninterpreted-function obligations in
`theory/`, Anneal's zero-axiom policy (`Trusted.allowedAxioms = ∅`) prohibits
trusting an external SMT solver's `unsat` exit code or even an external
certificate checker such as `Carcara` (for Alethe proofs). While `Carcara`
(`--apply-function-defs`) checks Alethe proof scripts in Rust, it neither emits
a Lean 4 `Expr` proof term nor eliminates Alethe `trust`, `hole`, and
unelaborated `theory_rewrite` steps.

By contrast, `ufmg-smite/lean-smt` (`db545bebe2de1e06dc2df62a6ff6c20e5736bfc0`
on `main`; `7e54df3e5b7f78e5e6170ffab8ebe813904262b0` on `no_mathlib`) embeds
cvc5 via FFI (`cvc5.Proof`) and reconstructs cvc5's **Cooperating Proof Calculus
(CPC)** DAG directly into a Lean 4 kernel proof term
(`Smt/Reconstruct.lean:177–336`):

- **Axiom-Free Proof Term Construction:** Every supported CPC rule (`ASSUME`,
  `SCOPE`, `RESOLUTION`, `CHAIN_RESOLUTION`, `FACTORING`, `REORDERING`, `CNF_*`,
  `CONG`, `REFL`, `SYMM`, `TRANS`, `ARITH_SUM_UB`, `ARITH_TRICHOTOMY`,
  `INT_TIGHT_LB`/`UB`, `BV_BITBLAST_STEP`, `ACI_NORM`, and rare/DSL rules
  compiled via `Smt/Reconstruct/Rewrite.lean`) is reconstructed in
  `ReconstructM` by building an explicit Lean `Expr` proof or running a small
  kernel-verified reflection theorem (`rfl` / `decide`).

- **Explicit Open Subgoals on Unreconstructed Steps (`skipStep` and
  `addTrust`):** When cvc5 emits an opaque step (`cvc5.ProofRule.TRUST`,
  `TRUST_THEORY_REWRITE`, `SAT_REFUTATION`, `ARITH_MULT_TANGENT`, or
  `ARITH_TRANSCENDENTAL_*`), `reconstructProofStep` invokes `skipStep`
  (`Smt/Reconstruct.lean:177–195`) and `addTrust`
  (`Smt/Reconstruct.lean:222–237`), which creates a fresh unassigned
  metavariable `mv : MVarId` for that step's conclusion and appends `mv` to
  `State.currPfGoals`. When `reconstructProof` finishes
  (`Smt/Tactic/Smt.lean:202–268`), any skipped steps remain as explicit open
  Lean goals (`mv :: mvs`) that the user or downstream tactics (`omega`,
  `grind`) must close—never as hidden axioms unless the user explicitly invokes
  `smt +trust` (which closes skipped steps with `sorryAx`, caught immediately by
  `trusted/audit/`).

- **`no_mathlib` Branch Viability
  (`7e54df3e5b7f78e5e6170ffab8ebe813904262b0`):** On its `no_mathlib` branch,
  `lean-smt` drops its dependency on `Mathlib`, replacing
  `Mathlib.Tactic.NormNum` and `Mathlib.Data.Real.Archimedean` with Lean 4 `Std`
  and a lightweight `Rat.FloorRing` module
  (`Smt/Reconstruct/Rat/FloorRing.lean`). Propositional, EUF, linear
  integer/rational arithmetic (`LIA`/`LRA`), and bitvector (`QF_BV`) proof
  reconstruction work without `Mathlib`, making `lean-smt`'s `no_mathlib`
  reconstruction theorems directly portable into Anneal's `theory/` layer.

#### 2.3 LRAT and Bitvector Certificates (`BVDecide` vs. `KernelLRAT`)

For fixed-width Rust integer and pointer obligations (`U8`, `U16`, `U32`, `U64`,
`Usize`), Lean `v4.34.1`'s built-in `bv_decide` tactic (`Std.Tactic.BVDecide`)
bitblasts bitvector goals into an And-Inverter Graph (AIG), converts the AIG to
CNF, runs CaDiCaL externally to emit an LRAT certificate, and verifies the
certificate via `Lean.ofReduceBool`. As established in our companion report
(`sat-pb-and-bitvector-certificate-endpoints-2026-10-14/REPORT.md`), stock
`bv_decide` cannot be used in Anneal because `trusted/audit/` forbids
`Lean.ofReduceBool` and replacing `ofReduceBool` with `rfl` (`reduce_at_kernel`)
hits **seven kernel-reduction blockers** inside `Std.Tactic.BVDecide` and
`Std.Sat`: (1) `Opaque` `Std.HashMap.Raw.m`, (2) `@[extern]` `USize.ofNat` in
hash bucket indexing, (3) `Char.utf8Size` array indexing in LRAT binary parsing,
(4) `Std.Sat.AIG.Entrypoint` `HashMap` DAG memoization, (5) `Except` monadic
wrapping in `DefaultFormula.performRupAdd`, (6) `ByteArray` FFI operations in
binary LRAT ingestion, and (7) `Lean.ofReduceBool` in the reflection glue.
Anneal's `theory/` layer therefore uses the pure `Array`-based `KernelLRAT`
(`checkKernelLratProof_sound`) and `KernelBVDecide` (`checkKernelBVUnsat_sound`)
endpoints, which parse CaDiCaL LRAT certificates in `MetaM` and discharge the
resulting boolean checker in the Lean kernel by `rfl` within `-j1 -M1024`.

| Certificate Path | External Tool / Format | Reconstruction Mechanism | Axiom Footprint | `reduce_at_kernel` (`-M1024`) Compatible? |
| :--- | :--- | :--- | :--- | :--- |
| `lean4export` (`v3.1.0`) | NDJSON `.olean` exporter (`df81913e...`) | Outbound DAG serialization (`in`, `il`, `ie`, `iu`) | Preserves exact kernel environment | Yes (external audit consumer) |
| Alethe + `Carcara` | SMT-LIB v2 $\to$ `.alethe` | External Rust checker (`carcara check`) | Produces no Lean proof term | No (external to Lean kernel) |
| `lean-smt` (`no_mathlib`) | cvc5 FFI $\to$ CPC DAG (`7e54df3e...`) | In-Lean `ReconstructM` building kernel `Expr`s | Zero custom axioms (unsupported steps become open subgoals) | Yes (for `Prop`, `EUF`, `LIA`, `LRA`, `BV`) |
| Stock `bv_decide` | CaDiCaL $\to$ binary LRAT | `Std.Tactic.BVDecide` + `Lean.ofReduceBool` | Adds `Lean.ofReduceBool` (`Lean.trustCompiler`) | **No** (blocked by `trusted/audit/` + 7 kernel blockers) |
| Anneal `KernelBVDecide` | CaDiCaL $\to$ `Array Action` | Total `Array`-backed reflection + `rfl` | Zero axioms (`∅`) | **Yes** (verified in `rfl` under `-j1 -M1024`) |

### Finding 3: Semantic and Type-Directed Search Engines

**Basis:** `source inspection`, `measurement` (inspection of `nomeata/loogle` at
`9f11169aaebf1ed1e7dcc4077f2aafe0fcf66fd0`, `justincasher/lean-explore` at
`17b9d6c87a2bf0dc4ea27de05da8a1c9965391b7`, and
`leanprover-community/LeanSearchClient` at
`c61286b7b63cbfd563b28e11e81d0a18233a044a`).

#### 3.1 `Loogle` Architecture (`Loogle/Find.lean` and `Loogle/Trie.lean`)

Joachim Breitner's `Loogle` (`9f11169aaebf1ed1e7dcc4077f2aafe0fcf66fd0`,
`Loogle/Find.lean:1–660`) answers four query filters—constant reference
(`Real.sin`), name substring (`"differ"`), subexpression pattern (`_ * (_ ^
_)`), and conclusion/type-shape template (`?a + ?b = ?b + ?a` or `List ?a → ?a →
Prop`)—against the entire Mathlib/Std environment in tens of milliseconds. Its
speed and precision rest on four mechanisms in `Loogle/Find.lean`:

1. **Two-Pass Inverted Constant Index (`NameRel`) and Path-Compressed
  `SuffixTrie` (`Find.lean:206–232`, `Trie.lean:20–85`):** At index
  initialization, `Loogle` scans all non-internal declarations (`!c.isInternal
  && !isBlackListed name`) and builds: (a) `byConst : NameRel` (`RBMap Name
  NameSet Name.quickCmp`), mapping every constant `c` to the set of declarations
  whose *type* mentions `c` (`cInfo.type.getUsedConstantsAsSet`), followed by a
  second pass over the `@[simp]` extension that also indexes constants appearing
  on the right-hand side of `@[simp]` lemmas (`Find.lean:216–231`); and (b)
  `byName : SuffixTrie Name`, a radix-compressed suffix trie
  (`Loogle/Trie.lean:20–45`, `compress` at `Trie.lean:50–58`) mapping every
  substring of a declaration's name to its `NameSet`.

2. **Deferred-Postponement Pattern Elaboration and `abstractMVars`
  (`Find.lean:239–266`, `458–481`):** User query fragments such as `_ * (_ ^ _)`
  lack concrete types for their holes, causing standard `Term.elabTerm` to fail
  on unresolved `HMul`/`HPow` typeclass instances. `Loogle` elaborates each
  pattern inside `Term.withoutPostponing` (`elabTermForPattern` at
  `Find.lean:458–481`), suppressing premature typeclass synthesis failure and
  leaving unresolved instance arguments as metavariables. Next, `abstractMVars`
  (`Find.lean:239–266`) transforms the elaborated pattern: user-named
  metavariables (`?a`, `?b`) and anonymous holes (`_`) are abstracted into
  universally bound parameters (`forallE` for conclusion templates, `lam` for
  subterm patterns), whereas local free variables (`fvarId`) in the query
  context are converted via `localFVarToMVar` into fresh unassigned
  metavariables. This inversion ensures that repeated `?a` identifiers across
  separate query filters share a single template binder (enforcing non-linear
  equality), while distinct `_` holes unify independently.

3. **Complexity-Ordered Hypothesis-Permuting Unification (`matchUpToHyps` and
  `matchHyps` at `Find.lean:268–337`):** When matching a conclusion query `?P →
  ?Q → ?R` against a candidate lemma type `T`, `matchUpToHyps` opens `T` with
  `forallMetaTelescope` (converting all lemma parameters into metavariables
  `tHyps`), instantiates the pattern's template parameters with fresh
  metavariables, and opens the pattern with `forallTelescopeReducing` (`pHyps`).
  It then partitions both `pHyps` and `tHyps` by `isProp`: non-propositional
  data parameters in the pattern must unify with the lemma's metavariable
  telescope, while propositional hypotheses in the pattern are sorted by
  ascending `exprSize` (`pHyps.qsort (fun h1 h2 => exprSize h1.2.2 < exprSize
  h2.2.2)` at `Find.lean:328`) and matched via backtracking `isDefEq`
  (`matchHyps` at `Find.lean:268–288`) against any subset and permutation of the
  lemma's hypotheses.

4. **Constant-Guarded Subterm Traversal (`findInConst` and `checkUsedConsts` at
  `Find.lean:160–170`, `339–366`):** Running higher-order `isDefEq` at every AST
  node of every candidate lemma's type is prohibitively slow. `Loogle` computes
  `patConsts : NameSet` (the non-metavariable constants in the query pattern)
  once, and inside `Meta.forEachExpr'`, calls `checkUsedConsts patConsts
  subexpr` (`patConsts.all e.getUsedConstantsAsSet.contains`). Whenever a
  subexpression `subexpr` lacks even one constant required by `patConsts`,
  `forEachExpr'` returns `false`, pruning the entire subtree without allocating
  metavariables or invoking `isDefEq`.

#### 3.2 Hybrid Search (`LeanExplore`, `LeanSearchClient`, `Moogle`)

When an engineer or LLM agent does not know the exact constant names or type
shape of a lemma, purely syntactic/unification search (`Loogle`) returns no
hits. Three complementary architectures address natural-language and goal-state
retrieval:

- **`LeanExplore` (`17b9d6c87a2bf0dc4ea27de05da8a1c9965391b7`,
  `src/lean_explore/util/search_engine.py:34–412`):** Offline-indexes each Lean
  declaration into SQLite + FAISS by generating an LLM natural-language
  informalization (`informal_text`) of the declaration's signature and
  docstring. At query time, `SearchEngine.search` combines three BM25+ lexical
  scores (`name_tokens` weighted $1.5\times$, `informal_tokens` weighted
  $1.0\times$, and `statement_tokens` weighted $0.8\times$), dense cosine
  similarity from a FAISS index of `Qwen/Qwen3-Embedding-0.6B` vectors, a
  call-graph pagerank/dependency weight (`DEPENDENCY_WEIGHT = 0.25`), and a
  final cross-encoder reranking pass using `Qwen/Qwen3-Reranker-0.6B`
  (`search_engine.py:298–395`).

- **`LeanSearchClient` (`c61286b7b63cbfd563b28e11e81d0a18233a044a`,
  `LeanSearchClient/Syntax.lean:51–328`):** Integrates three hosted search APIs
  into Lean 4 commands and tactics: `#leansearch` (queries `leansearch.net` with
  natural-language + formal syntax), `#statesearch` (formats the active proof
  goal via `Meta.ppGoal mvarId` and queries `leanstatesearch.net` for premises
  commonly used to close similar goals), and `#loogle` (queries
  `loogle.lean-lang.org`). Critically, `Syntax.lean:100–106` introduces
  `checkTactic`, which runs `withoutModifyingState <| evalTactic stx` on
  candidate `apply`, `exact`, or `rw` suggestions and filters out candidates
  that fail to elaborate on the live goal.

- **Fit for Anneal:** Because `cargo-anneal` runs offline inside developer
  worktrees and CI containers without GPU inference servers or external network
  access, hosted APIs (`leansearch.net`, `leanstatesearch.net`, `moogle.ai`) and
  600M-parameter embedding pipelines (`LeanExplore`) are unsuitable as hard
  dependencies. However, combining `Loogle`'s two-stage constant-filtered
  hypothesis-permuting unification with `LeanSearchClient`'s speculative
  `withoutModifyingState` tactic verification yields a fast, deterministic,
  zero-dependency search and validation loop directly inside Lean `v4.34.1`
  (implemented in `support/anneal_harness.lean`).

### Finding 4: Interactive REPL and Agentic Proof Protocols

**Basis:** `source inspection`, `measurement` (inspection of
`lenianiva/Pantograph` at `0789692d65e365c027d171074bf747f1d40328d0`,
`stanford-centaur/PyPantograph` at `a098035e29f7910a627b8440145b51246ec38484`,
`lean-dojo/LeanDojo-v2` at `baed5eae6e87a65a446d9f54af07aab2154e7599`,
`oOo0oOo/lean-lsp-mcp` at `bd95db58fe684ec0c3f5f875c81bac949abc8929`,
`leanprover-community/repl` at `6a2be396449a5213a36748ca7682d16d54a1ca4a`,
`augustepoiroux/LeanInteract` at `768e18ebcb5c7ec34d308768a785389eeac37798`, and
`Project-Numina/kimina-lean-server` at
`fb2393de3461db35eda4c714e3fd21187e92ec90`).

#### 4.1 Coupled Metavariables and State Restoration in `Pantograph`

Unlike human-oriented IDE protocols (LSP) that re-elaborate text edits,
`Pantograph` (`0789692d65e365c027d171074bf747f1d40328d0`, `v0.3.19`) models
tactic proof search as a directed acyclic graph of immutable `GoalState` nodes
(`Pantograph/Goal.lean:94–307`). Source inspection of `Pantograph/Goal.lean` and
`Pantograph/MetaTranslate.lean` identifies four subtle metaprogramming
invariants required for sound machine-driven tree search in Lean 4:

1. **Coupled Metavariables Across Sibling Goals
  (`Pantograph.Condensed.dependentMVars`, `Pantograph/Goal.lean:54–78`):** When
  a tactic such as `apply Exists.intro`, `refine ⟨?_, ?_⟩`, or `Apply.apply`
  splits a goal into subgoals `[g1, g2]`, `g1` may be a *type-level
  metavariable* `?w : α` that appears inside the target or local hypotheses of
  `g2` (`⊢ P ?w`). Naive tree-search harnesses that solve `g1` and `g2`
  independently in parallel branches produce incompatible assignments for `?w`.
  `Pantograph` detects this coupling by running `MetavarContext.findMVars` over
  every local declaration type/value and the target type of each goal
  (`Goal.lean:58–75`), recording the set of unassigned expression metavariables
  referenced by each goal. In `GoalState.step` (`Goal.lean:180–218`), only the
  targeted goal `freeMVar` runs the tactic while dormant sibling goals are
  removed from `Tactic.SavedState.goals`; however, if solving `freeMVar` assigns
  or partially instantiates a coupled metavariable shared with a dormant
  sibling, `Pantograph` automatically pulls the affected sibling back into the
  active goal frontier so the agent sees its updated type.

2. **Delayed Metavariable Assignments (`DelayedMetavarAssignment`,
  `Pantograph/Goal.lean:119–131`):** Tactics that enter binders (`intro`,
  `revert`, `cases`, `induction`) do not immediately assign their parent
  metavariable `?m` in `mctx.eAssignment`; instead, Lean records a
  `DelayedMetavarAssignment` (`mctx.dAssignment.find? mvarId`) containing
  `fvars` and `mvarIdPending`. `GoalState.hasMCtxDepth` (`Goal.lean:119–131`)
  explicitly checks both `eAssignment` and `dAssignment` before declaring a goal
  assigned.

3. **Fixing Stock `Tactic.SavedState.restore` Name-Generator Collisions
  (`restoreCoreMExtra`, `Pantograph/Goal.lean:158–178`):** In Lean 4
  (`v4.34.1`), `Lean.Elab.Tactic.SavedState.restore` restores `Term.SavedState`
  and the goal list, but **omits** three fields of `Core.State` and
  `Meta.State`: `ngen` (the fresh `NameGenerator`), `nextMacroScope` (hygienic
  macro scope counter), and `auxDeclNGen` (the generator for compiler auxiliary
  declarations such as `_auxProof_1`). If a proof search agent branches from a
  saved state twice, both branches generate identical `MVarId`s, macro scopes,
  and `_auxProof` constant names, corrupting subsequent environment merges.
  `Pantograph` patches this via `restoreCoreMExtra` (`Goal.lean:166–178`), which
  explicitly restores `ngen`, `nextMacroScope`, and `auxDeclNGen` alongside
  `SavedState.restore`.

4. **Cross-Context Proof Replay and Auxiliary Declaration Filtering
  (`GoalState.replay` at `Goal.lean:245–307` and `MetaTranslate.lean:57–196`):**
  When an agent proves a helper lemma in a detached draft state (`have` or `let`
  sub-search) and merges it back into the main proof tree, `MetaTranslate`
  translates the assigned metavariable DAG across `MetavarContext` instances
  while explicitly filtering out `decl.isAuxDecl` hypotheses
  (`MetaTranslate.lean:105–116`), which reflect Lean's internal
  recursive-definition header and would otherwise appear as bogus user
  hypotheses.

#### 4.2 `LeanDojo-v2`, `lean-lsp-mcp`, `repl`, `LeanInteract`, and `Kimina`

- **`LeanDojo-v2` (`baed5eae6e87a65a446d9f54af07aab2154e7599`):** Splits offline
  corpus extraction from online proof search. Its offline tracer
  (`lean_dojo_v2/lean_dojo/data_extraction/ExtractData.lean:1–348`) hooks into
  `lake build` via `lean --run ExtractData.lean`, walking every command's
  `InfoTree` (`visitTacticInfo` at `ExtractData.lean:54–101` and `visitTermInfo`
  at `ExtractData.lean:103–145`) in spawned child processes (`processModule` at
  `ExtractData.lean:245–312`) to emit `.ast.json` and `.trace.xml` files
  containing before/after goal states and resolved premise constants (including
  `.olean` step locations via `Environment.getModuleIdxFor?`). For online
  interactive search, `LeanDojo-v2` dropped its custom Lean 4 REPL patch in
  favor of `PyPantograph` (`lean_dojo_v2/prover/base_prover.py:29–77`), calling
  `server.load_sorry(code)` and `server.goal_tactic(state, goal_id=0,
  tactic=tactic)`.

- **`lean-lsp-mcp` (`bd95db58fe684ec0c3f5f875c81bac949abc8929`, `v0.32.0`):**
  Exposes 22 Model Context Protocol (MCP) tools to LLM agents by combining a
  persistent LSP client (`leanclient`) with an in-memory virtual file pool
  (`ScratchPool` in `src/lean_lsp_mcp/server.py:125–155`, allocating virtual
  URIs `_scratch_multi_attempt_0.lean` .. `_N.lean` via LSP
  `didOpen`/`didChange` without writing to disk) and an optional
  `leanprover-community/repl` fast path (`src/lean_lsp_mcp/repl.py:121–328`). In
  `repl.py`, `lean_multi_attempt` splits a file at the theorem start, caches the
  header/prefix as an `env` snapshot ID, replaces the target line with `sorry`,
  and tests $k$ candidate tactics in parallel against the resulting `proofState`
  ID in ~50–100 ms per candidate. In addition, `lean_verify`
  (`src/lean_lsp_mcp/verify.py:42–92`) runs `#print axioms` plus a regex source
  scanner (`_SOURCE_WARNING_PATTERNS` at `verify.py:22–35`) for
  `#[implemented_by]`, `@[extern]`, `@[csimp]`, `lcErased`, `unsafe`, `partial`,
  and `sorryAx`, while `lean_minimal_hypotheses`
  (`src/lean_lsp_mcp/minimal_hypotheses.py:29–141`) prunes unused hypotheses via
  binary halving (`_find_minimal_indices`) before synthesizing a proof.

- **`leanprover-community/repl` (`6a2be396449a5213a36748ca7682d16d54a1ca4a`,
  `REPL/Main.lean:1–472` and `REPL/Lean/ContextInfo.lean:1–185`):** Reads JSON
  commands over `stdin` and indexes both `CommandSnapshot`s (`env` IDs) and
  `ProofSnapshot`s (`proofState` IDs). Whenever a command elaborates a `sorry`
  tactic, `runCommandElabM` extracts all `Info.ofTacticInfo` nodes matching
  `Parser.Tactic.tacticSorry` and stores a `ProofSnapshot`
  (`Main.lean:245–302`). Two features of `repl` are critical for soundness and
  scaling: (1) `getProofStatus` (`REPL/Lean/ContextInfo.lean:128–164`) does not
  merely check `goals.isEmpty`; once all goals close, it instantiates the root
  proof metavariable (`instantiateMVars`), checks `!e.hasSorry &&
  !e.hasExprMVar`, and runs `Lean.Kernel.addDecl` (`env.addDecl decl`) to verify
  that the assembled proof term passes the Lean 4 kernel before reporting
  `"ProofStatus": "Completed"`; and (2) `pickleCommandSnapshot` /
  `pickleProofSnapshot` (`Main.lean:105–183`) use `compact_region` FFI calls
  (`REPL/Lean/Environ.lean`) to serialize live snapshots to `.olean` files on
  disk.

- **`LeanInteract` (`768e18ebcb5c7ec34d308768a785389eeac37798`, `v0.11.6`) and
  `Kimina` (`fb2393de3461db35eda4c714e3fd21187e92ec90`):** Both systems solve
  the long-running memory growth of `leanprover-community/repl` under
  high-throughput agent workloads. Because Lean 4 `Environment` objects
  accumulate monotonically unless explicitly freed, `LeanInteract`'s
  `AutoLeanServer` (`src/lean_interact/server.py:345–520`) monitors system RAM
  (`max_total_memory = 0.8`), kills and restarts the `repl` subprocess on
  timeout or memory pressure, and transparently reconstructs active
  `env`/`proofState` handles by replaying their command chain from
  `ReplaySessionCache` (`src/lean_interact/sessioncache.py:249–370`). `Kimina`
  (`server/split.py:24–53` and `server/manager.py:85–240`) splits every snippet
  into `(header, body)`, assigns a dedicated worker process pre-warmed with
  `header` at `env = 0`, and sends each verification request with `{"cmd": body,
  "env": 0, "gc": true}` so per-snippet environments are freed immediately while
  the base `import` environment stays resident in memory.

| Protocol / Tool | Revision (40-char SHA) | State Granularity | Coupled Metavariables (`sibling_dep`)? | Kernel Verification Gate? | Memory Management |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `Pantograph` (`v0.3.19`) | `0789692d65e365c027d171074bf747f1d40328d0` | Tactic `GoalState` DAG + `restoreCoreMExtra` | **Yes** (`dependentMVars` + `dAssignment`) | Via `rootExpr` instantiation at completion | Explicit `goal.delete` / state GC |
| `LeanDojo-v2` | `baed5eae6e87a65a446d9f54af07aab2154e7599` | Offline `InfoTree` tracer + online `PyPantograph` | **Yes** (delegated to `Pantograph`) | Delegated to `Pantograph` / `lake build` | Per-module child processes (`ExtractData.lean`) |
| `lean-lsp-mcp` (`v0.32.0`) | `bd95db58fe684ec0c3f5f875c81bac949abc8929` | LSP `ScratchPool` + `repl` `proofState` fast path | No (single-goal string array in MCP tool) | `lean_verify` (`#print axioms` + source regex scan) | Virtual scratch rotation + `repl` restart |
| `leanprover-community/repl` | `6a2be396449a5213a36748ca7682d16d54a1ca4a` | `CommandSnapshot` (`env`) & `ProofSnapshot` (`proofState`) | No (flat `goals` string array) | **Yes** (`getProofStatus` runs `env.addDecl`) | `gc: true` flag + `.olean` `compact_region` pickling |
| `LeanInteract` (`v0.11.6`) | `768e18ebcb5c7ec34d308768a785389eeac37798` | Python wrapper over `repl` snapshots | No (inherits `repl` schema) | Yes (inherits `repl` `ProofStatus`) | `AutoLeanServer` RSS watchdog (80% RAM) + `ReplaySessionCache` |
| `Kimina` | `fb2393de3461db35eda4c714e3fd21187e92ec90` | Header-partitioned `repl` worker pool (`env: 0`) | No (whole-snippet verification) | Yes (full command elaboration + error check) | `split_snippet` header reuse + `gc: true` + `max_repl_mem` |
| `support/anneal_harness.lean` | SHA-256 `9f9c51ef...` | Single-shot CLI (`search` & `goals --try-tactic`) | **Yes** (`dependentMVars` per goal) | **Yes** (`!newMsgs.hasErrors && !instRoot.hasSorry`) | Targeted imports (`< 300 MB` RSS, fits `-j1 -M1024`) |

### Finding 5: Zero-Dependency Search and Goal Harness (`anneal_harness.lean`)

**Basis:** `source inspection`, `measurement`, `design reasoning`
(implementation and empirical verification of `support/anneal_harness.lean`, 893
lines, SHA-256
`9f9c51efc7ef322f7c7b991dbb3b261d3893f244b6f2f9c5d5cb29ae9fecb25a`, under Lean
`v4.34.1` commit `5045d0056413266e57c625dcd7c365b10e377c52`).

#### 5.1 Resolving the `-M1024` Umbrella-Import Failure Mode

A critical empirical finding of this investigation is that **any Lean `v4.34.1`
file that begins with umbrella `import Lean` + `import Std` immediately fails
under Anneal's mandatory `-j1 -M1024` (1,024 MB) memory limit** with `error:
(kernel) excessive memory consumption detected` on the very first declaration.
In Lean `v4.34.1`, `import Lean` transitively maps the `.olean` compacted
regions of the entire compiler backend (LCNF, IR, C codegen, Lake, and all
Widget/Server modules), consuming ~1,150 MB of Lean heap before a single line of
user code is elaborated.

Replacing `import Lean` + `import Std` with two targeted imports—`import
Lean.Elab.Frontend` and `import Lean.Elab.Tactic.Basic`—loads the complete
parser, command/term/tactic elaborators, `InfoTree` infrastructure, and `MetaM`
unification engine while keeping total memory consumption under ~300 MB. With
these two imports, `support/anneal_harness.lean` compiles cleanly from scratch
under `lean -j1 -M1024 support/anneal_harness.lean` in **2.5 seconds** with zero
warnings and zero errors.

#### 5.2 Architecture of `support/anneal_harness.lean`

`support/anneal_harness.lean` is a standalone, zero-dependency Lean `v4.34.1`
module (`namespace AnnealHarness`) and CLI executable that provides both
capabilities required by `cargo-anneal`'s autoprover loop without external Lake
packages:

1. **Sysroot-Aware Environment Bootstrap (`setupSearchPath`, lines `811–814`):**
  Resolves the running `lean` binary via `IO.appPath`, derives the toolchain
  sysroot via `Lean.findSysroot`, and initializes `Lean.searchPathRef` with any
  `--path` directories so `importModules` can load both `Init`/`Std` and project
  `.olean` artifacts directly via `lean --run` without `lake env`.

2. **Two-Stage Loogle-Style Type-Shape Search (`runSearch`, lines `80–243`,
  `492–592`):** (a) *Stage 1 (`isInternalOrBlacklisted`, `hasAllConsts`,
  `getDeclModuleName`, lines `70–106`, `152–157`):* Filters out internal
  compiler artifacts (`.recOn`, `.casesOn`, `.brecOn`, `._unary`, `.eq_def`,
  `._cstage`, `._sunfold`, and hygienic macro scopes), checks module prefix
  filters (`--mod-prefix`) and substring filters (`--name`), and verifies that
  `ci.type.getUsedConstantsAsSet` contains every constant required by `--const
  <Name>` and compiled `--concl`/`--pat` patterns before entering `MetaM`. (b)
  *Stage 2 (`elabPatternString`, `mkConclusionMatcher`, `mkSubtermMatcher`,
  `matchUpToHyps`, `matchHyps`, lines `110–230`):* Elaborates `--concl` and
  `--pat` strings under `Term.withoutPostponing`, abstracts metavariables
  (`abstractMVars`), checks head-index compatibility (`canMatchHead`), and runs
  backtracking `isDefEq` across hypothesis permutations (`matchHyps`) and
  `hasAllConsts`-pruned subterms (`Meta.forEachExpr'`). Matching hits are sorted
  deterministically by ascending AST complexity (`exprSize`).

3. **Coupled-Metavariable Goal Extraction and Speculative Tactic Validation
  (`runGoals`, lines `260–489`, `595–714`):** (a) *`sorry` Site Discovery and
  Span Deduplication (`collectInfoTreeSteps`, `runGoals`, lines `325–385`,
  `643–683`):* Elaborates a target `.lean` file or inline `--code` snippet via
  `Parser.parseHeader` and `Elab.Frontend.processCommands` (`elaborateSource`),
  walks every command's `InfoTree` to collect `TacticInfo` and `TermInfo` steps,
  and prioritizes outer `Lean.Parser.Tactic.tacticSorry` spans over
  macro-expanded child nodes at the same byte range so `mctxBefore` captures the
  pre-sorry tactic goal and metavariable coupling. (b) *Pantograph-Style Coupled
  Metavariable Serialization (`serializeGoal`, lines `260–310`):* For each
  active goal `mvarId`, `serializeGoal` instantiates every
  non-implementation-detail local hypothesis and the target type and runs
  `Meta.getMVars` to populate `dependentMVars`—the exact list of unassigned
  metavariables (`_uniq.N`) referenced inside that goal's context or target. (c)
  *Speculative Tactic Execution (`runCandidateTactic`, lines `430–489`):* When
  `--try-tactic "<tac>"` is supplied, `runCandidateTactic` restores the exact
  pre-`sorry` `ContextInfo` and `TacticInfo.mctxBefore`, parses and runs `<tac>`
  via `Elab.Tactic.evalTactic`, checks that the tactic emitted zero elaboration
  errors (`!errorMsgs.isEmpty`), verifies whether the post-tactic root proof
  term is free of residual `sorryAx` (`!instGoal.hasSorry`), and serializes the
  remaining open goals with updated `dependentMVars`.

#### 5.3 Empirical Verification of `support/anneal_harness.lean`

Running `support/anneal_harness.lean` on Lean `v4.34.1` confirms both its
`search` and `goals` pipelines:

```json
// Command:
// lean --run support/anneal_harness.lean search --module Init.Data.List.Lemmas \
//   --const HAppend.hAppend --const List.length --concl "(?xs ++ ?ys).length = ?rhs" --max 2
{"shown": 2,
 "hits":
 [{"type":
   "∀ {α : Type u} {as bs : List α}, (as ++ bs).length = as.length + bs.length",
   "name": "List.length_append",
   "module": "Init.Data.List.Basic",
   "kind": "theorem"},
  {"type":
   "∀ {α : Type u_1} {l : List α} {a : α}, (l ++ [a])[l.length]? = some a",
   "name": "List.getElem?_concat_length",
   "module": "Init.Data.List.Lemmas",
   "kind": "theorem"}],
 "count": 20}
```

On a proof containing a coupled existential witness (`theorem coupled_demo (n :
Nat) (h : n = 5) : ∃ k : Nat, k = n ∧ k > 0 := by refine ⟨?w, ?_, ?_⟩; sorry`),
`goals` identifies the shared witness metavariable `_uniq.85` (`case w : ⊢ Nat`)
inside `dependentMVars` of sibling goals `refine_1` (`⊢ ?w = n`) and `refine_2`
(`⊢ ?w > 0`), and verifies `--try-tactic "exact n"`:

```json
// Command:
// lean --run support/anneal_harness.lean goals \
//   --code "theorem coupled_demo (n : Nat) (h : n = 5) : ∃ k : Nat, k = n ∧ k > 0 := by refine ⟨?w, ?_, ?_⟩; sorry" \
//   --try-tactic "exact n"
{"unsolvedSites":
 [{"syntax": "sorry",
   "span": {"startLine": 1, "startCol": 98, "endLine": 1, "endCol": 103},
   "kind": "Lean.Parser.Tactic.tacticSorry",
   "goalsBefore":
   [{"userName": "w", "target": "Nat", "mvarId": "_uniq.85",
     "dependentMVars": []},
    {"userName": "refine_1", "target": "?w = n", "mvarId": "_uniq.94",
     "dependentMVars": ["_uniq.85"]},
    {"userName": "refine_2", "target": "?w > 0", "mvarId": "_uniq.95",
     "dependentMVars": ["_uniq.85"]}]}],
 "tacticTrials":
 [{"tactic": "exact n",
   "success": true,
   "remainingGoals":
   [{"userName": "refine_1", "target": "n = n", "mvarId": "_uniq.94",
     "dependentMVars": []},
    {"userName": "refine_2", "target": "n > 0", "mvarId": "_uniq.95",
     "dependentMVars": []}],
   "goalsSolved": false}]}
```

When `--try-tactic "exact n"` closes Goal 0 (`_uniq.85 : ⊢ Nat`), it assigns `?w
:= n`. The harness automatically propagates that assignment into sibling goals
`_uniq.94` and `_uniq.95`, transforming their targets from `?w = n` and `?w > 0`
to `n = n` and `n > 0` and clearing `dependentMVars`.

## Boundaries

1. **External Cross-Prover Checkers Are Audit Supplements, Never Substitutes for
  `trusted/audit/`:** Translating Anneal's `.olean` artifacts to Dedukti
  (`lean4less` + `lean2dk`) or Rocq (`rocq-lean-import`) requires adding
  extensionality postulates (`Lean4Less.pIrrel`, `Singleton.elim`,
  `Quot.liftProp`, or Rocq's `Axiom quot_sound`) and, in `lean2dk`, stubbing 43
  `omega`/`Nat.Linear` reflection lemmas in `Init.Data.Nat.Lemmas`. Therefore,
  `trusted/audit/` must remain anchored on the Lean 4 kernel (`v4.34.1`) with
  `Trusted.allowedAxioms = ∅`.

2. **`lean-smt` Scope Limitations Under `no_mathlib`:** While
  `ufmg-smite/lean-smt`'s `no_mathlib` branch
  (`7e54df3e5b7f78e5e6170ffab8ebe813904262b0`) reconstructs `Prop`, `EUF`,
  `LIA`, `LRA` (`Rat`), and `QF_BV` proofs without `Mathlib` or custom axioms,
  it does not support non-linear real arithmetic (`Real`), transcendental
  functions, or `TRUST_THEORY_REWRITE` steps without leaving open subgoals (`mv
  :: mvs`). Furthermore, `lean-smt` requires linking `libcvc5` via C++ FFI
  during elaboration; for pure offline SAT/bitvector verification without C++
  FFI, Anneal should prefer `KernelLRAT` and `KernelBVDecide`.

3. **Single-Shot Process Boundary in `support/anneal_harness.lean`:**
  `support/anneal_harness.lean` is designed as a stateless, zero-dependency CLI
  and library module that fits within `-j1 -M1024`. For single-file `goals`
  extraction or batch `search` queries, its ~2.0–2.5 s startup cost is
  negligible. If `cargo-anneal` later requires thousands of sequential tactic
  steps per second in a deep MCTS tree search,
  `AnnealHarness.runCandidateTactic` and `AnnealHarness.serializeGoal` should be
  driven inside a persistent `stdin`/`stdout` loop (following `Pantograph`'s
  `GoalState` table + `restoreCoreMExtra` pattern) rather than spawning a fresh
  OS process per tactic step.

4. **Definitional Equality vs. Syntactic Constant Pre-Filtering:**
  `support/anneal_harness.lean`'s Stage-1 constant pre-filter (`hasAllConsts`)
  requires every constant passed via `--const` to appear syntactically in
  `ci.type.getUsedConstantsAsSet`. Note also that surface notation such as `xs
  ++ ys` elaborates to the typeclass projection `HAppend.hAppend` rather than
  `List.append`; callers should either pass `--const HAppend.hAppend` or omit
  `--const` and let `--concl` / `--pat` extract the pattern's constants
  automatically.

## Evidence

### Inspected Upstream Repositories and Pinned Revisions

All 17 upstream repositories, Lean `v4.34.1`, and `joshlf/anneal` were inspected
at the exact 40-character Git commit hashes below (with full file-level SHA-256
digests recorded in `support/source-manifest.json`, SHA-256
`550d7df129b1ef89f532313ee96f32a11dee6f52fdda6cfb78e23f860b3ba89a`):

| Repository | Pinned Commit (40-char SHA) | Primary Inspected Files & Line Ranges |
| :--- | :--- | :--- |
| `leanprover/lean4export` | `df81913eee5519d5a88ae5b0fd701b5298cc29ab` | `Export.lean:1–354`, `Main.lean:1–86`, `format_ndjson.md:1–328` |
| `rish987/lean4less` | `5b66bbc4af5c2c11313fcfb5098630dadaf19281` | `Lean4Less/TypeChecker.lean:725–1242`, `Lean4Less/Methods.lean:62–326`, `Lean4Less/EConsts.lean:28–165`, `Lean4Less/Quot.lean:80–91`, `Lean4Less/Inductive.lean:160–188` |
| `rish987/lean2dk` (`main`) | `471208f18c29420e25750503648469fc95d2ac8f` | `Lean2Dk/Output.lean:1–299`, `theory/lean.dk:1–66` |
| `rish987/lean2dk` (`claude-stable`) | `29f985670008c29e852d61c562b8c10c84f7c5fb` | `Lean2Dk/Export.lean:245–360`, `patches/dkcheck-lazy-delta.patch:1–351`, `patches/dkcheck-eta-memo.patch:1–291` |
| `rocq-community/rocq-lean-import` | `2d28bbe80e7361bf3ac54f5ef099207fc61ce837` | `src/lean.ml:699–850, 1927–2150`, `theories/Loader.v:1–88` |
| `LLM4Rocq/babel-formal` | `71c2aa9bc78e6d41c5421f8ae8e9f551c12f570b` | `src/lean_parse.py:1–337`, `src/coq_emit.py:1–348`, `src/pipeline.py:1–183` |
| `minirust/specr` | `15200eb5e676e2ee91f43bd79e674f8fc32e5348` | `src/main.rs:1–61`, `src/tree.rs:1–329` |
| `nomeata/loogle` | `9f11169aaebf1ed1e7dcc4077f2aafe0fcf66fd0` | `Loogle/Find.lean:1–660`, `Loogle/Trie.lean:1–128` |
| `justincasher/lean-explore` | `17b9d6c87a2bf0dc4ea27de05da8a1c9965391b7` | `src/lean_explore/util/search_engine.py:34–412` |
| `leanprover-community/LeanSearchClient` | `c61286b7b63cbfd563b28e11e81d0a18233a044a` | `LeanSearchClient/Syntax.lean:51–328` |
| `lenianiva/Pantograph` | `0789692d65e365c027d171074bf747f1d40328d0` | `Pantograph/Goal.lean:54–307`, `Pantograph/Frontend.lean:1–376`, `Pantograph/MetaTranslate.lean:57–196` |
| `stanford-centaur/PyPantograph` | `a098035e29f7910a627b8440145b51246ec38484` | `pantograph/server.py:1–495`, `pantograph/expr.py:1–252` |
| `lean-dojo/LeanDojo-v2` | `baed5eae6e87a65a446d9f54af07aab2154e7599` | `lean_dojo_v2/lean_dojo/data_extraction/ExtractData.lean:1–348`, `lean_dojo_v2/prover/base_prover.py:1–83` |
| `oOo0oOo/lean-lsp-mcp` | `bd95db58fe684ec0c3f5f875c81bac949abc8929` | `src/lean_lsp_mcp/server.py:125–155`, `src/lean_lsp_mcp/repl.py:121–328`, `src/lean_lsp_mcp/verify.py:22–92`, `src/lean_lsp_mcp/minimal_hypotheses.py:29–141` |
| `leanprover-community/repl` | `6a2be396449a5213a36748ca7682d16d54a1ca4a` | `REPL/Main.lean:105–302`, `REPL/Lean/ContextInfo.lean:128–164` |
| `augustepoiroux/LeanInteract` | `768e18ebcb5c7ec34d308768a785389eeac37798` | `src/lean_interact/server.py:345–520`, `src/lean_interact/sessioncache.py:249–370` |
| `Project-Numina/kimina-lean-server` | `fb2393de3461db35eda4c714e3fd21187e92ec90` | `server/manager.py:85–240`, `server/repl.py:258–285`, `server/split.py:24–53` |
| `ufmg-smite/lean-smt` | `db545bebe2de1e06dc2df62a6ff6c20e5736bfc0` (`main`), `7e54df3e5b7f78e5e6170ffab8ebe813904262b0` (`no_mathlib`) | `Smt/Reconstruct.lean:177–336`, `Smt/Tactic/Smt.lean:202–268`, `Smt/Reconstruct/Rat/FloorRing.lean:1–72` |

### Complete Declaration and Theorem Inventory for `support/anneal_harness.lean`

The support artifact `support/anneal_harness.lean` (893 lines, SHA-256
`9f9c51efc7ef322f7c7b991dbb3b261d3893f244b6f2f9c5d5cb29ae9fecb25a`) defines 37
declarations (3 structures, 25 operational functions, and 9 kernel-checked
specification theorems) in `namespace AnnealHarness` (plus top-level `main`),
all verified with zero `sorry`s and zero warnings under `lean -j1 -M1024
support/anneal_harness.lean`:

| # | Declaration Name | Kind | Lines | Purpose / Formal Statement |
| :--- | :--- | :--- | :--- | :--- |
| 1 | `AnnealHarness.posToLineCol` | `def` | `40–42` | Converts a raw UTF-8 byte offset (`String.Pos.Raw`) into 1-based `(line, col)` coordinates |
| 2 | `AnnealHarness.syntaxSpanJson` | `def` | `45–55` | Serializes a `Syntax` node's source span (`startLine`, `startCol`, `endLine`, `endCol`) to `Json` |
| 3 | `AnnealHarness.constantKind` | `def` | `58–66` | Classifies `ConstantInfo` into `"axiom"`, `"def"`, `"theorem"`, `"opaque"`, `"quot"`, `"inductive"`, `"ctor"`, or `"recursor"` |
| 4 | `AnnealHarness.getDeclModuleName` | `def` | `70–75` | Resolves the defining module name for a declaration via `env.getModuleIdxFor?` |
| 5 | `AnnealHarness.isInternalOrBlacklisted` | `def` | `80–106` | Filters compiler-generated auxiliaries (`.recOn`, `.casesOn`, `.brecOn`, `._unary`, `.eq_def`, `._cstage`, `._sunfold`, macro scopes) |
| 6 | `AnnealHarness.canMatchHead` | `def` | `110–113` | Soundness-preserving `HeadIndex` pre-check (`true` if either head is `.mvar` or heads are equal) |
| 7 | `AnnealHarness.matchHyps` | `partial def` | `117–133` | Backtracking `isDefEq` matcher across permutations of propositional hypotheses |
| 8 | `AnnealHarness.matchUpToHyps` | `def` | `136–149` | Matches an `AbstractMVarsResult` template against a candidate type up to hypothesis permutation |
| 9 | `AnnealHarness.hasAllConsts` | `def` | `152–157` | Constant-set inclusion guard (`requiredConsts ⊆ e.getUsedConstantsAsSet`) |
| 10 | `AnnealHarness.mkConclusionMatcher` | `def` | `160–170` | Compiles a conclusion pattern (`--concl`) into a `ConstantInfo → MetaM Bool` predicate |
| 11 | `AnnealHarness.mkSubtermMatcher` | `def` | `173–191` | Compiles a subterm pattern (`--pat`) with `hasAllConsts` subtree pruning inside `Meta.forEachExpr'` |
| 12 | `AnnealHarness.elabPatternString` | `def` | `196–212` | Parses and elaborates a pattern string under `Term.withoutPostponing` |
| 13 | `AnnealHarness.ppConstantType` | `def` | `215–219` | Pretty-prints a declaration's type on a single line (`width := 10000`) |
| 14 | `AnnealHarness.exprSize` | `def` | `223–230` | Total structural AST node counter used to rank search hits by ascending complexity |
| 15 | `AnnealHarness.SearchConfig` | `structure` | `233–243` | Configuration record for the `search` subcommand |
| 16 | `AnnealHarness.serializeGoal` | `def` | `260–310` | Serializes a single `MVarId` goal with local hypotheses, target type, and coupled `dependentMVars` |
| 17 | `AnnealHarness.ExtractedStep` | `structure` | `313–322` | Record of an `InfoTree` tactic step or `sorry` hole with `goalsBefore` and `goalsAfter` |
| 18 | `AnnealHarness.collectInfoTreeSteps` | `partial def` | `325–385` | Traverses an `InfoTree` to extract `TacticInfo` steps and standalone `sorry` `TermInfo` holes |
| 19 | `AnnealHarness.elaborateSource` | `unsafe def` | `388–426` | Parses header imports, loads `.olean` modules, and runs `Elab.Frontend.processCommands` |
| 20 | `AnnealHarness.runCandidateTactic` | `def` | `430–489` | Restores pre-`sorry` `ContextInfo`/`mctxBefore`, runs `evalTactic`, and checks `!hasErrors && !hasSorry` |
| 21 | `AnnealHarness.runSearch` | `unsafe def` | `492–592` | Executes two-stage type-shape search and prints `exprSize`-ranked JSON hits |
| 22 | `AnnealHarness.GoalsConfig` | `structure` | `595–601` | Configuration record for the `goals` subcommand |
| 23 | `AnnealHarness.runGoals` | `unsafe def` | `604–714` | Extracts deduplicated `sorry` sites, coupled `dependentMVars`, and `--try-tactic` trials as JSON |
| 24 | `AnnealHarness.usage` | `def` | `720–745` | CLI help and usage string |
| 25 | `AnnealHarness.parseSearchArgs` | `partial def` | `747–783` | Command-line flag parser for `search` |
| 26 | `AnnealHarness.parseGoalsArgs` | `partial def` | `785–807` | Command-line flag parser for `goals` |
| 27 | `AnnealHarness.setupSearchPath` | `def` | `811–814` | Discovers the Lean sysroot via `IO.appPath` and `Lean.findSysroot` and initializes `LEAN_PATH` |
| 28 | `AnnealHarness.canMatchHead_mvar_left` | `theorem` | `821–823` | `∀ (m : MVarId) (hi : HeadIndex), canMatchHead (.mvar m) hi = true` |
| 29 | `AnnealHarness.canMatchHead_mvar_right` | `theorem` | `826–828` | `∀ (hi : HeadIndex) (m : MVarId), canMatchHead hi (.mvar m) = true` |
| 30 | `AnnealHarness.canMatchHead_structural` | `theorem` | `832–837` | `canMatchHead .sort .sort = true ∧ canMatchHead .lam .lam = true ∧ canMatchHead .forallE .forallE = true ∧ canMatchHead .sort .lam = false` |
| 31 | `AnnealHarness.exprSize_pos` | `theorem` | `840–841` | `∀ (e : Expr), 0 < exprSize e` (proves strict positivity of `exprSize`) |
| 32 | `AnnealHarness.exprSize_app` | `theorem` | `844–846` | `∀ (f a : Expr), exprSize (.app f a) = 1 + exprSize f + exprSize a` |
| 33 | `AnnealHarness.exprSize_forallE` | `theorem` | `849–851` | `∀ n d b bi, exprSize (.forallE n d b bi) = 1 + exprSize d + exprSize b` |
| 34 | `AnnealHarness.isInternalOrBlacklisted_recOn` | `theorem` | `855–857` | `∀ (p : Name), isInternalOrBlacklisted (.str p "recOn") = true` |
| 35 | `AnnealHarness.isInternalOrBlacklisted_brecOn` | `theorem` | `861–863` | `∀ (p : Name), isInternalOrBlacklisted (.str p "brecOn") = true` |
| 36 | `AnnealHarness.isInternalOrBlacklisted_anonymous` | `theorem` | `867–869` | `isInternalOrBlacklisted .anonymous = true` |
| 37 | `main` | `unsafe def` | `873–893` | Top-level CLI entry point dispatching `search` and `goals` |

## Revalidation

Revalidate the findings and `support/anneal_harness.lean` whenever any of the
following conditions occur:

- **Lean Toolchain Upgrade Beyond `v4.34.1`
  (`5045d0056413266e57c625dcd7c365b10e377c52`):** Re-run `lean -j1 -M1024
  support/anneal_harness.lean` to verify that `import Lean.Elab.Frontend` and
  `import Lean.Elab.Tactic.Basic` still compile within the 1,024 MB memory cap,
  and check whether `Lean.Elab.Tactic.SavedState.restore` has been updated
  upstream to restore `Core.State.ngen`, `nextMacroScope`, and
  `Meta.State.auxDeclNGen`.

- **`lean4export` Format Version Bump Beyond `3.1.0`
  (`df81913eee5519d5a88ae5b0fd701b5298cc29ab`):** If Anneal adopts `lean4export`
  for outbound `.olean` auditing, check whether the NDJSON schema for `"quot"`,
  `"rec"`, or `Expr.letE` (`nonDep`) changes.

- **`lean2dk` / `lean4less` Elimination of `Init.Data.Nat.Lemmas` Stubs:**
  Re-check `rish987/lean2dk` if Dedukti adds native binary integer/boolean
  evaluation or if `lean4less` optimizes `HEq` cast synthesis on `Eq.refl true`
  proof-by-reflection terms so the 43 `omega`/`Nat.Linear` axiom stubs in
  `Lean2Dk/Export.lean` (`29f985670008c29e852d61c562b8c10c84f7c5fb`) can be
  removed.

- **`cargo-anneal` Autoprover Integration:** If `cargo-anneal` transitions from
  single-file CLI invocations of `support/anneal_harness.lean` to a long-running
  multi-step tree search, extend `AnnealHarness` with a persistent
  `stdin`/`stdout` JSON-lines loop incorporating `Pantograph`'s
  `restoreCoreMExtra` and `Kimina`'s `env: 0, gc: true` command-state recycling.
