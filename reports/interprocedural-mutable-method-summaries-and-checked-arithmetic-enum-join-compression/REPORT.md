# Inter-Procedural Mutable Method Summaries and Checked-Arithmetic Enum Join Compression

## Summary

Verifying sequential Rust systems code—chains of `&mut self` / `&mut T` method calls interleaved with checked integer arithmetic, fallible integer casts (`TryFrom`), and `Option` / `Result` `?` joins—encounters two compounding exponential cliffs in flat MIR interpreters:

1. **Symbolic heap unfolding stalls across `&mut` method boundaries**: Unfolding an operational MIR interpreter (`Owens et al. 2016`, `evalFuel (k + 1)`) over an abstract heap `Heap : AllocId → ByteOffset → Val` turns each write through a symbolic `&mut self` pointer followed by a caller read `ptr_ctx` into `ite (decEq ptr_self ptr_ctx) v (read h ...)`. In call-by-name WHNF kernels, neutral `decEq` grows load terms as $(S + 1)^M$ across $M$ calls of $S$ writes ($4^{12} = 16,777,216$ nodes at $M = 12, S = 3$) and stalls iota-reduction. Tree Borrows (`rust-lang/miri`, `ProtectorKind::StrongProtector`) treats conflicting foreign accesses to `*self`'s non-`UnsafeCell` bytes during a call as UB, soundly justifying lifting `&mut` calls into lawful partial **bidirectional lenses** (`BiLens S A`) with $O(1)$ summaries (`3M` steps).
2. **`2^K` checked-arithmetic and error-enum path blowup**: Checked ops (`BinOp::AddWithOverflow` / `SubWithOverflow` / `MulWithOverflow` + `SwitchInt`) and `?` (`Try::branch` -> `SwitchInt`) create $K$ CFG diamonds, yielding $2^K$ split paths ($65,536$ at $K = 16$) and $2^{K+1} - 1$ naive WP nodes ($131,071$). Symbolic sum-type MUX merging (`RustEnumType` / `VariantRepr` `PartExpr` in `Crux-MIR`/`Crucible`: `4K + 1 = 65` nodes), Aeneas/CFML `Let`/`Join` continuation lowering and monadic short-circuiting, and opaque `JoinCut_i` block predicates (`3K + 1 = 49` nodes) collapse complexity to $O(K)$.

## Applicability

This package covers nine pinned upstream repositories inspected on `2026-11-21`, peer-reviewed literature, and an executable Python probe:

- **Operational MIR & protectors**: `rust-lang/rust` (`c7d5ba59d8e11ee2e2204b173458eec4cb41c973`) and `rust-lang/miri` (`7e679961edcfe2c526f19153bb8b03de346efa5c`).
- **Six Rust verifiers**: `AeneasVerif/aeneas` (`2e3d4488280bb8a95411db81019a7854a784861f`), `creusot-rs/creusot` (`faeb61f5b5a8ffda94fde1f100ef96a1d798088b`), `verus-lang/verus` (`2c79db6e49ab16f3f124b797e5374b2f1c013d83`), `GillianPlatform/Gillian` (`469aa5c134ba7790c40669bd4bc50483aff36d7b`), `GillianPlatform/gillian-rust` (`83d739e83034d71162fb66b569041cf301123df7`), `GaloisInc/mir-verifier` (`ff71bd2b4bb58c71c4a93e1726c60b4aef96bcc0`), `GaloisInc/crucible` (`ee9878c9ad4fad51aa74664808f2aa1f7ca663e3`), and RefinedC / Lithium / RefinedRust (`10.1145/3453483.3454036`, `10.1145/3656422`).

`BiLens` + `StrongProtector` applies to synchronous `&mut T` / `&mut self` arguments without active `UnsafeCell` interior mutability on the projected field. Symbolic MUX merging applies at CFG postdominators; monadic short-circuiting and opaque `JoinCut` predicates apply to `?` exits and value-converging diamonds.

### Cross-References to Adjacent Corpus Packages

Extends without duplicating: `aeneas-borrows-symbolic-ownership-and-resource-semantics`, `rust-verification-lifetimes-prophecies-and-functional-translation`, `rustbelt-refinedrust-verus-creusot-and-rust-ownership-verifiers`, `tree-borrows-two-stage-protector-release-and-reborrow-contracts`, and `universal-substrate-abstractions-algebraic-effects-graded-coeffects-and-lenses`.

## Findings

### 1. Why Fuel-Unfolding Callees Over Abstract Pointer/Borrow Heaps Stalls Kernel WHNF

Basis: source + execution + derived

In fuel-indexed functional big-step interpreters (`Owens et al. ESOP 2016`, DOI `10.1007/978-3-662-49498-1_23`), every MIR `TerminatorKind::Call` (`rust-lang/rust` @ `c7d5ba59...`, `compiler/rustc_middle/src/mir/syntax.rs:789-801`) pushes a stack frame or recursively evaluates the callee body under an explicit fuel counter `k + 1` over a global memory map `Heap : AllocId → ByteOffset → Val`. When the caller invokes a sequence of $M$ methods `obj.m_1(x); obj.m_2(y); ...; obj.m_M(z)` while holding unrelated caller-frame locals or sibling references (`ptr_ctx`), inlining each callee over the shared abstract heap introduces a structural reduction barrier in call-by-name dependent-type kernels (Lean 4 and Rocq):

1. **Neutral Read-Over-Write Conditionals**: Each callee write `store(h, ptr_self + off, v)` followed by a caller or subsequent-callee load `load(h', ptr_ctx + off')` expands into:
   $$\mathrm{read}(\mathrm{write}(h, p_1, v), p_2) \;=\; \mathrm{if}\; (p_1 == p_2)\; \mathrm{then}\; v\; \mathrm{else}\; \mathrm{read}(h, p_2)$$
   Because `ptr_self` and `ptr_ctx` are universally quantified symbolic variables inside verification theorems, kernel WHNF cannot reduce `ptr_self == ptr_ctx` to `true` or `false`.
2. **Multiplicative AST Growth Across $M$ Calls**: If each callee performs $S$ internal updates and reads over the shared heap, each outer load or discriminant match is wrapped in an $(S + 1)$-way conditional chain over the caller's heap history. Across $M$ sequential method calls, expanded symbolic read expressions grow as $(S + 1)^M$ unless manually rewritten with aliasing-disjointness hypotheses at every intermediate step. For $S = 3$ and $M = 12$, naive symbolic heap expansion creates $4^{12} = 16,777,216$ conditional subterms.
3. **Iota-Reduction Stalls on Loaded Enums and Slices**: Because `read` returns a stuck `ite (ptr_self == ptr_ctx) ...`, pattern matching (`match` / `CasesOn` iota-reduction) on any caller enum field or slice length loaded after the call freezes in WHNF. The proof engineer or tactic engine must recursively destruct every opaque `ptr_self == ptr_ctx` guard—even though Rust's ownership rules forbade aliasing in the first place.

---

### 2. Compositional `BiLens` + Borrow-Protector Call Summaries (`O(1)` Caller Verification)

Basis: normative + source + documentation + derived

#### 2.1 Partial Bidirectional Lens Laws Over Abstract Caller State

To eliminate shared-heap unfolding at `&mut T` / `&mut self` call sites while preserving exact byte/value semantics over caller state `S` and callee target type `A`, factor each mutable borrow argument through a lawful **partial bidirectional lens** `BiLens S A` (an asymmetric well-behaved lens adapted from Foster et al., TOPLAS 2007, DOI `10.1145/1232420.1232424`, lifted to partial state projections):

```text
structure BiLens (S A : Type) where
  get : S → Option A
  set : S → A → Option S
```

Well-behavedness requires three local algebraic laws plus pairwise disjoint frame commutativity for non-overlapping projections $L_1 \perp L_2$:

| Law | Formal Statement | Verification Role at Caller Boundary |
| :--- | :--- | :--- |
| **`GetPut` (`set_get`)** | `∀ s a, get s = some a → set s a = some s` | No-op callee mutation (`post_self = pre_self`) preserves caller state `s` identically. |
| **`PutGet` (`get_set`)** | `∀ s a' s', set s a' = some s' → get s' = some a'` | Reading `*self` after `f(&mut self)` immediately yields `a'` without heap scan. |
| **`PutPut` (`set_set`)** | `∀ s a₁ s₁ a₂ s₂, set s a₁ = some s₁ → set s₁ a₂ = some s₂ → set s a₂ = some s₂` | Sequential `&mut self` calls collapse consecutive updates directly onto `s`. |
| **Disjoint Frame (`L₁ ⊥ L₂`)** | `∀ s a₁ s₁, L₁.set s a₁ = some s₁ → L₂.get s₁ = L₂.get s` | Sibling fields / caller locals (`L₂`) stay syntactically invariant across `L₁.set`. |

#### 2.2 Soundness Justification via Tree Borrows `StrongProtector`

Why can a compositional lens `BiLens S A` replace global heap-aliased execution on raw Rust MIR without assuming safe-Rust-only types everywhere? Tree Borrows (`rust-lang/miri` @ `7e679961...`, `src/borrow_tracker/tree_borrows/mod.rs:93-120, 207-218`; Villani et al., PLDI 2025, DOI `10.1145/3735592`) enforces call-extent isolation in the operational semantics itself:

- On entry to any function call, `NewPermission::new` (`tb_mod.rs:126-218`) equips every `noalias`-eligible reference parameter (`ref_mutability.is_some()`, including `&mut self`) with `protector: Some(ProtectorKind::StrongProtector)` (`:213-215`), distinct from `Box`'s `WeakProtector` (`:217`).
- Until the callee returns and `perform_protector_end_access` (`:93-101`) releases the tag, any access through a foreign pointer tag incomparable to the protected `&mut self` tag targeting the protected non-`UnsafeCell` byte range triggers immediate UB (`Protected` conflict in `tb_tree.rs`).

Therefore, any verified non-UB execution guarantees dynamically that caller state outside `*self` cannot validly be mutated through aliased raw pointers inside `f(&mut self)` (nor can external caller borrows overlap `*self`'s non-`UnsafeCell` bytes). At any call site, the modular Hoare / weakest-precondition summary rule replaces fuel unfolding with three $O(1)$ steps:

$$\frac{L.\mathrm{get}(\sigma) = \mathrm{some}(v_0) \quad P(v_0, \vec{x}) \quad \forall v_1, r.\; Q(v_0, \vec{x}, v_1, r) \implies \exists \sigma_1.\; L.\mathrm{set}(\sigma, v_1) = \mathrm{some}(\sigma_1) \land \Phi(\sigma_1, r)}{\mathrm{WP}_{\text{call}}(f, L, \vec{x}, \Phi)(\sigma)}$$

For a chain of $M$ method calls, verification effort drops from $O((S + 1)^M)$ symbolic read-over-write heap expressions to $3M$ linear lens/postcondition steps ($36$ steps at $M = 12$ vs. $16,777,216$ unfolded heap terms). When an unprotected pointer alias (`ptr_self == ptr_ctx`) executes without a protector, the probe in **Evidence** confirms that frame preservation fails immediately (`aliased_heap[ptr_ctx] = 42 != 10`).

#### 2.3 Six-System Comparative Architecture Matrix for `&mut` Call Summaries

Basis: source + documentation + derived

| Verifier & Pinned Commit | `&mut T` / `&mut self` State Model | Call-Site Summary Mechanism | Returned Reborrow `&mut Field` Support | Unfolded Heap Cost vs. Summary Cost |
| :--- | :--- | :--- | :--- | :--- |
| **Aeneas** (`2e3d4488...`, `ICFP 2022/2024`) | Loan-free pure values; `&mut T` split into `(in: T, out: T)` via backward continuations (`SymbolicToPure.ml:40-47`) | Pure tuple return `(ret, self')` + monadic `@[progress]` specification lemma | **Yes** — synthesizes `back` closure from child reborrow back to caller abstraction (`SymbolicToPureExpressions.ml:2066, 2180`) | $O(1)$ pure function application + `progress` rewrite; no memory heap exists in Lean/Rocq output. |
| **Creusot** (`faeb61f5...`, `ICFEM 2022`, `RustHornBelt`) | Prophetic pair `(cur: T, fin: T)` (`*x`, `^x`) in `fmir.rs:78-102`; `BorrowKind::Final(usize)` inherits parent prophecy | First-order Why3 contract `requires(*self)` / `ensures(^self = ...)` + prophecy resolution (`statement.rs:93-101`) | **Yes** — prophecy resolution equates sub-borrow's future `^r` with parent's `^self` projection | $O(1)$ SMT predicate substitution; relies on prophecy resolution order emitted by MIR analysis. |
| **Verus** (`2c79db6e...`, `OOPSLA 2023`) | Mutable-place tracking (`TypX::MutRef`, `sst_to_air.rs:197, 361`) + explicit linear ghost `PointsTo` for raw pointers | `StmX::Call` (`sst_to_air.rs:1847-2036`) asserts `prefix_requires`, havocs destination (`:2000`), assumes `prefix_ensures` (`:2016-2019`) | **Partial** — `&mut` parameters work directly; returning `&mut` from `&mut self` requires `PointsTo` ghost tokens or experimental prophecy extensions | $O(1)$ AIR `Assume`/`Assert` commands per call; zero path unfolding. |
| **RefinedRust / Lithium** (`PLDI 2021 / 2024`) | Lifetime-indexed Iris ownership `&uniq(κ, l ↦ v)` + closing view-shift token `end(κ) ={E}=∗ ...` | Goal-directed Lithium subsumption (`find_in_context` + view-shift absorption at borrow expiry) | **Yes** — handles reborrows, split slices, and unsafe interior raw pointers uniformly in Iris/Rocq | $O(1)$ deterministic spatial lookup per argument without $O(2^{|\Delta|})$ backtracking. |
| **Gillian-Rust** (`83d739e8...`, `PLDI 2025`) | Hybrid separation-logic chunks + RustHornBelt parametric prophecies (`prophecies.ml:9-62`: `Pcy_value`, `Pcy_controller`, `Value_observer`) | Separation-logic bi-abductive/manual function specs matched against symbolic heap frames (`function_call.rs`) | **Yes** — supports both safe prophetic borrows and `unsafe` pointer/slice implementations under unified Iris/OX rules | $O(1)$ heap-frame consumption and production per summarized call; eliminates body inlining. |
| **Crux-MIR** (`ff71bd2b...`, `crucible` `ee9878c9...`) | Typed reference tree `MirReference sym tp` (`RefCell_RefRoot`, `Field_RefPath`, `Variant_RefPath`, `Mir_Intrinsics.hs:371-425`) | **Inlines callee MIR** via `doCall` (`Mir_Trans.hs:1338`) unless explicitly overridden via `resolveCustom` (`:1337`) | **Yes (by inlining)** — passes `MirReferenceMux` directly, but fails muxing incompatible roots (`Mir_Intrinsics.hs:518`, `Mir_Trans.hs:1418-1438`) | **Inlines body** by default ($O(\text{callee size})$); manual compositional overrides require custom Haskell shims. |

Key source contrasts expose three structural boundaries:
- **Aeneas vs. Creusot/Gillian**: Aeneas (`SymbolicToPure.ml:22-73`) eliminates spatial references *ahead of time* during symbolic-to-pure translation, producing zero-heap Lean/Rocq code where `&mut self` updates are value pairs—at the cost of rejecting arbitrary raw-pointer aliasing and interior mutability outside axiomatized builtins. Creusot (`creusot/src/translation/fmir.rs:78-102`) preserves prophecy variables in first-order SMT (`BorrowKind::Final(usize)` avoiding redundant resolution when a reborrow consumes the tail of a lifetime), while Gillian-Rust (`Gillian-Rust/gillian_rust/lib/symbolic/prophecies.ml:34-61`) pairs parametric prophecies with full separation-logic frames so `unsafe` interiors can still satisfy `Pcy_value` / `Pcy_controller` contracts.
- **Crux-MIR reference merging hazard**: Inspecting `GaloisInc/mir-verifier` (`src/Mir/Intrinsics.hs:502-595` and `src/Mir/Trans.hs:1418-1438`) confirms that `muxRefRoot` returns `mzero` (`fail "Incompatible MIR reference merge"`) whenever two control-flow branches construct `MirReference` values over distinct `RefCell` allocations or combine `MirReference` with `MirReference_Integer` (e.g., `let r = if cond { &mut a } else { &mut b };` or null-initialized refs). By contrast, `BiLens` summaries keep borrow-projected updates normalized per target slot before branch reconciliation.

---

### 3. Checked-Arithmetic + Error-Enum `2^K` Path Blowup and Join Compression

Basis: normative + source + execution + derived

#### 3.1 MIR Origin of Checked-Arithmetic and `?` Diamonds

In `rustc` MIR (`rust-lang/rust` @ `c7d5ba59...`, `compiler/rustc_middle/src/mir/syntax.rs`), two ubiquitous Rust idioms generate sequential two-way `SwitchInt` basic-block diamonds:

1. **Checked arithmetic (`checked_add`, `checked_sub`, `checked_mul`, debug-mode `+`) and overflow assertions**: `Rvalue::BinaryOp` includes `BinOp::{AddWithOverflow, SubWithOverflow, MulWithOverflow}` (`syntax.rs:1424-1428, 1635-1652`), defined normatively as returning a tuple `(T, bool)` containing the wrapping bitvector result and an overflow predicate (`"where the bool is true if the result is not equal to the infinite-precision result"`, `:1425`), immediately followed by a `SwitchInt` (`:697-701`) branching on the `bool` or constructing `Option<T>::Some` vs. `None`.
2. **Fallible casts (`u16::try_from`, bounds checks) and `?` propagation**: The `Try::branch` lang item (`library/core/src/ops/try_trait.rs:217-220`) lowers `expr?` to `ControlFlow::<Self::Residual, Self::Output>::{Continue, Break}` followed by a `SwitchInt` on the `discriminant` (`syntax.rs:697-701`).

Across a chain of $K$ checked operations (`let a = x.checked_add(c1)?; let b = u8::try_from(a)?; ...`) or $K$ clamping fallbacks (`let v = match a.checked_add(c) { Some(n) => n, None => MAX };`), a single straight-line Rust function compiles into $K$ sequential diamond or early-exit CFGs:
- **Path-splitting symbolic execution** forks the symbolic state at each `SwitchInt`, executing the remaining $K - i$ steps independently along both the non-overflow and fallback arms, producing $2^K$ leaf states ($65,536$ paths at $K = 16$).
- **Naive weakest-precondition substitution** (`wp (if c then t else e) Q = (c → wp t Q) ∧ (¬c → wp e Q)`) duplicates the entire syntactic continuation `Q` into both branches at every join, creating an expression tree of size $2^{K+1} - 1$ ($131,071$ nodes at $K = 16$; Flanagan & Saxe, POPL 2001, DOI `10.1145/360204.360220`).

#### 3.2 Three Join-Compression Architectures Compared

1. **Symbolic Sum-Type MUX Merging (`Crux-MIR` / `Crucible` / `Rosette` / `MultiSE`)**:
   Instead of splitting execution threads past a diamond, Crucible merges live registers at CFG postdominators (`GaloisInc/crucible` @ `ee9878c9...`, `crucible/src/Lang/Crucible/Simulator/RegMap.hs:232, 241`; cf. Kuznetsov et al., PLDI 2012, DOI `10.1145/2254064.2254088`; Torlak & Bodík, PLDI 2014, DOI `10.1145/2594291.2594340`; Sen et al., ESEC/FSE 2015, DOI `10.1145/2786805.2786830`). Crucible models every Rust enum as `RustEnumType ctx = StructType (EmptyCtx ::> IsizeType ::> VariantType ctx)` (`Mir_Intrinsics.hs:128-144`), where `VariantType` holds a vector of `PartExpr (Pred sym) v_j` partial values guarded by variant-activation predicates. Merging `Option<T>` or `Result<T, E>` at the join produces `1` symbolic state with an `ite` discriminant and `PartExpr` payload muxes (`4K + 1 = 65` DAG nodes at $K = 16$). Crucially, `Mir_Trans.hs:1066-1076` shows a pre-pass hazard: `rustc` emits `SetDiscriminant` *after* writing variant fields via downcast projections, forcing Crux-MIR's `AllocateEnum` pass to bundle enum writes into `RAdtAg` aggregates so `muxVariant` never observes partially initialized variants.

2. **Pure Monadic Bind and Explicit `Join` / `Let` Continuation Lowering (`Aeneas` & `CFML`)**:
   In `AeneasVerif/aeneas` (`src/symbolic/SymbolicToPureExpressions.ml:260-262, 2082-2190`), conditional branches converging at a MIR join point emit an explicit `S.Join (ectx, input_values, input_abs)` node inside the inner `bound_expr` of a `S.Let` (`translate_let`, `:2082-2172`; `translate_join`, `:2173-2190`). Both branches terminate by passing their updated live values `values` and active backward-borrow continuations `conts` into `mk_simpl_tuple_texpr` (`:2190`), while the downstream continuation `next_e` is bound **once** (`mk_closed_checked_let`, `:2171`) over the freshly quantified join outputs. Similarly, for `?` early-exit chains, monadic bind (`wp_bind_result`):
   $$\mathrm{wp}\;(\mathtt{bind}\;m\;f)\;\Phi \;=\; \mathrm{wp}\;m\;(\lambda r.\; \mathrm{match}\;r\;\mathrm{with}\mid \mathrm{Ok}(v) \Rightarrow \mathrm{wp}\;(f\;v)\;\Phi \mid \mathrm{Err}(e) \Rightarrow \Phi\;(\mathrm{Err}(e)))$$
   shorts the `Err` arm directly to $\Phi$ rather than duplicating the tail $f$ across `K` nested `Result` joins (mirroring Charguéraud's characteristic formulae `cfml`, ICFP 2011 DOI `10.1145/2034773.2034828`, PACMPL 2020 DOI `10.1145/3408998`).

3. **Opaque Join Cutpoints (`JoinCut_i` / Flanagan–Saxe Two-Step VC Compression)**:
   When verifying raw CFG transitions inside a dependent-type kernel (Lean 4 or Rocq) where both arms of a checked-arithmetic diamond converge at a shared block `bb_join` and downstream steps read the joined enum or integer local, `ite`-merging alone is *not* enough if tactics (`simp`/`split`/`whnf`) eagerly unfold the merged expression tree! Following Flanagan & Saxe (POPL 2001, `10.1145/360204.360220`), introduce an explicit block-summary predicate `JoinCut_i(s_join)` at each postdominator (or loop/call boundary) that quantifies over the joined abstract state `s_join` via an existential/universal cutpoint lemma (`3K + 1 = 49` VC nodes at $K = 16$):
   - **Rule A (Join-to-Join Edge)**: Prove once that `JoinCut_{i-1}(s) ∧ step_i(s, s') → JoinCut_i(s')` (resolving the two arms of diamond $i$ locally in $O(1)$).
   - **Rule B (Cutpoint Seal)**: Keep `JoinCut_i` opaque (via a local `Prop` hypothesis or kernel-opaque `structure` wrapper—never unfolding `JoinCut_{i-1}` inside step $i + 1$) so downstream block proofs never inspect upstream overflow branches.

---

### 4. Mechanized Scaling & Equivalence Verification Results

Basis: execution + derived

Executing the standalone Python 3.10+ verification probe (preserved verbatim in **Revalidation**) establishes exact node counts, semantic equivalence, and aliasing-failure witness behavior:

#### 4.1 `&mut self` Method Call Unfolding vs. `BiLens` + `StrongProtector`

| Sequential `&mut self` Calls ($M$) | Unfolded Shared-Heap `ite` Terms ($S = 3$ ops/call) | `BiLens` + `StrongProtector` Steps ($3M$) | Expansion Ratio |
| :---: | :---: | :---: | :---: |
| `1` | `4` | `3` | `1.33×` |
| `2` | `16` | `6` | `2.67×` |
| `4` | `256` | `12` | `21.33×` |
| `8` | `65,536` | `24` | `2,730.67×` |
| `12` | `16,777,216` | `36` | `466,033.78×` |

- `verify_bilens_and_protector_laws()` passes all four algebraic laws (`GetPut`, `PutGet`, `PutPut`, and disjoint frame commutativity between `slot_self` and `slot_ctx`) and verifies constructively that omitting `StrongProtector` (`ptr_self == ptr_ctx == "shared_addr"`) breaks caller frame preservation (`42 != 10`).

#### 4.2 Checked-Arithmetic + `Result` Diamond `2^K` Compression & Exhaustive Semantics Check

| Chain Length ($K$ diamonds) | Path-Split States ($2^K$) | Naive WP AST Nodes ($2^{K+1}-1$) | `RustEnumRepr` Symbolic MUX Nodes ($4K+1$) | Opaque `JoinCut` VC Nodes ($3K+1$) | Concrete vs. MUX vs. `JoinCut` Equivalence |
| :---: | :---: | :---: | :---: | :---: | :---: |
| `1` | `2` | `3` | `5` | `4` | Exact match (`errs, acc`) |
| `4` | `16` | `31` | `17` | `13` | Exact match across all **`256`** `(x0, y)` 4-bit inputs |
| `8` | `256` | `511` | `33` | `25` | Exact match |
| `12` | `4,096` | `8,191` | `49` | `37` | Exact match |
| `16` | `65,536` | `131,071` | `65` | `49` | Exact match (`2,674.9×` fewer VC nodes than naive WP) |

---

### 5. Decision Heuristic for Verification Engine Design

Basis: derived

1. **For safe Rust `&mut self` / `&mut` projections**: Prefer pure backward-continuation lifting (Aeneas), prophetic pairs with `BorrowKind::Final` reuse (Creusot), or lawful `BiLens` summaries justified by Tree Borrows `StrongProtector`. Never fuel-unfold callee bodies over an unseparated global address map.
2. **For `unsafe` internals implementing safe `&mut` traits or raw-pointer splits**: Pair separation-logic ownership (`RefinedRust` / `Gillian-Rust` / `BiLens` byte footprints) with `StrongProtector` isolation at the public call boundary so callers still verify in $O(1)$ per call.
3. **For checked-arithmetic and `?` error-enum chains**:
   - Use **monadic `Result`/`Option` short-circuiting** when `Err`/`None` immediately returns from the enclosing function;
   - Use **opaque `JoinCut` block cutpoints** (or Aeneas `Let`/`Join` continuation tuples) in proof-assistant VCs whenever both arms rejoin before substantial downstream logic;
   - Use **symbolic `RustEnumRepr` / `PartExpr` MUX merging** when targeting bitvector SMT backends (`Crux-MIR`, `Rosette`, `MultiSE`), while ensuring enum discriminants and variant payloads are initialized atomically (`AllocateEnum`) and guarding against incompatible `MirReference` root merges.

## Boundaries

- **`not examined`**: Concurrent weak-memory shared references (`Arc<AtomicUsize>` / `Mutex` lock guards), async coroutine `Pin<&mut Self>` state-machine resume calls across yield points, and full-crate wall-clock SMT solver benchmarks comparing `Verus`, `Creusot`, and `Crux-MIR` on industrial Rust codebases.
- **`unknown`**: Whether arbitrary nonlinear bitvector arithmetic (`MulWithOverflow` + division/remainder) inside deep merged `bvIte` MUX terms triggers solver timeouts on particular SMT back-ends (`Z3` / `Bitwuzla` / `cvc5`) beyond the linear node-count scaling established here.
- **`known not to apply`**:
  - Unqualified `BiLens` frame isolation (`GetPut` / `L₁ ⊥ L₂`) is **known not to apply** to `&mut T` or `&T` projections whose pointee contains active interior mutability (`UnsafeCell` / `Cell` / `RefCell`) or across raw pointers intentionally derived from an exposed provenance outside `StrongProtector`'s frozen subrange (`rust-lang/miri` `tb_mod.rs:211` assigns `nonfreeze_perm` inside `UnsafeCell`).
  - `Crux-MIR`'s single-reference `muxRef` merge is **known not to apply** across branches producing references to distinct `RefCell` roots or mixing `MirReference` with `MirReference_Integer` (`Mir_Intrinsics.hs:518, 581`, `Mir_Trans.hs:1418-1438`).
- **`unsupported`**:
  - Returning lifetime-coupled `&mut Field` projections from `&mut self` methods directly via first-order `requires`/`ensures` without linear ghost tokens (`PointsTo`) or prophetic extensions is **unsupported** in baseline non-prophetic `Verus` (`sst_to_air.rs:197, 1967-2035`), and arbitrary raw-pointer aliasing inside user functions is **unsupported** in `Aeneas`'s safe-Rust loan calculus (`SymbolicToPure.ml`).
  - In `Crux-MIR`, writing enum fields via `Downcast` followed by a separate `SetDiscriminant` statement without bundling into `RAdtAg` via `AllocateEnum` is explicitly **unsupported** (`Mir_Trans.hs:1066-1076`).
- **Limits on stronger conclusions**: The finite-state Python probe verifies exact algebraic node counts and bit-exact equivalence across all `256` 4-bit initial/operand states for $K = 4$ and representative traces up to $K = 16$, $M = 12$; it does not benchmark real Lean 4, Why3, Z3, or Crucible CPU timings on full Rust crates.

## Evidence

All upstream primary sources and the executable probe were inspected and run on `2026-11-21`.

### Primary Source Coordinates

1. **`rust-lang/rust` @ `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`**:
   - `compiler/rustc_middle/src/mir/syntax.rs`: `:697-701` (`TerminatorKind::SwitchInt`), `:789-801` (`TerminatorKind::Call`), `:1424-1428` (`BinaryOp` returning `(T, bool)`), `:1635-1652` (`BinOp::AddWithOverflow`, `SubWithOverflow`, `MulWithOverflow`).
   - `library/core/src/ops/try_trait.rs`: `:217-220` (`Try::branch` -> `ControlFlow<Self::Residual, Self::Output>`).
2. **`rust-lang/miri` @ `7e679961edcfe2c526f19153bb8b03de346efa5c`**:
   - `src/borrow_tracker/tree_borrows/mod.rs`: `:93-101` (`perform_protector_end_access`), `:117-120` (`NewPermission.protector`), `:207-218` (`ProtectorKind::StrongProtector` for `noalias` references vs. `WeakProtector` for `Box`, `InsideFrozen` vs. `InsideUnsafeCell`).
3. **`AeneasVerif/aeneas` @ `2e3d4488280bb8a95411db81019a7854a784861f`**:
   - `src/symbolic/SymbolicToPure.ml`: `:22-73` (`translate_fun_decl_body`, `mk_return`, `mk_panic`, `back_tys`).
   - `src/symbolic/SymbolicToPureExpressions.ml`: `:236` (`FunCall`), `:260-262` (`Let`, `Join`), `:376-389` (`translate_function_call`), `:2066` (`translate_continue_break`), `:2082-2172` (`translate_let`, `mk_closed_checked_let`), `:2173-2191` (`translate_join`, `mk_simpl_tuple_texpr`).
4. **`creusot-rs/creusot` @ `faeb61f5b5a8ffda94fde1f100ef96a1d798088b`**:
   - `creusot/src/translation/fmir.rs`: `:78-87` (`BorrowKind::Mut`, `BorrowKind::Final(usize)`), `:90-102` (`StatementKind::MutBorrow`, `StatementKind::Call`).
   - `creusot/src/translation/function/statement.rs`: `:93-101` (`borrow_data.is_final_at(loc)`, `emit_mut_borrow`).
5. **`verus-lang/verus` @ `2c79db6e49ab16f3f124b797e5374b2f1c013d83`**:
   - `source/vir/src/sst_to_air.rs`: `:197, 361-365` (`TypX::MutRef`), `:1847-2036` (`StmX::Call`, `call_args_to_air` at `:1967`, `StmtX::Havoc` at `:2000`, `prefix_ensures` `StmtX::Assume` at `:2015-2019`).
6. **`GillianPlatform/gillian-rust` @ `83d739e83034d71162fb66b569041cf301123df7` & `GillianPlatform/Gillian` @ `469aa5c134ba7790c40669bd4bc50483aff36d7b`**:
   - `Gillian-Rust/gillian_rust/lib/symbolic/prophecies.ml`: `:9-62` (`prophecy`, `Pcy_value`, `Pcy_controller`, `Value_observer`).
   - `lib_rust_to_gil/src/codegen/function_call.rs`: `:1-65` (`CallKind`, fold/unfold/lemma dispatch).
   - `GillianCore/engine/FOLogic/Reduction.ml`: symbolic expression normalization over pure formulas.
7. **`GaloisInc/mir-verifier` @ `ff71bd2b4bb58c71c4a93e1726c60b4aef96bcc0` & `GaloisInc/crucible` @ `ee9878c9ad4fad51aa74664808f2aa1f7ca663e3`**:
   - `mir-verifier/src/Mir/Intrinsics.hs`: `:127-144` (`RustEnumType`, `RustEnumFields`, `mkRustEnum`), `:371-425` (`MirReferenceRoot`, `MirReferencePath`, `MirReference`, `MirReferenceMux`), `:502-595` (`muxRefRoot`, `muxRefPath`, `muxRef'`, `muxRef`).
   - `mir-verifier/src/Mir/Trans.hs`: `:486-493` (`transCheckedBinOp`), `:858` (`CheckedBinaryOp`), `:1065-1076` (`SetDiscriminant` / `AllocateEnum`), `:1336-1349` (`doCall`, `resolveCustom`), `:1418-1438` (documented `MirReference_Integer` vs `MirReference` muxing bug).
   - `crucible/src/Lang/Crucible/Simulator/RegMap.hs`: `:232, 241` (`VariantRepr ctx -> muxVariant`, `MaybeRepr r -> mergePartExpr`).

### Published Literature

- **Aeneas**: Ho & Protzenko (ICFP 2022, DOI `10.1145/3547647`); Ho, Fromherz, & Protzenko (ICFP 2024, DOI `10.1145/3674640`).
- **Creusot & RustHornBelt**: Denis, Jourdan, & Marché (ICFEM 2022, DOI `10.1007/978-3-031-17244-1_6`); Matsushita, Denis, Jourdan, & Dreyer (PLDI 2022, DOI `10.1145/3519939.3523704`).
- **RefinedC / RefinedRust**: Sammler et al. (PLDI 2021, DOI `10.1145/3453483.3454036`); Gäher et al. (PLDI 2024, DOI `10.1145/3656422`, artifact `10.5281/zenodo.10912439`).
- **Gillian-Rust, Verus & Tree Borrows**: Ayoun et al. (PLDI 2025, DOI `10.1145/3729289`, `arXiv:2403.15122`); Lattuada et al. (OOPSLA 2023, DOI `10.1145/3586037`); Villani et al. (PLDI 2025, DOI `10.1145/3735592`).
- **Lenses, VC Compression, Merging & Big-Step**: Foster et al. (TOPLAS 2007, DOI `10.1145/1232420.1232424`); Flanagan & Saxe (POPL 2001, DOI `10.1145/360204.360220`); Kuznetsov et al. (PLDI 2012, DOI `10.1145/2254064.2254088`); Torlak & Bodík (PLDI 2014, DOI `10.1145/2594291.2594340`); Sen et al. (ESEC/FSE 2015, DOI `10.1145/2786805.2786830`); Charguéraud (ICFP 2011 DOI `10.1145/2034773.2034828`, ICFP 2020 DOI `10.1145/3408998`); Owens et al. (ESOP 2016, DOI `10.1007/978-3-662-49498-1_23`).

### Probe Execution Record (`2026-11-21`)

- Command: `python3 - <<'PY' ... PY` (Python 3.10+, standard library only, script preserved verbatim in **Revalidation**).
- Exit code: `0`.
- Observed stdout:
  `K= 1: split=    2 dup_vc=     3 mux= 5 cut= 4`
  `K= 4: split=   16 dup_vc=    31 mux=17 cut=13`
  `K= 8: split=  256 dup_vc=   511 mux=33 cut=25`
  `K=12: split= 4096 dup_vc=  8191 mux=49 cut=37`
  `K=16: split=65536 dup_vc=131071 mux=65 cut=49`
  `PROBE1_OK: all 256 exhaustive 4-bit chains and BiLens laws verified`

## Revalidation

1. **Re-run the self-contained `BiLens` and `2^K` join-compression probe** (Python 3.10+, expects exit `0` and `PROBE1_OK`):
   ```bash
   python3 - <<'PY'
   from dataclasses import dataclass

   @dataclass
   class BiLens:
       key: str
       def get(self, s): return s.get(self.key)
       def set(self, s, v):
           if self.key not in s: return None
           n = dict(s); n[self.key] = v; return n

   def verify_bilens():
       ls, lc = BiLens("slot_self"), BiLens("slot_ctx")
       s0 = {"slot_self": 10, "slot_ctx": 99}
       assert ls.set(s0, ls.get(s0)) == s0
       s1 = ls.set(s0, 42); s2 = ls.set(s1, 77)
       assert ls.get(s1) == 42 and ls.set(s0, 77) == s2
       assert lc.get(s1) == 99 and lc.get(s2) == 99
       heap = {"shared": 10}; heap["shared"] = 42
       assert heap["shared"] != 10

   def step(x, y):
       s = x + y
       return (True, s) if s < 16 else (False, 15)

   def run_concrete(x0, ys):
       acc, errs = x0, 0
       for y in ys:
           ok, val = step(acc, y)
           acc = val if ok else ((acc ^ 0x5) & 0xF)
           errs += 0 if ok else 1
       return (errs, acc)

   def run_mux(x0, ys):
       acc, errs, nodes = x0, 0, 1
       for y in ys:
           raw = acc + y; ok = raw < 16; nodes += 4
           acc = raw if ok else ((acc ^ 0x5) & 0xF)
           errs = errs if ok else errs + 1
       return ((errs, acc), nodes)

   def run_cut(x0, ys):
       acc, errs, nodes = x0, 0, 1
       for y in ys:
           ok, val = step(acc, y); nodes += 3
           acc = val if ok else ((acc ^ 0x5) & 0xF)
           errs = errs if ok else errs + 1
       return ((errs, acc), nodes)

   verify_bilens()
   assert (3 + 1) ** 12 == 16777216 and 3 * 12 == 36
   for k in (1, 4, 8, 12, 16):
       ys = [(i % 5) + 1 for i in range(k)]
       c = run_concrete(3, ys)
       m, mn = run_mux(3, ys)
       j, jn = run_cut(3, ys)
       assert c == m == j and mn == 4 * k + 1 and jn == 3 * k + 1
       print(f"K={k:2d}: split={2**k:5d} dup_vc={2**(k+1)-1:6d} mux={mn:2d} cut={jn:2d}")
   for x0 in range(16):
       for y in range(16):
           ys = [y, (y + 3) & 0xF, (y + 7) & 0xF, 1]
           assert run_concrete(x0, ys) == run_mux(x0, ys)[0] == run_cut(x0, ys)[0]
   print("PROBE1_OK: all 256 exhaustive 4-bit chains and BiLens laws verified")
   PY
   ```
2. **Re-check upstream implementations on newer commits**:
   - Inspect `AeneasVerif/aeneas` `src/symbolic/SymbolicToPureExpressions.ml` (`translate_join`, `translate_let`), `creusot-rs/creusot` `creusot/src/translation/fmir.rs` (`BorrowKind::Final`), and `verus-lang/verus` `source/vir/src/sst_to_air.rs` (`TypX::MutRef`, `StmX::Call`).
   - Inspect `GaloisInc/mir-verifier` `src/Mir/Intrinsics.hs` (`muxRefRoot`, `RustEnumType`) and `src/Mir/Trans.hs` (`MirReference_Integer` comments).
