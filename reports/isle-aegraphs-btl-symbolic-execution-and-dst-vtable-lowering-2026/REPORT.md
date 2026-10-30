# Cranelift ISLE, Acyclic E-Graphs (`aegraphs`), `BTL` Symbolic Execution, Checked Arithmetic, and Dynamic DST / VTable Lowering

## Summary

A formally verified Rust compiler targeting RISC-V (`RV64GC` + `Zba` + `Zbb`),
AArch64, and x86-64 must bridge two tightly coupled lowering problems between
post-cleanup MIR and machine assembly:

1. **Verifying Mid-End Peephole Rewriting and Target Instruction Selection
   Inside Anneal's Kernel Axiom Boundary:**
   Anneal's `trusted/audit/TrustedBoundary.lean` and
   `trusted/lean/foundation-lock.json` (`joshlf/anneal` at
   `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`) permit only `[propext,
   Classical.choice, Quot.sound]` and explicitly reject `Lean.ofReduceBool`
   (which rules out `bv_decide` and `native_decide`). We audit Cranelift's ISLE
   compiler (`cranelift-isle` `0.132.0`) and acyclic e-graph optimizer
   (`cranelift-codegen` `0.132.0`, `bytecodealliance/wasmtime` at
   `87282b8fd77fa9fbba6caadb0be690bedec2dc64`) alongside VeriISLE/Crocus,
   `lean-egg`, and Chamois-CompCert's `BTL` symbolic execution engine, and
   mechanize three complementary, `Lean.ofReduceBool`-free verification
   architectures in Lean `v4.34.1`:
   - **Architecture A (Constructive ISLE-Style Term Lowering):** Proving a
     total pattern-matching selector `lowerISLE` once over all `BitVec 64`
     inputs using `BitVec.eq_of_toNat_eq` and `bv_omega` (`lowerISLE_sound`).
   - **Architecture B (Proof-Producing E-Graph Rewrite Traces):** Checking
     untrusted `egg` /`aegraph` equational rewrite certificates
     `List RewriteStep`
     via kernel reduction (`rfl`) and lifting them via `checkRewriteTrace_sound`
     (`dstSliceAddr_verified`).
   - **Architecture C (CompCert `BTL`-Style Superblock Symbolic Execution with
     Partitioned `.rodata` and Stack Stores):** Symbolically executing
     unoptimized
     and optimized superblocks with canonical expression normalization
     (`normExpr` / `normMemExpr`), ordered trap guards (`assertNonZero`),
     immutable `.rodata` vtable loads (`loadRo`), and a symbolic stack store
     buffer (`stackStores` / `symReadStack`), proved sound in
     `validateSuperblock_sound` and `validateSuperblockWithMem_sound`.
   We also formalize Cranelift's `subsume` SSA-dominance rule
   (`aegraph_unsubsumed_union_violates_dominance`) and `loop_hoist_level`
   preheader code motion (`argHoistLevel_not_in_loop`, `pure_loop_hoist_sound`,
   and the negative canary
   `canary_hoist_trapping_div_above_zero_iteration_loop_unsound`).
2. **Lowering Complex Rust MIR Arithmetic, Dynamic DSTs, and VTable Coercions:**
   Through primary-source audits of `rust-lang/rust`
   (`58cf8f9c35b355199727627d07ae34a4e2846d67` and
   `8006091eb71ae7d9e9bccb66c6122c9d68af4466`) and `rust-lang/compiler-builtins`
   (`351d48e4b95f1665cfd3360e3ba8f3dd4d3fb3c1`), we mechanize:
   - **64-Bit and 128-Bit Checked Arithmetic Without `bv_decide`:** Universal
     equivalence of flagless RISC-V unsigned `AddWithOverflow`
     (`riscv_uadd_overflow_iff_spec`), `SubWithOverflow`
     (`cg_clif_usub_overflow_iff_spec`), and 5-instruction signed
     `MulWithOverflow` (`mulh` + `mul` + `srai 63` + `xor` + `snez` in
     `riscv_smul_overflow_bv_iff_spec` and `riscv_smul_xor_snez_iff_spec`,
     discharged via Euclidean division in `omega`), plus 128-bit `U128Pair`
     carry-chaining (`u128_add_pair_correct`), borrow-chaining
     (`u128_sub_pair_correct`), cross-term wrapping multiplication
     (`u128_mul_pair_algebraic_identity`), and `compiler-builtins`
     `UMulo::mulo` (`compiler_builtins_umulo_*`).
   - **Dynamic DST (`[T]`, `str`, `dyn Trait`) Tail Offset and Total Size
     Calculation:** Bit-exact equivalence of `rustc_codegen_ssa` and
     `rustc_codegen_cranelift` upward alignment masks
     (`alignToBV_eq_cg_clif_formula`), `rustc`'s single-rounding
     `size_and_align_of_dst` algebraic identity
     (`rustc_dst_total_size_optimization`), the negative canary refuting static
     header alignment on `Packet<dyn Trait>`
     (`static_header_align_miscomputes_dst_tail_offset`), and a latent
     `ty::Foreign` panic in
     `rustc_codegen_cranelift/src/value_and_place.rs:28-30` .
   - **Rust 1.86+ `VtblEntry::TraitVPtr` Trait Upcasting and `GlobalRelocTable`
     :**
     Primary supertrait prefix reuse vs. secondary supertrait slot loading
     (`coerceDynUpcast_loads_traitVPtr`), automatic discharge of
     `vtableStoredAt` from `.rodata` relocation tables
     (`relocTable_discharges_vtableStoredAt`,
     `relocTable_chained_traitVPtr_stored` ), and a missing
     `flags.set_can_move()`
     in `rustc_codegen_cranelift/src/vtable.rs:8-12` (`vtable_memflags()`).

All results are mechanized across two preserved, zero-`sorryAx`,
zero-`Lean.ofReduceBool` Lean `v4.34.1` probes totaling 2,831 lines:
[`support/track5_isle_egraph_dst_probe.lean`](support/track5_isle_egraph_dst_probe.lean)
(1,089 lines) and
[`support/round2_track4_probe.lean`](support/round2_track4_probe.lean) (1,742
lines).

## Applicability

These findings apply to the combination and interaction of the examined
subjects:

- **Anneal Trusted Boundary (`joshlf/anneal` at
  `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`):**
  Governed by `trusted/audit/TrustedBoundary.lean` and
  `trusted/lean/foundation-lock.json`, which restrict the transitive axiom
  footprint of `Trusted.CrateTheorem` and `VerificationResult` to
  `{propext, Classical.choice, Quot.sound}` and forbid `Lean.ofReduceBool`.
- **Cranelift ISLE and Acyclic E-Graphs (`bytecodealliance/wasmtime` at
  `87282b8fd77fa9fbba6caadb0be690bedec2dc64`):**
  Applies to `cranelift/isle/isle/src/` (`ast.rs`, `sema.rs`, `trie_again.rs`,
  `codegen.rs`) and `cranelift/codegen/src/` (`egraph/mod.rs`, `egraph/cost.rs`,
  `egraph/elaborate.rs`, `opts.rs`, `inst_predicates.rs`, `ir/memflags.rs`,
  `opts/*.isle`, and `isa/{riscv64,aarch64,x64}/{lower.isle,inst.isle}`).
- **Rust Compiler DST, VTable, and Checked Arithmetic Lowering (`rust-lang/rust`
  at `58cf8f9c35b355199727627d07ae34a4e2846d67` and
  `8006091eb71ae7d9e9bccb66c6122c9d68af4466`, and `rust-lang/compiler-builtins`
  at `351d48e4b95f1665cfd3360e3ba8f3dd4d3fb3c1`):**
  Applies to `compiler/rustc_codegen_cranelift/src/` (`num.rs`,
  `codegen_i128.rs`, `unsize.rs`, `vtable.rs`, `value_and_place.rs`),
  `compiler/rustc_codegen_ssa/src/mir/` (`place.rs`, `rvalue.rs`),
  `compiler/rustc_middle/src/ty/vtable.rs`,
  `compiler/rustc_trait_selection/src/traits/vtable.rs`, and
  `compiler-builtins/src/int/mul.rs`.

## Findings

### 1. Cranelift ISLE, VeriISLE/Crocus, and Acyclic E-Graphs (`aegraphs`)

`Basis: source + execution + derived`

#### 1.1 Cranelift ISLE Decision Automaton and Embedded VeriISLE Specifications

In `cranelift/isle/isle/src/{ast.rs,sema.rs,trie_again.rs,codegen.rs}`
(`bytecodealliance/wasmtime` at `87282b8fd77fa9fbba6caadb0be690bedec2dc64`),
ISLE (Instruction Selection and Lowering Expressions) compiles declarative,
prioritized pattern-matching rules (`(rule <prio> <lhs-pattern> <if-lets>*
<rhs-expr>)`) into total or partial Rust functions:

- **Constructors and Extractors (`ast.rs:280-377`):** Every term carries an
  internal or external *constructor* signature (used on the RHS to construct
  CLIF or `MachInst` nodes) and/or *extractor* signature (used on the LHS to
  decompose values). Extractors may be `partial` or `infallible`.
- **Hash-Consed Decision Automaton (`trie_again.rs:10-388`):** `RuleSet` lowers
  each rule into a sequence of `Constraint` steps (`Variant`, `ConstBool`,
  `ConstInt`, `ConstPrim`, `Equal`) over hash-consed `Binding` sites (`Arg`,
  `Extractor`, `Constructor`, `Iterator`, `MakeVariant`, `MatchVariant`,
  `MatchSome`, `MatchTuple`, `MatchEqual`). Specifically, `Binding::Iterator`
  (`trie_again.rs:116-123`) iterates over all e-nodes in an e-class when ISLE
  rules execute over Cranelift's acyclic e-graph. Rules whose constraint sets
  satisfy `Overlap::may_overlap` (`trie_again.rs:312-388`) must be disambiguated
  by explicit integer priority.
- **Embedded VeriISLE / Crocus Specification AST (`ast.rs:16-20, 88-277`):**
  Upstream `cranelift-isle` embeds the VeriISLE/Crocus SMT-LIB bitvector
  specification grammar inside `.isle` files via `Def::Spec`, `Def::Model`,
  `Def::Form`, and `Def::Instantiation`. `SpecOp` (`ast.rs:193-277`) defines
  standard bitvector operations (`BVAdd`, `BVSub`, `BVMul`, `BVAnd`, `BVNot`,
  `BVShl`, `BVUle`, `BVUlt`, `ZeroExt`, `SignExt`, `Extract`, `Concat`),
  overflow predicates (`BVSaddo`), flag-setting subtraction (`Subs`), and memory
  effects (`LoadEffect`, `StoreEffect`), used in live annotations such as
  `cranelift/codegen/src/isa/aarch64/inst.isle:3898-3901` (`amode`) and
  `cranelift/codegen/src/isa/x64/inst.isle:571-579` (`amode_imm_reg_reg_shift`).

| Verification System | Target & Scope | Verification Mechanism | Compatibility with Anneal `TrustedBoundary.lean` |
| :--- | :--- | :--- | :--- |
| **Crocus / VeriISLE** (VanHattum et al., ASPLOS 2024; *Arrival*, OOPSLA 2025) | Cranelift ISLE lowering rules (`lower.isle`, `inst.isle`) against Sail/ASL ISA semantics | Translates each ISLE rule and helper `(spec ...)` contract into SMT-LIB bitvector VCs checked offline by Z3/CVC5 | External SMT solver is unverified; requires Lean proof reconstruction or algebraic `BitVec` lemmas to cross `TrustedBoundary.lean` |
| **`lean-egg`** (Rossel & Goens) | Equality saturation in Lean 4 via external Rust `egg` worker | Untrusted `egg` binary emits an equational explanation trace; Lean reconstructs a kernel-checked `Eq.trans` / `congrArg` proof | Zero extra axioms (`[propext, Classical.choice, Quot.sound]`); decouples e-graph search heuristics from the kernel |
| **Chamois-CompCert `BTL`** (`scheduling/BTL_SEsimuref.v`) | Superblock scheduling, CSE, LICM, and peephole strength reduction | Untrusted oracle transforms superblocks; verified checker runs hash-consed symbolic execution (`hval`, `smem`) and validates simulation by `rfl` | Zero extra axioms; validates DAG-level CSE, instruction reordering, trap guards, and partitioned memory in $O(|B|)$ time |

#### 1.2 Acyclic E-Graphs (`aegraphs`) and the `subsume` SSA-Dominance Invariant

Cranelift's mid-end optimization pass (`EGraphPass` in
`cranelift/codegen/src/egraph/{mod.rs,cost.rs,elaborate.rs}`) replaces a
multi-pass CFG optimizer with a single dominator-tree pass over an **acyclic
e-graph (`aegraph`)** embedded in the SSA `DataFlowGraph`:

1. **In-Place Acyclic Representation (`egraph/mod.rs:344-385`):** An e-class is
   represented as an acyclic binary tree of `ValueDef::Union(x, y)` nodes inside
   `dfg.values`, bounded by `ECLASS_ENODE_LIMIT = 5`, `MATCHES_LIMIT = 5`, and
   recursion depth `REWRITE_LIMIT = 5`.
2. **CFG Side-Effect Skeleton and Scoped GVN (`egraph/mod.rs:238-266,
  756-909`):**
   `remove_pure_and_optimize` walks the dominator tree in preorder. Pure
   instructions (`is_pure_for_egraph` in `inst_predicates.rs:46-78` :
   instructions
   without traps, mutable memory effects, control flow, or multi-result returns)
   are unlinked from `func.layout`, leaving only the side-effect skeleton in the
   basic blocks. Each pure node is canonicalized and inserted into
   `gvn_map : ScopedHashMap<(Type, InstructionData), Option<Value>>` at the
   shallowest block where all of its SSA operands are available
   (`get_available_block`).
3. **The `subsume` SSA-Dominance Rule (`opts/README.md` Rule 2,
   `opts.rs:149-155`, `egraph/mod.rs:346-354`):**
   Any rewrite rule whose RHS drops an SSA `Value` operand present on the LHS
   (such as `(band x 0) => 0`, `(bxor x x) => 0`, or `(select 1 x y) => x`)
   **must** wrap its RHS in `(subsume ...)`, replacing the e-class wholesale
   rather than unioning `orig` and `rewritten`. Without `subsume`, unioning
   `orig = (band x 0)` (defined in block `B1` where `x` is in scope) with
   `const 0` (available at the root block `B0`) allows GVN to share that unioned
   e-class with `B0`, where `x` is not in SSA scope!
   In
   [`support/track5_isle_egraph_dst_probe.lean`](support/track5_isle_egraph_dst_probe.lean)
   (lines `327-357`), `aegraph_unsubsumed_union_violates_dominance` mechanizes
   this exact dominance hazard: for `orig := Expr.and_ (.var 1) (.const 0#64)`
   and `rewritten := Expr.const 0#64` at `rootAvail := [0]`,
   `(∀ env, orig.eval env = rewritten.eval env)` and
   `rewritten.wellScoped rootAvail = true`, whereas
   `orig.wellScoped rootAvail = false`.
4. **Multi-Extractor E-Class Hazard (`opts/README.md` Rule 4, `opts.rs:53-115`
  ):**
   Because an ISLE pattern variable `v : Value` ranges over an entire e-class
   via
   `InstDataEtorIter`, matching `v` in two separate `if-let` extractors within
   one rule can bind two different e-nodes inside the same e-class unless the
   pattern decomposes the node in a single extractor.

#### 1.3 `aegraph` Extraction, `loop_hoist_level`, and Trap-Guard Dominance

During extraction (`cranelift/codegen/src/egraph/elaborate.rs:171-220, 540-628,
722-725`), `compute_best_values` selects the minimum-cost e-node per e-class,
and `elaborate_domtree` re-inserts pure instructions on demand. When entering a
loop header `block` with immediate dominator `idom`, `Elaborator::start_block`
pushes `LoopStackEntry { lp, hoist_block: idom, scope_depth }`. For each
elaborated instruction, `loop_hoist_level` (`elaborate.rs:562-583`) computes the
maximum over all operand values of the outermost index in `loop_stack` that does
not contain the operand's defining block; if `loop_hoist_level <
loop_stack.len()`, the instruction is hoisted to the end of
`loop_stack[loop_hoist_level].hoist_block` (`idom`, the loop preheader).

Why does `elaborate.rs:722-725` assert `is_pure_for_egraph(self.func, inst)`
(requiring `!inst.opcode().can_trap()` for ALU ops and
`readonly && notrap && can_move` for loads in `inst_predicates.rs:46-69`)?
Because `hoist_block` (`idom`) executes **unconditionally** before the loop
header's termination branch is tested—even when the loop executes **zero
iterations ($k = 0$)**!

In Section 3 of
[`support/round2_track4_probe.lean`](support/round2_track4_probe.lean) (lines
`1248-1658`), we mechanize `argHoistLevel`, `computeLoopHoistLevel`, and loop
iteration semantics (`execLoopIterations`), proving:
- **`argHoistLevel_not_in_loop` (lines `1314-1332`):** Whenever
  `loopStack[argHoistLevel isInLoop loopStack b]? = some entry`,
  `isInLoop b entry.lp = false`.
- **`pure_loop_hoist_sound` (lines `1551-1616`):** By induction on the trip
  count `k : Nat` (via `loop_hoist_iterations_equiv` and
  `assign_idempotent_when_already_equal`), hoisting a pure, non-trapping
  instruction `LoopInstr.assign dst rhs` whose operands `rhs.vars` are
  loop-invariant (`bodyPreservesRegs dst rhs.vars rest = true`) into the
  preheader preserves exact semantics across **all** trip counts $k \ge 0$
  (where the loop-internal temporary satisfies `dst ∉ liveOut` on $k = 0$, and
  for all registers including `dst` when $k \ge 1$).
- **`canary_hoist_trapping_div_above_zero_iteration_loop_unsound` (lines
  `1642-1657`):** Hoisting a trapping unsigned division `LoopInstr.udiv 3 1 2`
  (`r3 := r1 / r2`) into the preheader above a zero-iteration loop ($k = 0$)
  when
  `r2 = 0#64` causes the hoisted program to trap (`none`) in the preheader while
  the unhoisted loop terminates normally (`some initEnv`).

---

### 2. Three `TrustedBoundary.lean`-Compliant Verification Architectures Without `bv_decide`

`Basis: source + execution + derived`

```
                    MIR / AnSSA Function Body
                                │
         ┌──────────────────────┼──────────────────────┐
         ▼                      ▼                      ▼
  [Architecture A]       [Architecture B]       [Architecture C]
  Constructive ISLE      Untrusted E-Graph      Untrusted Superblock
  Term-Rewriting         Equality Saturation    Scheduler & CSE Oracle
  Lowerer (`lowerISLE`)  (`egg` / `aegraph`)    (Reordering + Memory)
         │                      │                      │
  Structural Induction   Emits `List RewriteStep`      Emits Optimized
  + Universal `BitVec`   Certificate Checked    Superblock Validated by
  Lemmas (`bv_omega`)    by Kernel `rfl`        `validateSuperblockWithMem`
         ▼                      ▼                      ▼
  `lowerISLE_sound`      `checkRewriteTrace_    `validateSuperblockWithMem_
                          sound`                 sound` (`rfl`)
         └──────────────────────┼──────────────────────┘
                                ▼
           Kernel-Checked `Trusted.CrateTheorem` Refinement
             (Axioms: `[propext, Classical.choice, Quot.sound]`)
```

#### 2.1 Architecture A: Constructive ISLE-Style Term Rewriting (`lowerISLE_sound`)

Every primitive algebraic rewrite rule in Cranelift's `opts/` and
`isa/riscv64/lower.isle` can be proved once at compiler-construction time over
all `x y : BitVec 64` using `BitVec.eq_of_toNat_eq`, `bv_omega`, and structural
bitvector lemmas (`BitVec.not_or`, `BitVec.and_assoc`, `BitVec.add_comm`,
`BitVec.add_assoc`). Unlike `bv_decide` (which invokes `Lean.ofReduceBool`),
`bv_omega` translates bitvector linear arithmetic into `Nat`/`Int` modular
arithmetic solved by Lean's kernel-proof-producing `omega` tactic.

In
[`support/track5_isle_egraph_dst_probe.lean`](support/track5_isle_egraph_dst_probe.lean)
(lines `59-324`), we prove:
- `bv64_mul_two_eq_shl_one`, `bv64_mul_four_eq_shl_two`,
  `bv64_mul_eight_eq_shl_three`, and `bv64_mul_two_eq_add_self`
  (strength reduction of multiplication to shifts and self-addition);
- `bv64_not_sub_one_eq_neg : ~~~(align - 1#64) = 0#64 - align`
  (equivalence of `rustc_codegen_ssa` and `rustc_codegen_cranelift` alignment
  masks);
- `bv64_and_not_and_not_eq_and_not_or : (x &&& ~~~y) &&& ~~~z = x &&& ~~~(y ||| z)`
  (RISC-V `Zbb` `andn` mask fusion); and
- `lowerISLE_sound : ∀ (env : RegEnv) (e : Expr), (lowerISLE e).eval env = e.eval env`
  ,
  verifying a total bottom-up instruction selector targeting `RV64GC` + `Zba`
  (`sh1add`, `sh2add`, `sh3add`) + `Zbb` (`andn`) + `AMode` (`amodeAddImm`).

#### 2.2 Architecture B: Proof-Producing E-Graph Rewrite Traces (`checkRewriteTrace_sound`)

When an acyclic e-graph (`aegraph`) or equality-saturation engine (`egg`)
applies sequences of algebraic rewrites, associativity/commutativity
reassociations, and target instruction fusions, the untrusted optimizer emits a
compact certificate `trace : List RewriteStep`, where each `RewriteStep` pairs a
subterm tree coordinate `pos : SubtermPos` with a rule identifier
`rule : RewriteRule`. Inside Lean
([`support/track5_isle_egraph_dst_probe.lean`](support/track5_isle_egraph_dst_probe.lean),
lines `370-576`), `checkRewriteTrace src trace dst` executes in
$O(|\text{trace}| \cdot \text{depth}(\text{src}))$ time via kernel reduction
(`rfl`), and `checkRewriteTrace_sound` lifts `rfl` into universal semantic
equality `src.eval env = dst.eval env` across all register environments `env`.
Theorem `dstSliceAddr_verified` (lines `573-576`) demonstrates this by verifying
the 4-step optimization of a dynamic DST slice element address
`((base + ((hdr + (align - 1)) &&& (0 - align))) + (idx * 4)) + 16` into fused
RISC-V `Zba`/`Zbb`/`AMode` form
`amodeAddImm (sh2add idx (base + andn (hdr + (align - 1)) (align - 1))) 16` by
`rfl`.

#### 2.3 Architecture C: CompCert `BTL`-Style Superblock Symbolic Execution and the `vtable_memflags()` Discovery

Expression-tree certificates (Architecture B) do not by themselves cover
DAG-level transformations across basic blocks or superblocks—such as common
subexpression elimination (CSE), instruction reordering, store-to-load
forwarding, and hoisting read-only vtable loads across stack stores.

**Primary-Source Discovery on `vtable_memflags()`
(`rustc_codegen_cranelift/src/vtable.rs:8-12`):**
Inspecting `compiler/rustc_codegen_cranelift/src/vtable.rs:8-12` (commit
`8006091eb71ae7d9e9bccb66c6122c9d68af4466`) alongside
`cranelift/codegen/src/inst_predicates.rs:46-54` and
`cranelift/codegen/src/ir/memflags.rs:109-126` (`bytecodealliance/wasmtime` at
`87282b8fd77fa9fbba6caadb0be690bedec2dc64`) revealed a subtle interaction:
- In `inst_predicates.rs:46-54`, `is_pure_for_egraph` classifies a
  `Load { flags, .. }` instruction as a pure e-graph node if and only if
  `flags.readonly() && flags.notrap() && flags.can_move()`.
- In `ir/memflags.rs:124-126`, `MemFlags::trusted()` sets only `notrap` and
  `aligned`, **not** `can_move`.
- In `rustc_codegen_cranelift/src/vtable.rs:8-12` (used by `drop_fn_of_obj`,
  `size_of_obj`, `align_of_obj`, `get_ptr_and_method_ref`, and secondary
  supertrait upcasting in `unsize.rs:55`), `vtable_memflags()` writes:
  ```rust
  pub(crate) fn vtable_memflags() -> MemFlags {
      let mut flags = MemFlags::trusted(); // A vtable access is always aligned
      and will never trap.
      flags.set_readonly(); // A vtable is always read-only.
      flags
  }
  ```
  Because `vtable_memflags()` omits `flags.set_can_move()`, Cranelift's
  `is_pure_for_egraph` returns `false` for all vtable loads! Setting
  `flags.set_can_move()` on immutable `.rodata` vtable loads—or validating
  superblocks with partitioned read-only memory in a `BTL` symbolic
  executor—enables vtable loads to be hoisted and CSE'd across stack stores.

In Section 4 of
[`support/track5_isle_egraph_dst_probe.lean`](support/track5_isle_egraph_dst_probe.lean)
(lines `591-812`) and Section 2.1 of
[`support/round2_track4_probe.lean`](support/round2_track4_probe.lean) (lines
`495-1084`), we mechanize both the register-only superblock validator
(`validateSuperblock_sound`) and the partitioned-memory superblock validator
(`validateSuperblockWithMem_sound`), which separates memory into two disjoint
partitions:

1. **Immutable `.rodata` / VTable Memory (`roMem : WordMem`):**
   Read via `MemExpr.loadRo (addr : MemExpr)`. Because `MemSBInstr.storeStack`
   mutates only `ConcreteMemState.stackMem`, `symExecWithMem` translates
   `.loadRo dst addr` into `MemExpr.loadRo ( normMemExpr (substMemExpr st.sregs
   addr) )` with zero dependence on `st.stackStores`. Two `.loadRo` instructions
   at `vptr + 16` separated by arbitrary `.storeStack` instructions therefore
   normalize to the **exact same `MemExpr`**, validating CSE and hoisting across
   stack stores by `rfl` (`vtableHoistAndCseAcrossStackStore_verified`, lines
   `1004-1015`).
2. **Mutable Stack Store Buffer (`stackStores : List (MemExpr × MemExpr)`):**
   Updated by `.storeStack addr val`, and queried by `.loadStack dst addr` via
   `symReadStack`, which performs verified store-to-load forwarding when the
   normalized store and load addresses match (`sAddr == lAddr`, verified in
   `stackStoreToLoadForwarding_verified`, lines `1033-1045`) and otherwise
   emits a `MemExpr.stackSelect` node that prevents unsound hoisting across
   potentially aliasing stack stores
   (`canary_hoist_stack_load_across_aliasing_store_rejected`, lines `1064-1083`
   ).

---

### 3. Bit-Accurate 64-Bit Checked Arithmetic, Division Edge Cases, and 128-Bit Multi-Word Lowering

`Basis: source + execution + derived`

#### 3.1 64-Bit `CheckedBinOp` Across RISC-V, AArch64, and x86-64

In `Runtime(PostCleanup)` MIR, `Rvalue::BinaryOp(BinOp::{AddWithOverflow,
SubWithOverflow, MulWithOverflow}, lhs, rhs)` returns `(T, bool)` with
`BackendRepr::ScalarPair`. Comparing
`compiler/rustc_codegen_cranelift/src/num.rs:203-310` (`rust-lang/rust` at
`8006091eb71ae7d9e9bccb66c6122c9d68af4466`) with
`cranelift/codegen/src/isa/{riscv64,aarch64,x64}/lower.isle`
(`bytecodealliance/wasmtime` at `87282b8fd77fa9fbba6caadb0be690bedec2dc64`)
shows how flagless RISC-V sequences correspond to condition-flag sequences on
AArch64 and x86-64:

| Operation (64-Bit) | RISC-V (`RV64GC`) Lowering (`riscv64/lower.isle:326`, `num.rs:219-297`) | AArch64 Lowering (`aarch64/lower.isle:3023-3220`) | x86-64 Lowering (`x64/lower.isle:174-225`) | Mathematical Overflow Predicate & Mechanized Theorem |
| :--- | :--- | :--- | :--- | :--- |
| **Unsigned `AddWithOverflow` (`u64`)** | `add sum, a, b` <br> `sltu ovf, sum, a` | `adds sum, a, b` <br> `cset ovf, hs` (`C == 1`) | `addq b, a` <br> `setb ovf` (`CF == 1`) | $a +_{\mathbb{N}} b \ge 2^{64} \iff (a \boxplus b) <_u a$ <br> (`riscv_uadd_overflow_iff_spec`) |
| **Signed `AddWithOverflow` (`i64`)** | `add sum, a, b` <br> `slti t0, b, 0` <br> `slt t1, sum, a` <br> `xor ovf, t0, t1` | `adds sum, a, b` <br> `cset ovf, vs` (`V == 1`) | `addq b, a` <br> `seto ovf` (`OF == 1`) | $(b <_s 0) \neq ((a \boxplus b) <_s a)$ |
| **Unsigned `SubWithOverflow` (`u64`)** | `sub diff, a, b` <br> `sltu ovf, a, diff` (`num.rs:235`) *or* `sltu ovf, a, b` | `subs diff, a, b` <br> `cset ovf, lo` (`C == 0`) | `subq b, a` <br> `setb ovf` (`CF == 1`) | $a <_{\mathbb{N}} b \iff a <_u (a \boxminus b)$ <br> (`cg_clif_usub_overflow_iff_spec`) |
| **Signed `SubWithOverflow` (`i64`)** | `sub diff, a, b` <br> `slti t0, b, 0` <br> `slt t1, a, diff` <br> `xor ovf, t0, t1` | `subs diff, a, b` <br> `cset ovf, vs` (`V == 1`) | `subq b, a` <br> `seto ovf` (`OF == 1`) | $(b <_s 0) \neq (a <_s (a \boxminus b))$ |
| **Unsigned `MulWithOverflow` (`u64`)** | `mul lo, a, b` <br> `mulhu hi, a, b` <br> `snez ovf, hi` | `mul lo, a, b` <br> `umulh hi, a, b` <br> `cmp hi, 0; cset ovf, ne` | `mulq b` (`RDX:RAX`) <br> `seto ovf` (`CF/OF == 1`) | $\lfloor (a \cdot_{\mathbb{N}} b) / 2^{64} \rfloor \neq 0$ |
| **Signed `MulWithOverflow` (`i64`)** | `mulh hi, a, b` <br> `mul lo, a, b` <br> `srai sgn, lo, 63` <br> `xor t, hi, sgn` <br> `snez ovf, t` | `mul lo, a, b` <br> `smulh hi, a, b` <br> `cmp hi, lo, asr #63` <br> `cset ovf, ne` | `imulq b` (`RDX:RAX`) <br> `seto ovf` (`CF/OF == 1`) | $\lfloor (a \cdot_{\mathbb{Z}} b) / 2^{64} \rfloor \neq ((a \boxdot b) \gg_s 63)$ <br> (`riscv_smul_overflow_bv_iff_spec`, `riscv_smul_xor_snez_iff_spec`) |

**Why Euclidean Division in `omega` Solves Signed 64-Bit `MulWithOverflow`
Without `bv_decide` :**
Bit-blasting a 64×64$\to$128 multiplier produces a non-linear AIG circuit that
neither `bv_omega` nor kernel reduction can decide directly. However, once the
128-bit signed product is named as a single integer variable
$P = \text{toInt}(a) \cdot \text{toInt}(b) \in [-2^{127}, 2^{127} - 1]$, its
upper and lower 64-bit words are linear Euclidean division/modulo terms with
respect to the concrete positive divisor $2^{64} > 0$:
$$q = \lfloor P / 2^{64} \rfloor = \texttt{P / (2 \textasciicircum 64 : Int)}, \qquad r = P \bmod 2^{64} = \texttt{P \% (2 \textasciicircum 64 : Int)} \in [0, 2^{64} - 1]$$
with $P = 2^{64} q + r$ and $\text{sgn} = \text{if } r \ge 2^{63} \text{ then }
-1 \text{ else } 0$. Lean 4's `omega` tactic discharges
`riscv_smul_overflow_iff_spec`, `riscv_smul_overflow_bv_iff_spec`, and
`riscv_smul_xor_snez_iff_spec` in a single step
([`support/round2_track4_probe.lean`](support/round2_track4_probe.lean), lines
`102-149`).

**Division and Remainder Edge Cases (`MIN / -1` and `/ 0`):**
In `Runtime(PostCleanup)` MIR, safe integer division and remainder emit explicit
`TerminatorKind::Assert` guards (`divisor != 0` and, for signed types,
`!(lhs == INT_MIN && rhs == -1)`) prior to `BinOp::Div` / `BinOp::Rem`. On
RISC-V (`RV64M`), hardware `div`/`divu`/`rem`/`remu` never trap (returning `-1`
on `/ 0` and `INT_MIN` on `INT_MIN / -1`), whereas Cranelift's `udiv`/`sdiv`
IR instructions carry explicit trap semantics (`opcode.can_trap() == true` in
`inst_predicates.rs:64-69`, modeled by `SBInstr.assertNonZero` and
`LoopInstr.udiv` in our probes).

#### 3.2 128-Bit (`u128` / `i128`) Multi-Word Lowering and `compiler-builtins` `UMulo::mulo`

Inspecting `compiler/rustc_codegen_cranelift/src/codegen_i128.rs:1-83`
(`rust-lang/rust` at `8006091eb71ae7d9e9bccb66c6122c9d68af4466`),
`cranelift/codegen/src/isa/{riscv64,aarch64,x64}/lower.isle`
(`bytecodealliance/wasmtime` at `87282b8fd77fa9fbba6caadb0be690bedec2dc64`),
and `compiler-builtins/src/int/mul.rs:33-98, 194-204`
(`rust-lang/compiler-builtins` at `351d48e4b95f1665cfd3360e3ba8f3dd4d3fb3c1`)
establishes how 128-bit operations lower to 64-bit register pairs
`U128Pair (lo hi : BitVec 64)` with valuation
$\text{toNat}(x) = x_{\text{lo}} + x_{\text{hi}} \cdot 2^{64}$:

1. **128-Bit Addition and Carry-Chaining (`riscv64/lower.isle:106-114, 340-353`,
   `u128_add_pair_correct` in `round2_track4_probe.lean:243-280`):**
   Computes `sumLo = x.lo + y.lo`, `carryBool = BitVec.ult sumLo x.lo`,
   `sumHiWithCarry = (x.hi + y.hi) + carry`, and
   `overflow = BitVec.ult sumHiWithCarry x.hi || (carryBool && (sumHiWithCarry == x.hi))`
   ,
   producing the exact modular sum `(x.toNat + y.toNat) % 2^128` and 129-bit
   carry `decide (x.toNat + y.toNat ≥ 2^128)`.
2. **128-Bit Subtraction and Borrow-Chaining (`riscv64/inst.isle:2848-2860`,
   `u128_sub_pair_correct` in `round2_track4_probe.lean:338-376`):**
   Computes `diffLo = x.lo - y.lo`, `borrowBool = BitVec.ult x.lo diffLo`,
   `diffHi = (x.hi - y.hi) - borrow`, and
   `underflow = BitVec.ult x.hi y.hi || ((x.hi == y.hi) && borrowBool)`,
   producing `(2^128 - y.toNat + x.toNat) % 2^128` and borrow
   `decide (x.toNat < y.toNat)`.
3. **128-Bit Wrapping Multiplication (`riscv64/lower.isle:498-522`,
   `aarch64/lower.isle:797-822`, `x64/lower.isle:1090-1119`,
   `u128_mul_pair_algebraic_identity` in `round2_track4_probe.lean:408-421`):**
   By bilinear radix expansion (`radix_mul_expand`) and
   `(Nat.pow_add 2 64 64).symm` ($2^{64} \cdot 2^{64} = 2^{128}$), the high-word
   product $x_{\text{hi}} y_{\text{hi}} \cdot 2^{128}$ vanishes modulo $2^{128}$
   ,
   reducing the 128-bit product to `dstLo = (xLo * yLo) % 2^64` (`mul`) and
   `dstHi = ((xLo * yLo) / 2^64 + xLo * yHi + xHi * yLo) % 2^64` (`mulhu` + two
   `mul`/`add` cross-terms).
4. **128-Bit Checked Multiplication (`codegen_i128.rs:51-83`,
   `compiler-builtins/src/int/mul.rs:33-54`, `compiler_builtins_umulo_*` in
   `round2_track4_probe.lean:433-460`):**
   Delegates to `__rust_u128_mulo` / `__rust_i128_mulo` (`UMulo::mulo`), which
   branches on `(xHi == 0, yHi == 0)`:
   - `(false, false)` :
     $x_{\text{hi}} > 0 \wedge y_{\text{hi}} > 0 \implies x \cdot y \ge 2^{128}$
     (`compiler_builtins_umulo_both_hi_nonzero_overflows`);
   - `(true, true)` :
     $x_{\text{hi}} = 0 \wedge y_{\text{hi}} = 0 \implies x_{\text{lo}} \cdot y_{\text{lo}} < 2^{128}$
     (`compiler_builtins_umulo_both_hi_zero_no_overflow`); and
   - `(true, false)` (and symmetrically `(false, true)`):
     $x_{\text{lo}} (y_{\text{lo}} + y_{\text{hi}} 2^{64}) \ge 2^{128} \iff x_{\text{lo}} y_{\text{lo}} + ((x_{\text{lo}} y_{\text{hi}}) \bmod 2^{64}) 2^{64} \ge 2^{128} \vee \lfloor (x_{\text{lo}} y_{\text{hi}}) / 2^{64} \rfloor > 0$
     (`compiler_builtins_umulo_lhs_hi_zero_iff`).

---

### 4. Dynamic DST (`[T]`, `str`, `dyn Trait`) Tail Offset Computation and the `ty::Foreign` Bug

`Basis: source + execution + derived`

#### 4.1 Field Projection (`PlaceElem::Field`) and `size_and_align_of_dst`

Inspecting `compiler/rustc_codegen_ssa/src/mir/place.rs:175-336, 431-450` and
`compiler/rustc_codegen_cranelift/src/{value_and_place.rs:11-56, unsize.rs:222-291}`
at commit `8006091eb71ae7d9e9bccb66c6122c9d68af4466` establishes how `rustc`
lowers field projection and runtime extent calculation on custom DSTs such as
`struct Packet<T: ?Sized> { header: u32, payload: T }`:

1. **Statically Aligned Tail (`field.is_sized()` or `field.ty` is `[U]` / `str`
  /
   `Foreign`):**
   Because `[U]` has the compile-time alignment of `U` and `str` has alignment
   `1`, `layout.fields.offset(i)` already equals the exact runtime byte offset.
   The backend computes `base_ptr + field_offset.bytes()` and forwards the wide
   pointer's metadata (`len` or `vptr`) unchanged.
2. **Dynamically Aligned Tail (`field.ty` is `dyn Trait` or a nested unsized
   `Adt` /`Tuple` with `unaligned_offset = layout.fields.offset(i).bytes() > 0`
   ):**
   The runtime alignment `unsized_align` of `payload: dyn Trait` is loaded from
   **vtable slot 2** (`COMMON_VTABLE_ENTRIES_ALIGN`, byte offset `2 * ptr_size =
   16` on 64-bit targets; `rustc_codegen_cranelift/src/vtable.rs:27-33`), capped
   at `min(unsized_align, P)` if the struct is `#[repr(packed(P))]`
   (`place.rs:249-252`, `value_and_place.rs:37-43`), and used to align
   `unaligned_offset` upward:
   - `rustc_codegen_ssa` (`place.rs:442-449`) emits
     `(unaligned_offset + (unsized_align - 1)) & !(unsized_align - 1)`;
   - `rustc_codegen_cranelift` (`value_and_place.rs:46-52`) emits
     `(unaligned_offset + (unsized_align - 1)) & (0 - unsized_align)`.
   Theorem `alignToBV_eq_cg_clif_formula`
   ([`support/track5_isle_egraph_dst_probe.lean`](support/track5_isle_egraph_dst_probe.lean),
   lines `907-911`) proves that both formulas are bit-for-bit identical for all
   64-bit bitvectors and lower to a single RISC-V `Zbb` `andn` instruction.
3. **Single-Rounding Total Size Identity in `size_and_align_of_dst`
   (`unsize.rs:264-272`, `place.rs:321-334`):**
   Because the dynamic tail size `unsized_size` is guaranteed to be a multiple
   of
   `unsized_align` (`unsized_size = k * align`), the two-stage specification
   $$\text{alignTo}\big(\text{alignTo}(\text{unaligned\_offset}, \text{align}) + \text{unsized\_size},\; \text{align}\big)$$
   simplifies to a **single** alignment rounding:
   $$\text{alignTo}(\text{unaligned\_offset} + \text{unsized\_size},\; \text{align})$$
   We prove this identity in `alignToNat_add_mul`, `alignToNat_idem`, and
   `rustc_dst_total_size_optimization`
   ([`support/track5_isle_egraph_dst_probe.lean`](support/track5_isle_egraph_dst_probe.lean),
   lines `936-979`).
4. **Negative Canary (`static_header_align_miscomputes_dst_tail_offset`, lines
   `1030-1043`):**
   For `Packet<dyn Trait>` with `header: u32` (`unalignedOffset = 4`,
   `staticHeaderAlign = 4`) backed by a `u64` payload (`vtable.align = 8` at
   `vptr = 0x2000`), using `staticHeaderAlign` instead of `vtable.align`
   computes offset `4` instead of `8`, producing an unaligned address `0x1004`
   (`(0x1000 + 4) % 8 = 4 ≠ 0`).
5. **Latent `ty::Foreign` Panic in `rustc_codegen_cranelift`:**
   Comparing `compiler/rustc_codegen_ssa/src/mir/place.rs:193` with
   `compiler/rustc_codegen_cranelift/src/value_and_place.rs:28-30` uncovered a
   bug in `rustc_codegen_cranelift`: `rustc_codegen_ssa` matches
   `ty::Slice(..) | ty::Str | ty::Foreign(..)` in its `simple` statically
   aligned branch, whereas `rustc_codegen_cranelift` matches only
   `ty::Slice(..) | ty::Str`, causing `ty::Foreign(..)` tail fields to fall
   through to `size_and_align_of` (`unsize.rs:289`), which panics with
   `unreachable!()`.

---

### 5. Rust 1.86+ `VtblEntry::TraitVPtr` Trait Upcasting and `GlobalRelocTable`

`Basis: source + execution + derived`

#### 5.1 VTable Segment Linearization and `unsized_info` Lowering

Inspecting `compiler/rustc_middle/src/ty/vtable.rs:12-156`,
`compiler/rustc_trait_selection/src/traits/vtable.rs:17-187, 374-450`, and
`compiler/rustc_codegen_cranelift/src/unsize.rs:20-162` at commit
`8006091eb71ae7d9e9bccb66c6122c9d68af4466` reveals how `rustc` constructs
vtables and lowers `CastKind::PointerCoercion(PointerCoercion::Unsize)`:

1. **Fixed 3-Word Header and Primary Supertrait Prefix
  (`prepare_vtable_segments`,
   `rustc_trait_selection/src/traits/vtable.rs:60-187`):**
   Every vtable with a principal trait begins with the 3-word prefix
   `COMMON_VTABLE_ENTRIES = [MetadataDropInPlace, MetadataSize, MetadataAlign]`
   (slots `0, 1, 2`, byte offsets `0, 8, 16`). The **first** direct supertrait
   chain forms a contiguous prefix of the vtable (`emit_vptr_on_upcast =
   false`),
   so upcasting `&dyn SubTrait` to its primary supertrait `&dyn SuperA`
   (`tcx.supertrait_vtable_slot((source, target)) == None`) reuses the existing
   vtable pointer with **zero machine instructions**!
2. **Secondary Supertrait Sub-VTable Pointers (`VtblEntry::TraitVPtr`):**
   For the second and subsequent supertraits in `trait Sub: SuperA + SuperB` (or
   secondary diamond branches), `emit_vptr_on_upcast = true` appends a
   `VtblEntry::TraitVPtr(super_trait_ref)` entry at slot `entry_idx`
   (`tcx.supertrait_vtable_slot == Some(entry_idx)`), containing the address of
   a
   separately allocated read-only sub-vtable `tcx.vtable_allocation((ty,
   Some(super_trait_ref)))`. Upcasting loads the pointer at
   `old_vptr + entry_idx * 8` (`coerceDynUpcast_loads_traitVPtr` in
   [`support/track5_isle_egraph_dst_probe.lean`](support/track5_isle_egraph_dst_probe.lean)
   ,
   lines `883-894`).

```
   WidePtr (&dyn SubTrait)                   SubTrait VTable (at `vptr`)
  ┌──────────────┬──────────────┐           ┌──────────────────────────────────┐
  │ data_ptr     │ metadata:    │──────────►│ Slot 0: MetadataDropInPlace      │
  │ (0x1000)     │ vptr (0x2000)│           │ Slot 1: MetadataSize (8)         │
  └──────────────┴──────────────┘           │ Slot 2: MetadataAlign (8)        │
                                            │ Slot 3: Method(SuperA::foo)      │ ◄── Primary prefix:
                                            │ Slot 4: Method(SubTrait::bar)    │     `&dyn SuperA` reuses
                                            │ Slot 5: TraitVPtr(0x3000) ───────┼──┐  `0x2000` (slot = None)
                                            └──────────────────────────────────┘  │
                                                                                  ▼
                                             Secondary SuperB Sub-VTable (`0x3000`)
                                            ┌──────────────────────────────────┐
                                            │ Slot 0: MetadataDropInPlace      │ ◄── `&dyn SuperB` loads
                                            │ Slot 1: MetadataSize (8)         │     slot 5 (`vptr + 40`)
                                            │ Slot 2: MetadataAlign (8)        │     (slot = Some(5))
                                            │ Slot 3: Method(SuperB::baz)      │
                                            └──────────────────────────────────┘
```

#### 5.2 Discharging `vtableStoredAt` via `GlobalRelocTable`

In Section 2.2 of
[`support/round2_track4_probe.lean`](support/round2_track4_probe.lean) (lines
`1097-1203`), we model pre-linking symbolic vtable entries (`RelocVtblEntry`,
referencing function symbol IDs `fnSymId` and secondary supertrait vtable
allocation IDs `subVtableAllocId`) together with a module-level
`GlobalRelocTable`:

- **`relocTable_discharges_vtableStoredAt` (lines `1165-1182`):** Under the
  module initialization invariant `roMemInitializedFromRelocTable tbl roMem`,
  every vtable allocation `allocId` automatically satisfies
  `vtableStoredAt roMem (tbl.vtableAllocAddr allocId) (tbl.resolveVtable allocId)`
  .
- **`relocTable_chained_traitVPtr_stored` (lines `1187-1203`):** When a subtrait
  vtable `subAllocId` contains `RelocVtblEntry.traitVPtr superAllocId` at
  `entryIdx`, loading slot `entryIdx` from `roMem` yields
  `tbl.vtableAllocAddr superAllocId` and simultaneously discharges
  `vtableStoredAt` for the target supertrait vtable.

---

### 6. Complete Theorem Inventories

`Basis: execution`

#### 6.1 `support/track5_isle_egraph_dst_probe.lean` (1,089 Lines)

SHA-256: `bfedaab9b0c00406ada5614c165ebc401d01c5e197597c8ed2ef0842d9cabf19`.
Verified with `lean -j1 -M1024` (exit code `0`, zero `sorryAx`, zero
`Lean.ofReduceBool`):

| Section | Theorem Name | Lines | Formal Statement Summary | Axiom Footprint (`#print axioms`) |
| :--- | :--- | :--- | :--- | :--- |
| 1 | `bv64_mul_two_eq_shl_one` | 59–63 | `∀ x : BitVec 64, x * 2#64 = x <<< 1#64` | `[propext, Classical.choice, Quot.sound]` |
| 1 | `bv64_mul_four_eq_shl_two` | 67–71 | `∀ x : BitVec 64, x * 4#64 = x <<< 2#64` | `[propext, Classical.choice, Quot.sound]` |
| 1 | `bv64_mul_eight_eq_shl_three` | 73–77 | `∀ x : BitVec 64, x * 8#64 = x <<< 3#64` | `[propext, Classical.choice, Quot.sound]` |
| 1 | `bv64_mul_two_eq_add_self` | 81–85 | `∀ x : BitVec 64, x * 2#64 = x + x` | `[propext, Classical.choice, Quot.sound]` |
| 1 | `bv64_not_sub_one_eq_neg` | 89–91 | `∀ align : BitVec 64, ~~~(align - 1#64) = 0#64 - align` | `[propext, Classical.choice, Quot.sound]` |
| 1 | `bv64_and_not_and_not_eq_and_not_or` | 95–97 | `(x &&& ~~~y) &&& ~~~z = x &&& ~~~(y \|\|\| z)` | `[propext]` |
| 1 | `riscv_uadd_overflow_iff_spec` | 117–133 | `(riscvUaddOverflow a b).2 = uaddOverflowSpec a b` (`(a + b) <ᵤ a`) | `[propext, Classical.choice, Quot.sound]` |
| 1 | `cg_clif_usub_overflow_iff_spec` | 145–166 | `BitVec.ult a (a - b) = usubOverflowSpec a b` (`a <ᵤ (a - b)`) | `[propext, Classical.choice, Quot.sound]` |
| 2 | `lowerAddRule_sound` | 240–243 | Soundness of `Zba` `sh1add`/`sh2add`/`sh3add` and `amodeAddImm` selection | `[propext, Quot.sound]` |
| 2 | `lowerAndRule_sound` | 256–263 | Soundness of `Zbb` `andn` and negative alignment-mask selection | `[propext, Classical.choice, Quot.sound]` |
| 2 | `lowerMulRule_sound` | 274–281 | Soundness of power-of-two multiplication strength reduction | `[propext, Classical.choice, Quot.sound]` |
| 2 | `lowerISLE_sound` | 303–323 | `∀ env e, (lowerISLE e).eval env = e.eval env` | `[propext, Classical.choice, Quot.sound]` |
| 2 | `aegraph_unsubsumed_union_violates_dominance` | 348–357 | Formal model of Cranelift `opts/README.md` Rule 2 (`subsume` dominance) | `[propext, Quot.sound]` |
| 3 | `applyRuleRoot_sound` | 404–421 | Root-level soundness of all 11 `RewriteRule` constructors | `[propext, Classical.choice, Quot.sound]` |
| 3 | `applyAtPos_sound` | 469–492 | Congruence soundness of `applyAtPos` over `SubtermPos` | `[propext, Classical.choice, Quot.sound]` |
| 3 | `runRewriteTrace_sound` | 510–526 | Multi-step soundness of `runRewriteTrace` | `[propext, Classical.choice, Quot.sound]` |
| 3 | `checkRewriteTrace_sound` | 531–541 | `checkRewriteTrace src trace dst = true → src.eval env = dst.eval env` | `[propext, Classical.choice, Quot.sound]` |
| 3 | `dstSliceAddr_verified` | 573–576 | `rfl`-checked e-graph trace optimizing DST slice element address | `[propext, Classical.choice, Quot.sound]` |
| 4 | `normExpr_sound` | 622–659 | `∀ env e, (normExpr e).eval env = e.eval env` | `[propext, Classical.choice, Quot.sound]` |
| 4 | `substExpr_eval` | 679–682 | Substitution homomorphism `(substExpr sregs e).eval initEnv` | `[propext]` |
| 4 | `symExecSuperblock_correct` | 731–765 | Exact simulation between `symExecSuperblock` and `execSuperblock` | `[propext, Classical.choice, Quot.sound]` |
| 4 | `validateSuperblock_sound` | 781–812 | Soundness of `BTL`-style superblock validator over register & guard states | `[propext, Classical.choice, Quot.sound]` |
| 5 | `coerceDynUpcast_loads_traitVPtr` | 883–894 | Secondary supertrait upcast loads `TraitVPtr` from `vptr + entryIdx * 8` | `[propext]` |
| 5 | `alignToBV_eq_cg_clif_formula` | 907–911 | Equivalence of `rustc_codegen_ssa` and `rustc_codegen_cranelift` alignment masks | `[propext, Classical.choice, Quot.sound]` |
| 5 | `alignToNat_add_mul` | 936–946 | `alignToNat offset align + k * align = alignToNat (offset + k * align) align` | `[propext, Quot.sound]` |
| 5 | `alignToNat_idem` | 950–961 | Idempotence `alignToNat (alignToNat x align) align = alignToNat x align` | `[propext, Quot.sound]` |
| 5 | `rustc_dst_total_size_optimization` | 972–979 | Single-rounding identity for `size_and_align_of_dst` | `[propext, Quot.sound]` |
| 5.1 | `static_header_align_miscomputes_dst_tail_offset` | 1030–1043 | Negative canary: static header alignment misaligns `Packet<dyn Trait>` tail | `[propext, Quot.sound]` |

#### 6.2 `support/round2_track4_probe.lean` (1,742 Lines)

SHA-256: `73f05a1e0b80bae34a1d1f17e75283c1a2c6fd6bdd83ed75f7ffa193f7451462`.
Verified with `lean -j1 -M1024` (exit code `0`, zero `sorryAx`, zero
`Lean.ofReduceBool`):

| Section | Theorem Name | Lines | Formal Statement Summary | Axiom Footprint (`#print axioms`) |
| :--- | :--- | :--- | :--- | :--- |
| 1.1 | `riscv_smul_overflow_iff_spec` | 102–109 | Universal `Int` proof that `(P / 2^64 ≠ sgn) ↔ (P < -2^63 ∨ P ≥ 2^63)` | `[propext, Classical.choice, Quot.sound]` |
| 1.1 | `riscv_smul_overflow_bv_iff_spec` | 130–134 | Universal `BitVec 64` proof of signed `MulWithOverflow` (`mulh` + `mul` + `srai 63`) | `[propext, Classical.choice, Quot.sound]` |
| 1.1 | `riscv_smul_xor_snez_iff_spec` | 141–149 | 64-bit modular `xor` + `snez` equivalence (`hi % 2^64 ≠ sgn % 2^64`) for $P \in [-2^{127}, 2^{127}-1]$ | `[propext, Classical.choice, Quot.sound]` |
| 1.2 | `U128Pair.toNat_lt` | 177–181 | `∀ x : U128Pair, x.toNat < 2 ^ 128` | `[propext, Quot.sound]` |
| 1.2 | `bv64_add_toNat_carry` | 200–214 | Exact `toNat` carry characterization of 64-bit addition | `[propext, Classical.choice, Quot.sound]` |
| 1.2 | `bv64_ult_add_iff` | 218–224 | `BitVec.ult (a + b) a = true ↔ a.toNat + b.toNat ≥ 2 ^ 64` | `[propext, Classical.choice, Quot.sound]` |
| 1.2 | `u128_add_pair_correct` | 243–280 | Universal proof of RISC-V 128-bit `uadd_overflow` carry-chaining (`riscv64/lower.isle:340-353`) | `[propext, Classical.choice, Quot.sound]` |
| 1.2 | `bv64_sub_toNat_borrow` | 283–301 | Exact `toNat` borrow characterization of 64-bit subtraction | `[propext, Classical.choice, Quot.sound]` |
| 1.2 | `bv64_ult_sub_iff` | 304–310 | `BitVec.ult a (a - b) = true ↔ a.toNat < b.toNat` | `[propext, Classical.choice, Quot.sound]` |
| 1.2 | `u128_sub_pair_correct` | 338–376 | Universal proof of RISC-V 128-bit `sub_i128` borrow-chaining (`riscv64/inst.isle:2848-2860`) | `[propext, Classical.choice, Quot.sound]` |
| 1.2 | `radix_mul_expand` | 379–398 | Bilinear expansion for two-word radix-$B$ integers | `[propext, Quot.sound]` |
| 1.2 | `u128_mul_pair_algebraic_identity` | 408–421 | Universal proof of 128-bit wrapping multiplication cross-term reduction | `[propext, Quot.sound]` |
| 1.2 | `compiler_builtins_umulo_both_hi_nonzero_overflows` | 433–441 | `UMulo::mulo` (`mul.rs:39`): `xHi > 0 ∧ yHi > 0 → x * y ≥ 2^128` | `[propext, Quot.sound]` |
| 1.2 | `compiler_builtins_umulo_both_hi_zero_no_overflow` | 443–448 | `UMulo::mulo` (`mul.rs:41`): `xHi = 0 ∧ yHi = 0 → xLo * yLo < 2^128` | `[propext, Quot.sound]` |
| 1.2 | `compiler_builtins_umulo_lhs_hi_zero_iff` | 450–460 | `UMulo::mulo` (`mul.rs:42-53`): exact overflow condition when one high word is zero | `[propext, Classical.choice, Quot.sound]` |
| 2.1 | `normMemExpr_sound` | 625–672 | Universal soundness of `normMemExpr` over `(env, roMem, initStack)` | `[propext, Classical.choice, Quot.sound]` |
| 2.1 | `substMemExpr_eval` | 700–705 | Substitution homomorphism for `MemExpr` | `[propext]` |
| 2.1 | `symReadStack_eval` | 789–811 | Soundness of symbolic store-to-load forwarding and `.stackSelect` | `[propext, Classical.choice, Quot.sound]` |
| 2.1 | `symExecWithMem_correct` | 857–920 | Simulation theorem for `symExecWithMem` over partitioned `.rodata` and stack memory | `[propext, Classical.choice, Quot.sound]` |
| 2.1 | `validateSuperblockWithMem_sound` | 938–977 | Universal soundness of `BTL` superblock validator with partitioned `roMem` and `stackStores` | `[propext, Classical.choice, Quot.sound]` |
| 2.1 | `vtableHoistAndCseAcrossStackStore_verified` | 1004–1015 | Verified CSE/hoisting of vtable `loadRo (vptr + 16)` across `storeStack` + `Zbb` `andn` | `[propext, Classical.choice, Quot.sound]` |
| 2.1 | `stackStoreToLoadForwarding_verified` | 1033–1045 | Verified store-to-load forwarding on stack memory across intervening `loadRo` | `[propext, Classical.choice, Quot.sound]` |
| 2.1 | `canary_hoist_stack_load_across_aliasing_store_rejected` | 1064–1083 | Negative canary: `validateSuperblockWithMem` rejects hoisting `loadStack` across aliasing `storeStack` | `[propext, Quot.sound]` |
| 2.2 | `relocTable_discharges_vtableStoredAt` | 1165–1182 | `GlobalRelocTable` module initialization automatically discharges `vtableStoredAt` | `[propext]` |
| 2.2 | `relocTable_chained_traitVPtr_stored` | 1187–1203 | Chained secondary supertrait `TraitVPtr` load yields relocated super-vtable satisfying `vtableStoredAt` | `[propext]` |
| 3.1 | `argHoistLevel_not_in_loop` | 1314–1332 | Soundness of `argHoistLevel` (`elaborate.rs:569-575`): target loop does not contain `argDefBlock` | `[propext]` |
| 3.2 | `MemExpr.eval_eq_of_vars_eq` | 1354–1388 | Register-environment frame agreement on `e.vars` preserves `e.eval` | `[propext]` |
| 3.2 | `execLoopBody_preserves_invariant` | 1478–1491 | `bodyPreservesRegs` preserves loop-invariant operands and hoisted destination register | `[propext, Classical.choice, Quot.sound]` |
| 3.2 | `assign_idempotent_when_already_equal` | 1497–1507 | Re-assigning an already-equal loop-invariant value is an identity state transition | `[propext, Classical.choice, Quot.sound]` |
| 3.2 | `loop_hoist_iterations_equiv` | 1514–1542 | Inductive equivalence of unhoisted and preheader-hoisted loop bodies across `k` iterations | `[propext, Classical.choice, Quot.sound]` |
| 3.2 | `pure_loop_hoist_sound` | 1551–1616 | Positive theorem: hoisting loop-invariant pure instruction into preheader is sound for all $k \ge 0$ | `[propext, Quot.sound]` |
| 3.2 | `canary_hoist_trapping_div_above_zero_iteration_loop_unsound` | 1642–1657 | Negative canary: hoisting trapping `udiv` above $k = 0$ loop introduces spurious trap when `denom = 0` | `[propext, Quot.sound]` |

## Boundaries

- **Known Not to Apply (`bv_decide` / `Lean.ofReduceBool` Inside Audited
  Proofs):**
  Invoking `bv_decide` or `native_decide` introduces `Lean.ofReduceBool` into
  the theorem's kernel axiom footprint, which is **known not to apply** under
  `trusted/audit/TrustedBoundary.lean` and `trusted/lean/foundation-lock.json`.
  All bitvector and integer obligations in this package are proved via
  `BitVec.eq_of_toNat_eq`, `bv_omega`, `omega`, and kernel reduction (`rfl` /
  `decide`).
- **Known Not to Apply (Unsubsumed Dependency-Erasing E-Graph Unions and
  Hoisting Trapping Instructions Above Zero-Trip Loops):**
  - Unioning a dependency-erasing rewrite such as `(band x 0) => 0` into an
    acyclic e-graph without `(subsume ...)` is **known not to apply** because
    GVN can share the constant e-class with a dominating block where `x` is out
    of SSA scope (`aegraph_unsubsumed_union_violates_dominance`).
  - Hoisting a potentially trapping instruction (`opcode.can_trap()`, such as
    hardware/IR division or a load without `notrap`) into a loop preheader
    (`hoist_block = idom`) via `loop_hoist_level` is **known not to apply**
    because `hoist_block` executes even when the loop runs zero iterations
    (`canary_hoist_trapping_div_above_zero_iteration_loop_unsound`).
- **Unsupported in `rustc_codegen_cranelift` (`ty::Foreign` DST Tail Fields and
  `vtable_memflags()` `can_move`):**
  - At `rust-lang/rust` commit `8006091eb71ae7d9e9bccb66c6122c9d68af4466`,
    `compiler/rustc_codegen_cranelift/src/value_and_place.rs:28-30` omits
    `ty::Foreign(..)` from its statically aligned field-projection fast path
    (unlike `compiler/rustc_codegen_ssa/src/mir/place.rs:193`), causing
    `size_and_align_of` (`unsize.rs:289`) to panic on `ty::Foreign` DST tails.
  - At the same revision, `compiler/rustc_codegen_cranelift/src/vtable.rs:8-12`
    sets `MemFlags::trusted()` and `set_readonly()` without calling
    `set_can_move()`, preventing Cranelift's `is_pure_for_egraph`
    (`inst_predicates.rs:46-54`) from hoisting or deduplicating vtable loads
    inside
    the acyclic e-graph pass.
- **Not Examined (128-Bit Division Libcall Bodies):**
  While 128-bit addition, subtraction, wrapping multiplication, and
  `compiler-builtins` checked multiplication (`UMulo::mulo`) are mechanized in
  [`support/round2_track4_probe.lean`](support/round2_track4_probe.lean), the
  iterative bit-shift division loop inside `__udivti3` / `__divti3` is **not
  examined** in this package.

## Evidence

1. **Preserved Lean `v4.34.1` Mechanization Probes:**
   - [`support/track5_isle_egraph_dst_probe.lean`](support/track5_isle_egraph_dst_probe.lean)
     (1,089 lines, SHA-256
     `bfedaab9b0c00406ada5614c165ebc401d01c5e197597c8ed2ef0842d9cabf19`).
   - [`support/round2_track4_probe.lean`](support/round2_track4_probe.lean)
     (1,742 lines, SHA-256
     `73f05a1e0b80bae34a1d1f17e75283c1a2c6fd6bdd83ed75f7ffa193f7451462`).
   - Both files were verified under `leanprover/lean4` `v4.34.1` (commit
     `5045d0056413266e57c625dcd7c365b10e377c52`) with `lean -j1 -M1024`,
     exiting with status `0` and passing all 27 `#guard_msgs in #print axioms`
     assertions.
2. **Cranelift ISLE and Acyclic E-Graph Sources (`bytecodealliance/wasmtime` at
   `87282b8fd77fa9fbba6caadb0be690bedec2dc64`, version `0.132.0`):**
   - `cranelift/isle/isle/src/ast.rs:16-20, 88-377` and
     `cranelift/isle/isle/src/trie_again.rs:10-388` (ISLE AST, VeriISLE/Crocus
     `Def::Spec` / `SpecOp`, and hash-consed decision automaton).
   - `cranelift/codegen/src/egraph/mod.rs:238-385, 756-909`,
     `cranelift/codegen/src/egraph/cost.rs:1-178`, and
     `cranelift/codegen/src/egraph/elaborate.rs:102-114, 171-220, 285-628, 722-725, 819-858`
     (`ValueDef::Union`, `ScopedHashMap` GVN, `subsume`, `LoopStackEntry`, and
     `loop_hoist_level`).
   - `cranelift/codegen/src/inst_predicates.rs:46-78` and
     `cranelift/codegen/src/ir/memflags.rs:109-126` (`is_pure_for_egraph` and
     `MemFlags::trusted()`).
   - `cranelift/codegen/src/opts/README.md:1-125`,
     `cranelift/codegen/src/opts.rs:53-155`, and
     `cranelift/codegen/src/opts/{arithmetic.isle,bitops.isle,shifts.isle}`.
   - `cranelift/codegen/src/isa/riscv64/lower.isle:50-115, 323-354, 498-576, 720-768, 2180-2266`
     and
     `cranelift/codegen/src/isa/riscv64/inst.isle:520-535, 1621-1628, 2427-2463, 2848-2860`
     .
   - `cranelift/codegen/src/isa/aarch64/lower.isle:82-127, 797-822, 3023-3220`
     and `cranelift/codegen/src/isa/aarch64/inst.isle:3898-3990`.
   - `cranelift/codegen/src/isa/x64/lower.isle:117-225, 650-800, 1090-1119` and
     `cranelift/codegen/src/isa/x64/inst.isle:550-609`.
3. **Rust Compiler and `compiler-builtins` Sources (`rust-lang/rust` at
   `58cf8f9c35b355199727627d07ae34a4e2846d67` and
   `8006091eb71ae7d9e9bccb66c6122c9d68af4466`; `rust-lang/compiler-builtins` at
   `351d48e4b95f1665cfd3360e3ba8f3dd4d3fb3c1`):**
   - `compiler/rustc_middle/src/ty/vtable.rs:12-156` and
     `compiler/rustc_trait_selection/src/traits/vtable.rs:17-187, 374-450`
     (`VtblEntry`, `COMMON_VTABLE_ENTRIES`, `prepare_vtable_segments`,
     `emit_vptr_on_upcast`, and `supertrait_vtable_slot`).
   - `compiler/rustc_codegen_cranelift/src/unsize.rs:1-294`,
     `compiler/rustc_codegen_cranelift/src/vtable.rs:1-88`, and
     `compiler/rustc_codegen_cranelift/src/value_and_place.rs:11-56, 671-701`
     (`unsized_info`, `vtable_memflags`, `size_and_align_of_dst`, and
     `codegen_field`).
   - `compiler/rustc_codegen_cranelift/src/num.rs:150-346` and
     `compiler/rustc_codegen_cranelift/src/codegen_i128.rs:1-83`
     (`codegen_checked_int_binop` and 128-bit arithmetic lowering).
   - `compiler/rustc_codegen_ssa/src/mir/place.rs:175-336, 431-450` and
     `compiler/rustc_codegen_ssa/src/mir/rvalue.rs:514-605, 920-970`.
   - `compiler-builtins/src/int/mul.rs:1-206` (`UMulo::mulo`, `Mulo::mulo`,
     `__rust_u128_mulo`, and `__rust_i128_mulo`).

## Revalidation

1. **Re-run Both Standalone Lean `v4.34.1` Probes:**
   From this report package directory, run:
   ```console
   lean -j1 -M1024 support/track5_isle_egraph_dst_probe.lean
   lean -j1 -M1024 support/round2_track4_probe.lean
   ```
   Both commands must exit with code `0` and zero output, confirming that all
   60 theorems across the two files and all 27 `#guard_msgs in #print axioms`
   assertions hold using only subsets of `{propext, Classical.choice,
   Quot.sound}`.
2. **Check Upstream Cranelift and `rustc` Drift:**
   - Diff `cranelift/codegen/src/egraph/{mod.rs,elaborate.rs}` and
     `cranelift/codegen/src/inst_predicates.rs` when upgrading
     `cranelift-codegen` to verify that `is_pure_for_egraph`, `subsume`, and
     `loop_hoist_level` preserve the invariants modeled in Section 1.
   - Diff
     `compiler/rustc_codegen_cranelift/src/{num.rs,codegen_i128.rs,unsize.rs,vtable.rs,value_and_place.rs}`
     and `compiler/rustc_trait_selection/src/traits/vtable.rs` when upgrading
     `rust-lang/rust` to check whether `vtable_memflags()` adds `set_can_move()`
     or `value_and_place.rs:28-30` adds `ty::Foreign(..)`.
