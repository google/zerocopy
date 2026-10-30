# Block-Argument SSA (`AnSSA`), Verified `mem2reg`/`SROA`, and MIR-to-SSA Semantic Lowering Hazards

## Summary

Lowering `Runtime(PostCleanup)` MIR to a register-oriented backend (Cranelift,
LLVM IR, or direct machine code) crosses a fundamental semantic boundary: MIR is
a memory-and-place machine in which every local `_0 .. _n` occupies an
addressable slot, whereas mid-end optimizers and instruction selectors operate
on Static Single Assignment (SSA) values. Closing this gap in a formally
verified Rust compiler requires solving two coupled problems:

1. **Structural SSA Representation and Promotion (`AnSSA` and `checkMem2Reg`):**
   Classical $\phi$-node SSA (as mechanized in CompCertSSA and Vellvm) requires
   global dominance-tree well-formedness invariants, critical-edge splitting,
   and simultaneous parallel-move semantics at basic-block entries. By contrast,
   a **block-argument SSA intermediate representation (`AnSSA`)**—modeled on
   Lean 4's LCNF join points (`Code.jp` / `Code.jmp` in `leanprover/lean4` at
   `5045d0056413266e57c625dcd7c365b10e377c52`) and Cranelift's basic-block
   parameters (`SSABuilder` in `bytecodealliance/wasmtime` at
   `87282b8fd77fa9fbba6caadb0be690bedec2dc64`)—places SSA merges onto
   control-flow edges as explicit argument vectors bound simultaneously to
   target block parameters (`bindParams`). Under this representation, `mem2reg`
   and field-sensitive scalar replacement of aggregates (`SROA`) are verified by
   a single-pass $O(|V| + |E|)$ symbolic translation validator (`checkMem2Reg`)
   that requires no verified Lengauer-Tarjan dominator tree or mutable Braun DFG
   invariants inside the trusted computing base (TCB).
2. **Rust-Specific MIR-to-SSA Semantic Lowering Hazards:**
   Promoting MIR places to SSA registers is unsound if the mid-end IR adopts
   naive C or LLVM scalar assumptions. Primary-source inspection of
   `rust-lang/rust`
   at `8006091eb71ae7d9e9bccb66c6122c9d68af4466` and
   `e402c1edf047a23b0cfef40c6097d1caa294050b`
   (PR `#154341`), paired with a 1,494-line Lean `v4.34.1` mechanization
   ([`support/track3_ssa_mem2reg_niche_probe.lean`](support/track3_ssa_mem2reg_niche_probe.lean)),
   establishes four mandatory semantic invariants for `AnSSA`:
   - **`MaybeUninit<T>`, `Scalar::Union`, and Struct Padding:** `Scalar::Union`
     values (`is_uninit_valid() == true`) and uninitialized padding bytes must
     never be promoted to multi-valued LLVM-style `undef` registers, which
     refute `Compiles` under common subexpression elimination and copy
     propagation (`multi_undef_refutes_compiles`). Promotion must either
     preserve byte-level initialization (`ByteVal` / `MaskedWord`) or apply a
     coherent `freeze` at the promotion boundary (`freeze_copy_prop_sound`,
     `freeze_self_eq_and_sub_zero`).
   - **Aliasing, `!Unpin` , `UnsafeCell` , and `Rvalue::Use(op, WithRetag)` (PR
     `#154341` ):**
     Upstream `rustc` commit `e402c1edf047a23b0cfef40c6097d1caa294050b` deleted
     standalone `StatementKind::Retag` statements and folded retagging into
     `Rvalue::Use(Operand, WithRetag)`. Because `WithRetag::Yes` mutates the
     borrow-tracker state (`Tree Borrows` / `Stacked Borrows`), `AnSSA` cannot
     treat `Rvalue::Use(op, WithRetag::Yes)` as a pure SSA expression: it must
     lower `WithRetag::Yes` on `Unpin` mutable references and `Freeze` shared
     references to an explicit side-effectful `AnSSAStmt.retag` instruction
     while
     suppressing retagging inside `!Unpin` (`UnsafePinned`), `UnsafeCell`
     (`!Freeze`), and `MaybeDangling` wrappers
     (`retag_eligibility_classification`).
   - **`Variants::Multiple` and `TagEncoding::Niche` Wrapping Modular
     Subtraction:**
     Niche-encoded enums decode their active variant via wrapping $w$-bit
     modular subtraction `(tag - nicheStart) ≤ᵤ nicheSpan`
     (`decode_encode_niche_tagged`, `decode_encode_niche_untagged`,
     `wrappingNiche8_verified`). Lowering passes must load the discriminant tag
     using the outer enum's combined `tag` validity range rather than the
     untagged payload's narrower validity range; attaching `!nonnull` or payload
     `!range` metadata prior to discriminant decoding introduces artificial
     target UB on niche variants such as `Option<NonZeroU8>::None`
     (`premature_payload_range_unsound`).
   - **Zero-Sized Types (`ZST`, `size == 0` ) and Uninhabited Types (`!` /
     `Variants::Empty` ):**
     Every `ZST` place read, write, copy, and pointer offset must lower to a
     no-op (`LocalKind::ZST` / `OperandValue::ZeroSized`) without emitting
     hardware memory accesses, preserving safety on `NonNull::dangling()`
     (`zst_elision_compiles`, `naive_zst_load_refutes_compiles`). Conversely,
     constructing an uninhabited enum variant, setting an uninhabited
     discriminant, or reaching `TerminatorKind::Return` in a function with an
     uninhabited return layout must emit an explicit machine trap
     (`abort_immediate` / `AnSSATerm.trap`) prior to `unreachable`.

## Applicability

These findings apply to the combination and interaction of the examined
subjects:

- **Anneal Trusted MIR Semantics and Refinement Algebra (`joshlf/anneal` at
  `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`):**
  Applies to `trusted/lean/Trusted/MirAst.lean`, `MirSemantics.lean`,
  `Memory.lean`, `Refinement.lean`, and `StepResult.lean`. Specifically, it
  governs updating `Trusted/MirAst.lean` from pre-`#154341`
  `StatementKind.retag`
  to post-`#154341` `Rvalue.use (op : Operand) (withRetag : Bool)` and composing
  the MIR-to-`AnSSA` refinement proof (`Compiles MirLang (AnSSALang entryMap)
  (π_ssa locals blockMap)`) via `Compiles.trans` and `π_ssa_monotone`.
- **Rust Compiler MIR Transforms, ABI Layout, and Codegen (`rust-lang/rust` at
  `8006091eb71ae7d9e9bccb66c6122c9d68af4466` and PR `#154341` at
  `e402c1edf047a23b0cfef40c6097d1caa294050b`):**
  Applies to `Runtime(PostCleanup)` MIR produced after `sroa`
  (`compiler/rustc_mir_transform/src/sroa.rs`) and `SsaLocals`
  (`compiler/rustc_mir_transform/src/ssa.rs`), ABI layout computation in
  `compiler/rustc_abi/src/{lib.rs,layout.rs}` and
  `compiler/rustc_ty_utils/src/abi.rs`, and SSA lowering in
  `compiler/rustc_codegen_ssa/src/mir/` and
  `compiler/rustc_codegen_cranelift/src/discriminant.rs`.
- **Cranelift and Lean 4 Block-Argument SSA Architectures
  (`bytecodealliance/wasmtime` at `87282b8fd77fa9fbba6caadb0be690bedec2dc64` and
  `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`):**
  Applies to the design of `AnSSA`'s parameterized basic-block CFG (`SSABlock`
  with `params : List SSAId` and outgoing edge argument lists
  `args : List SSAExpr` ),
  which maps directly to Lean 4 LCNF join points (`Code.jp` / `Code.jmp`) and
  Cranelift CLIF block parameters (`dfg.append_block_param` /
  `block.append_argument`).
- **Companion Reference Reports in This Corpus:**
  The three cross-track follow-up seams identified during this investigation are
  resolved and mechanized in companion reports:
  - [`reports/rustc-codegen-anneal-monomorphization-abi-and-intrinsics-2026/`](../rustc-codegen-anneal-monomorphization-abi-and-intrinsics-2026/REPORT.md)
    resolves `BackendRepr::ScalarPair` byte-offset field projection
    (`extractScalarPairByOffset`), sub-word niche extraction in two-register
    pairs (`scalarPair_decode_encode_niche_tagged`), and `PassMode::Cast`
    byte-masked register packing (`MaskedWord` + `freezeMaskedWord`).
  - [`reports/verified-rust-compiler-self-hosting-and-certifying-bootstrap-2026/`](../verified-rust-compiler-self-hosting-and-certifying-bootstrap-2026/REPORT.md)
    resolves the operational lowering of post-`#154341`
    `Rvalue.use op withRetag`
    to `AnSSAStmt.retag` vs. `AnSSAStmt.letCopy` (`retag_lowering_compiles`,
    `retag_copy_prop_compiles`, `duplicate_retag_refutes_compiles`, and
    `erase_withRetag_refutes_compiles`).
  - [`reports/anllvm-verified-llvm-lowering-tree-borrows-noalias-and-binary-tv-2026/`](../anllvm-verified-llvm-lowering-tree-borrows-noalias-and-binary-tv-2026/REPORT.md)
    resolves the relational simulation from Tree Borrows (`ReservedFrz`,
    `Active`, `Frozen`, `Disabled` + function-entry protectors) to LLVM
    `noalias`, `readonly`, and `writable` attributes
    (`treeBorrows_implies_llvm_noalias_readonly_sound`) and `AnByteWord`
    (`DTYPE_B`) widened aggregate loads (`passModeCast_byte_vs_int_load_sound`).

## Findings

### 1. Block-Argument SSA (`AnSSA`) vs. $\phi$-Node SSA

`Basis: source + execution + derived`

#### 1.1 Why $\phi$-Node SSA Complicates Mechanized Small-Step Semantics

In classical $\phi$-node SSA (as mechanized in CompCertSSA's `midend/SSA.v` and
`midend/SSAvalid.v` and Vellvm's `DynamicValues.v` / `LLVMAst.v`), join points
place pseudo-instructions `x_0 = phi(bb_1: x_1, ..., bb_k: x_k)` at the head of
a basic block. Formalizing $\phi$-node SSA in an interactive theorem prover
imposes three structural proof burdens:

1. **Predecessor-Indexed Small-Step State and CFG Normalization:** Evaluating a
   $\phi$-node requires the operational machine state to record the *previous*
   basic block identifier `prev_bb` alongside the current block identifier
   `curr_bb`. Furthermore, if a predecessor branches to the same target block on
   multiple edges (a critical edge or `SwitchInt` with duplicate targets),
   indexing by `prev_bb` is ambiguous unless critical edges are split or edges
   carry distinct indices.
2. **Simultaneous Parallel-Move Semantics:** All $\phi$-nodes at the entry of a
   join block must be evaluated simultaneously in the predecessor's register
   environment before updating any target register; evaluating $\phi$-nodes
   sequentially miscompiles cyclic swaps (the classic "swap problem" and
   "lost-copy problem").
3. **Global Dominance Well-Formedness (`wf_ssa_function`):** Stating that a
   $\phi$-node CFG is well-formed requires proving that every use of an SSA
   register is dominated by its unique definition site (or precedes the incoming
   CFG edge of a $\phi$-operand), pulling global dominator-tree invariants into
   the syntax and typing judgment of the IR.

#### 1.2 Parameterized Basic Blocks in Lean 4 LCNF and Cranelift `SSABuilder`

Both **Lean 4's LCNF compiler** (`leanprover/lean4` at
`5045d0056413266e57c625dcd7c365b10e377c52`) and **Cranelift's SSA frontend**
(`bytecodealliance/wasmtime` at `87282b8fd77fa9fbba6caadb0be690bedec2dc64`,
`cranelift/frontend/src/ssa.rs:1-658`) eliminate $\phi$-nodes in favor of
**parameterized basic blocks (join points)**:

- **Lean 4 LCNF (`src/Lean/Compiler/LCNF/Basic.lean:180-360` and
  `Check.lean:95-190`):**
  Represents local control-flow merges as join-point declarations
  `Code.jp (decl : FunDecl pu) (k : Code pu)` and jumps as
  `Code.jmp (fvarId : FVarId) (args : Array (Arg pu))`. In
  `Check.lean:154-166`, well-formedness reduces to local lexical scope checking
  (`checkJpInScope`) and an arity equality check `decl.getArity == args.size`.
  Compiler passes such as `CSE.lean:1-210`, `JoinPoints.lean:1-260`, and
  `SimpCase.lean:1-180` recurse structurally over `Code` without maintaining
  $\phi$-node predecessor tables.
- **Cranelift `SSABuilder` (`cranelift/frontend/src/ssa.rs:34-658`):**
  Implements Braun et al.'s (CC 2013) on-the-fly SSA construction directly over
  basic-block parameters:
  - Each basic block maintains a formal parameter list
    (`dfg.append_block_param(block, ty)`, line `366`), and each predecessor
    branch instruction carries an explicit per-edge argument list
    (`block.append_argument(val, &mut dfg.value_lists)`, line `611`).
  - Unsealed loop headers (`Sealed::No { undef_variables }`, lines `88-94`)
    allocate placeholder block parameters on demand (`use_var_nonlocal`, lines
    `341-376`) and wire predecessor edge arguments when `seal_block` is invoked
    (lines `515-563`).

| Architectural Dimension | $\phi$-Node SSA (CompCertSSA / Vellvm) | Block-Argument SSA (`AnSSA` / LCNF / Cranelift) |
| :--- | :--- | :--- |
| **Join syntax** | `x = phi(bb₁: v₁, ..., bbₖ: vₖ)` inside target block | Target block declares `params : List SSAId`; each outgoing terminator edge passes `args : List SSAExpr` |
| **Small-step machine state** | Must carry `prev_bb : BlockId` (or edge index) to evaluate $\phi$ table | Carries only `{ bb : BlockId, ssaEnv : Env SSAId, mem : Env LocalId }` |
| **Simultaneous parallel moves** | Requires a dedicated simultaneous $\phi$-block step | Native to edge transition: `bindParams ssaEnv' targetBlk.params (evalEdgeArgs ssaEnv' mem' args)` |
| **Critical / duplicate edges** | Must split critical edges or disambiguate multi-edges | Each branch target edge carries its own independent argument vector (`tArgs` vs. `fArgs`) |
| **Well-formedness & arity check** | Global dominance tree + predecessor-list bijection | Local per-edge check: `args.length == targetBlk.params.length` |

In
[`support/track3_ssa_mem2reg_niche_probe.lean`](support/track3_ssa_mem2reg_niche_probe.lean)
(lines `360-476`), `AnSSABody` formalizes this block-argument SSA machine:

```lean
inductive SSATerm where
  | jump (target : BlockId) (args : List SSAExpr)
  | branch (cond : SSAExpr)
      (tTarget : BlockId) (tArgs : List SSAExpr)
      (fTarget : BlockId) (fArgs : List SSAExpr)
  | ret (val : SSAExpr)

structure SSABlock where
  params : List SSAId
  stmts  : List SSAStmt
  term   : SSATerm
```

When `stepSSA` (lines `439-467`) executes a terminator edge to `target` with
argument expressions `args` , it evaluates
`vals := evalEdgeArgs ssaEnv' mem' args`
in the predecessor's post-statement environment `(ssaEnv', mem')` and binds them
to `targetBlk.params` via `bindParams ssaEnv' targetBlk.params vals` . Because
all
arguments in `args` are evaluated before `bindParams` updates `ssaEnv'`, cyclic
register swaps across loop backedges execute as an atomic parallel move without
temporary scratch registers or $\phi$-simultaneity side conditions.

---

### 2. Linear-Time Symbolic `checkMem2Reg` and Field-Sensitive `SROA` Validation

`Basis: source + execution + derived`

#### 2.1 Translation Validation vs. Constructive Braun / Lengauer-Tarjan Proofs

Promoting MIR locals and flattened aggregate fields into `AnSSA` registers can
be verified under two distinct architectures:

- **Constructive Verification of SSA Construction:** Proving the SSA
  construction algorithm itself sound in Lean 4 requires mechanizing either
  Lengauer-Tarjan dominance frontiers (as in
  `compiler/rustc_mir_transform/src/ssa.rs:51-127` at commit
  `8006091eb71ae7d9e9bccb66c6122c9d68af4466`) or Braun et al.'s recursive
  predecessor graph traversal with fuel/termination proofs and mutable DFG
  aliasing invariants (`cranelift/frontend/src/ssa.rs:381-615`,
  `results_in_same_value` and `remove_block_param`).
- **Untrusted SSA Generator + Verified Linear-Time Symbolic Validator
  (`checkMem2Reg`):** An untrusted pass runs Braun's algorithm (or MIR `SROA` +
  `SsaLocals`) and emits the `AnSSABody` together with a per-block witness map
  `blockMap : BlockId → List (LocalId × SSAId)` recording which `SSAId` holds
  each promoted MIR local `l ∈ promoted` at the entry of basic block `bb`. The
  verified validator `checkAllBlocks`
  ([`support/track3_ssa_mem2reg_niche_probe.lean`](support/track3_ssa_mem2reg_niche_probe.lean),
  lines `553-650` and `946-954`) validates the transformation in a single
  $O(|V| + |E|)$ pass over the CFG:
  1. **Promotion Eligibility & Address-Taken Exclusion (`checkStmt`):**
     In `compiler/rustc_codegen_ssa/src/mir/analyze.rs:18-268`
     (`non_ssa_locals`)
     and `compiler/rustc_mir_transform/src/sroa.rs:84-142` (`escaping_locals`),
     any local whose address is taken (`Rvalue::Ref`, `Rvalue::RawPtr`, or
     indirect dereference mutation) is excluded from SSA promotion and kept in
     `LocalKind::Memory`. Likewise, `checkStmt` (lines `569-588`) rejects any
     indirect reference store `MirStmt.writeRef target rhsM` or unpromoted store
     `SSAStmt.storeMem` if `promoted.contains target == true`.
  2. **Straight-Line Symbolic Environment Evolution (`checkStmts`):**
     Starting from `σ₀ = blockMap bb`, `checkStmts` (lines `590-597`) steps in
     lockstep through `mBlk.stmts` and `sBlk.stmts`. A promoted assignment
     `MirStmt.assign dst rhsM` paired with `SSAStmt.letBind v rhsS` verifies
     `checkExpr promoted σ rhsM rhsS == true` and updates `σ ↦ (dst, v) :: σ`
     (subject to `StmtFresh σ`, ensuring `v` does not clobber any other live
     local's SSA register in `σ`).
  3. **Edge-Argument & Dominator-Inheritance Check (`checkEdgeArgs` /
    `checkTerm` ):**
     At the end of block `bb` with symbolic map `σ_end`, for each outgoing edge
     to `target` with argument list `args` and target entry map
     `targetMap = blockMap target`, `checkEdgeArgs` (lines `605-618`) splits
     `targetMap` into:
     - `paramPairs := targetMap.filter (fun (_, v) => targetParams.contains v)`
       (locals merged via `target`'s block parameters), verifying that
       `targetParams == paramPairs.map Prod.snd` and that `args` passes
       `SSAExpr.ssaVar v_src` where `lookupMap σ_end l = some v_src`; and
     - `inheritedPairs := targetMap.filter (fun (_, v) => !targetParams.contains v)`
       (locals whose SSA register `v` is inherited directly from a dominating
       block without being passed as a block parameter), verifying that
       `lookupMap σ_end l == some v` already holds at the end of `bb`.

#### 2.2 Mechanized Simulation Invariant and Negative Control

In
[`support/track3_ssa_mem2reg_niche_probe.lean`](support/track3_ssa_mem2reg_niche_probe.lean)
(lines `478-1050`), we define the state-reconstruction projection
`projSSAState locals blockMap : SSAState → MirState` and behavior morphism
`π_ssa locals blockMap`, and prove:

- **Monotonicity (`π_ssa_monotone`, lines `534-538`):** `Monotone (π_ssa locals
  blockMap)`, enabling vertical composition with upstream and downstream
  compiler passes via `Compiles.trans` (lines `119-129`).
- **Frame Simulation Invariant (`FrameInv`, lines `658-661`):**
  $$\text{FrameInv}(\text{promoted}, \sigma, \text{frame}, \text{ssaEnv}, \text{mem}) \iff \bigl(\forall l \in \text{promoted},\; \sigma(l) = \text{some } v \implies \text{frame}(l) = \text{ssaEnv}(v)\bigr) \;\wedge\; \bigl(\forall l \notin \text{promoted},\; \text{frame}(l) = \text{mem}(l)\bigr)$$
- **Inductive Expression and Statement Soundness (`checkExpr_sound`,
  `checkStmt_sound`, `checkStmts_sound`, lines `663-870`):** If `FrameInv` holds
  at block entry and `checkStmts promoted σ₀ stmtsM stmtsS = some σ_end` with
  `StmtsFresh`, then `FrameInv` holds at `σ_end` after executing `stmtsM` and
  `stmtsS`.
- **Diamond CFG End-to-End Equivalence (`diamond_mem2reg_validated` and
  `diamond_all_steps_exact_simulation`, lines `957-999`):** Verifies a 4-block
  diamond CFG (`diamondMir` $\to$ `diamondSSA`) combining three promoted SSA
  locals (`0, 1, 2`, where `2` is merged at join block `bb3` via block parameter
  `params = [20]`) with an unpromoted address-taken local (`3`, mutated via
  `writeRef 3`). Proves exact state-for-state equivalence across all fuels
  `f ∈ [0, 1, 2, 3]` on both branch paths.
- **Address-Taken Promotion Negative Control
  (`validator_rejects_illegal_promotion`
  and `illegal_promotion_refutes_compiles`, lines `1001-1049`):** Proves that
  promoting address-taken local `3` across `writeRef 3 (.const 99)` is rejected
  by `checkAllBlocks` (`= false`) and formally refutes `Compiles` (`aliasedMir`
  returns `99` whereas `illegallyPromotedSSA` returns stale register value `10`
  ).

#### 2.3 Field-Sensitive `SROA` Eligibility and `StorageLive`/`StorageDead` Hazards

Inspecting `compiler/rustc_mir_transform/src/sroa.rs:1-432` at commit
`8006091eb71ae7d9e9bccb66c6122c9d68af4466` reveals the exact conditions under
which `rustc` flattens an aggregate local into per-field MIR locals:

1. **Exclusion of Unions and Multi-Variant Enums (`sroa.rs:165-190`):**
   `compute_flattening` only flattens types whose `Variants` shape is
   `Variants::Single { index }` and excludes `TyKind::Adt(def, _)` when
   `!def.is_struct()` (thus never flattening `union` types such as
   `MaybeUninit<T>` into scalar fields at the MIR `SROA` stage).
2. **Escaping / Address-Taken Sub-Places (`sroa.rs:84-142`):**
   `escaping_locals` uses `PlaceVisitor` to reject any local that is borrowed
   (`Rvalue::Ref`), converted to a raw pointer (`Rvalue::RawPtr`), or indexed by
   a non-constant projection (`ProjectionElem::Index`, `ConstantIndex`,
   `Subslice`, `Downcast`, or `OpaqueCast`).
3. **`StorageLive` / `StorageDead` Replacement (`sroa.rs:316-331`):**
   When an aggregate local `local` is flattened into child locals
   `f_1, ..., f_k`, every `StatementKind::StorageLive(local)` and
   `StorageDead(local)` is expanded into `StorageLive(f_i)` and
   `StorageDead(f_i)` for all `i`, while the original aggregate local is marked
   dead. In `AnSSA`, promoting a local (or flattened field) to an SSA register
   elides stack allocation entirely; however, if `StorageDead` is used by
   borrow-check/Miri to invalidate pointers into a stack local, the
   address-taken
   exclusion (`l ∉ promoted`) guarantees that no valid pointer can ever target a
   promoted SSA local across `StorageDead`.
4. **`BackendRepr::ScalarPair` Byte-Offset Dispatch:**
   As resolved and mechanized in the companion report
   [`reports/rustc-codegen-anneal-monomorphization-abi-and-intrinsics-2026/`](../rustc-codegen-anneal-monomorphization-abi-and-intrinsics-2026/REPORT.md)
   ,
   when `AnSSA` represents two-scalar aggregates (`(A, B)`, `&[T]`,
   `Option<(u64, NonZeroU64)>`) natively as `ScalarPairVal { fst, snd }`, field
   extraction and insertion must dispatch on **byte offset**
   (`layout.fields.offset(i) == 0` vs. `b_offset > 0`, matching
   `rustc_codegen_ssa`'s `OperandRef::extract_field` in
   `compiler/rustc_codegen_ssa/src/mir/operand.rs:383-454`), never on raw
   `FieldIdx`.

---

### 3. `MaybeUninit<T>`, `Scalar::Union`, and Struct Padding: `ByteVal` and `freeze` vs. Multi-Valued `undef`

`Basis: source + execution + derived`

#### 3.1 How `rustc` Represents Uninitialized Scalars (`Scalar::Union`)

In `compiler/rustc_abi/src/lib.rs:1575-1685` (commit
`8006091eb71ae7d9e9bccb66c6122c9d68af4466`), `rustc` partitions scalar ABI
representations into two variants:

```rust
pub enum Scalar {
    Initialized {
        value: Primitive,
        valid_range: WrappingRange,
    },
    Union {
        value: Primitive,
    },
}
```

Single-scalar unions—most notably `MaybeUninit<u64>`, `MaybeUninit<*const T>`,
and the non-niche scalar of a `BackendRepr::ScalarPair` niche-encoded enum
(`compiler/rustc_abi/src/layout.rs:711-728`)—have
`BackendRepr::Scalar(Scalar::Union { .. })`, for which
`Scalar::is_uninit_valid(&self)` returns `true`
(`compiler/rustc_abi/src/lib.rs:1680-1684`). As noted in
`compiler/rustc_codegen_ssa/src/mir/operand.rs:233-239`:

> *"However, `MaybeUninit<u64>` is considered a `Scalar` as far as its layout is
> concerned -- and yet cannot be represented by an interpreter `Scalar`, since
> we have to handle the case where some of the bytes are initialized and others
> are not."*

To prevent LLVM from treating an uninitialized `Scalar::Union` load or function
argument as immediate UB:
- `compiler/rustc_codegen_llvm/src/builder.rs:759-761` attaches `!noundef` load
  metadata **only** when `!scalar.is_uninit_valid()`; and
- `compiler/rustc_ty_utils/src/abi.rs:328-330` attaches `ArgAttribute::NoUndef`
  to function arguments and return values **only** when
  `!scalar.is_uninit_valid()`.

#### 3.2 Why Multi-Valued `undef` Is Unsound Under SSA and How `freeze` Restores Refinement

Even when `!noundef` is omitted, lowering an uninitialized byte
(`ByteVal.uninit`)
to an SSA register with LLVM's legacy multi-valued `undef` semantics—in which
each read of the same SSA register can independently choose a different bit
pattern—is **unsound**:

- In MIR memory, a local `x : MaybeUninit<u8>` occupies a fixed allocation whose
  bytes do not spontaneously mutate between reads. Once `x` is promoted to an
  SSA register `x_ssa` and copied via `let y = x_ssa`, every read of `x_ssa` and
  `y` must observe the **same** bit pattern.
- Under multi-valued `undef`, common subexpression elimination or copy
  propagation rewriting `let y = x; x == y` into `x == x` allows the two uses of
  `x` in `x == x` to pick distinct witnesses `w₁ = 0#8` and `w₂ = 1#8`,
  evaluating `x == x` to `0#8` (`false`).

In Section 2 of
[`support/track3_ssa_mem2reg_niche_probe.lean`](support/track3_ssa_mem2reg_niche_probe.lean)
(lines `1055-1158`), we mechanize `ByteVal` (`.uninit | .init (b : BitVec 8)`)
and `freezeByte (oracleBits : BitVec 8) : ByteVal → BitVec 8`, proving:

1. **Refutation of Multi-Valued `undef` (`multi_undef_refutes_compiles`, lines
   `1152-1157`):**
   $$\neg\,\text{Compiles}\;\text{FrozenSelfEqLang}\;\text{MultiUndefSelfEqLang}\;\text{id}\;()\;()$$
   Witnessed by `slotVal = .uninit`, `w1 = 0#8`, `w2 = 1#8`, where
   `FrozenSelfEqLang` returns `1#8` (`true`) while `MultiUndefSelfEqLang`
   returns `0#8` (`false`).
2. **Soundness of Coherent `freeze` Across Copy Propagation and CSE
   (`freeze_copy_prop_sound` and `freeze_self_eq_and_sub_zero`, lines
   `1092-1121`):**
   Binding `v := freezeByte oracleBits bVal` once at the promotion site ensures
   that substituting `x` for `y` (`substVar y x e`) preserves exact expression
   semantics `evalFrozenBitExpr env (substVar y x e) = evalFrozenBitExpr env e`
   for **every** `bVal : ByteVal` and **every** `oracleBits : BitVec 8`, and
   guarantees `x == x = 1#8` and `x - x = 0#8`.

For multi-byte `Scalar::Union` values and `PassMode::Cast` widened integer
registers containing uninitialized padding bytes, `AnSSA` tracks
per-bit/per-byte
initialization masks (`MaskedWord := { bits : BitVec 64, initMask : BitVec 64 }`
in
[`reports/rustc-codegen-anneal-monomorphization-abi-and-intrinsics-2026/`](../rustc-codegen-anneal-monomorphization-abi-and-intrinsics-2026/REPORT.md)
and `AnByteWord := Fin 8 → PoisonOr (BitVec 8)` in
[`reports/anllvm-verified-llvm-lowering-tree-borrows-noalias-and-binary-tv-2026/`](../anllvm-verified-llvm-lowering-tree-borrows-noalias-and-binary-tv-2026/REPORT.md)
),
applying per-byte `freeze` so that uninitialized padding lanes never taint
adjacent initialized field bytes.

---

### 4. Upstream `rustc` PR `#154341` (`Rvalue::Use(op, WithRetag)`) and Aliasing Attributes

`Basis: source + execution + derived`

#### 4.1 Exact Conditions for `NoAlias`, `NoFree`, and `ReadOnly` in `rustc`

Inspection of `compiler/rustc_ty_utils/src/abi.rs:350-410` at commit
`8006091eb71ae7d9e9bccb66c6122c9d68af4466` establishes the exact conditions
under which `rustc` attaches aliasing metadata to pointer-like scalars
(`PointerKind`):

| `PointerKind` Variant | `NoAlias` Condition | `NoFree` Condition | `ReadOnly` / `CapturesReadOnly` | Primary Source Citation & Semantic Invariant |
| :--- | :--- | :--- | :--- | :--- |
| `SharedRef { frozen }` (`&T`) | `frozen && !is_return` | `!is_return` | `frozen && !is_return` | `rustc_ty_utils/src/abi.rs:354-380`: `frozen` holds iff `T: Freeze` (no `UnsafeCell`). Interior mutability suppresses both `NoAlias` and `ReadOnly`. |
| `MutableRef { unpin }` (`&mut T`) | `unpin && !is_return` | `!is_return` | Never | `rustc_ty_utils/src/abi.rs:384-396`: `unpin` holds iff `T: Unpin` (no `PhantomPinned` / `UnsafePinned`). Self-referential `!Unpin` coroutines alias across suspension points. |
| `Box { unpin, global }` (`Box<T, A>`) | `unpin && global && noalias_for_box && !is_return` | **Never** | Never | `rustc_ty_utils/src/abi.rs:398-409`: `Box` may be deallocated inside the callee, so `NoFree` is unconditionally omitted. |
| Raw pointers (`*const T`, `*mut T`) | Never | Never | Never | Represented as `Primitive::Pointer` without `PointeeInfo`. |

#### 4.2 Architectural Shift in `rustc` PR `#154341`: Retag-on-Typed-Copy

In `rust-lang/rust` commit `e402c1edf047a23b0cfef40c6097d1caa294050b` (PR
`#154341`, *"Replace explicit `Retag` statements by 'retag-on-typed-copy'"*),
standalone `StatementKind::Retag(RetagKind, Box<Place>)` and the `AddRetag` MIR
pass (`compiler/rustc_mir_transform/src/add_retag.rs`) were removed:

1. **Syntax Change (`compiler/rustc_middle/src/mir/syntax.rs:497-511,
  1359-1360`):**
   `Rvalue::Use(Operand<'tcx>)` was replaced by
   `Rvalue::Use(Operand<'tcx>, WithRetag)`, where `enum WithRetag { No, Yes }`
   specifies whether the typed copy performs a borrow-tracker retag.
2. **Operational Semantics in Miri
  (`compiler/rustc_const_eval/src/interpret/step.rs:179-184`):**
   Evaluating `Rvalue::Use(operand, retag)` invokes
   `copy_op(op, dest, retag_mode)`
   with `RetagMode::Default` when `retag == WithRetag::Yes`.
3. **Layout-Guided Retagging
  (`compiler/rustc_codegen_ssa/src/mir/rvalue.rs:146-163`
   and `retag.rs:67-263`):**
   When `retag == WithRetag::Yes` and `-Zmir-emit-retag` is enabled,
   `RetagVisitor` walks the type layout of the copied value:
   - It skips `UnsafePinned` (`!Unpin`) and `MaybeDangling` wrappers
     (`retag.rs:150-162`) because references inside `MaybeDangling` or `!Unpin`
     types may be dangling or aliased.
   - It recurses into structs, tuples, arrays, and single-variant enums
     (`Variants::Single`), and branches at runtime on the discriminant of
     multi-variant enums (`Variants::Multiple`, `retag.rs:94-141`) to retag only
     the active variant's reference fields.
4. **Interaction with MIR `SROA` (`compiler/rustc_mir_transform/src/sroa.rs:347,
  373, 409-413`):**
   When `SROA` flattens a struct copy
   `lhs = Rvalue::Use(Operand::Copy(rhs), retag)`
   into per-field assignments, it threads `retag` onto every decomposed field
   copy `Rvalue::Use(Operand::Copy(field), retag)` (and sets `WithRetag::Yes`
   when decomposing `Rvalue::Aggregate` at line `347`).

In Section 4B of
[`support/track3_ssa_mem2reg_niche_probe.lean`](support/track3_ssa_mem2reg_niche_probe.lean)
(lines `1370-1397`), `fieldNeedsNoaliasRetag` and
`retag_eligibility_classification` formalize the exact field-level eligibility
predicate (`uniqueMutRef ↦ true`, `pinnedMutRef ↦ false`,
`sharedRefFreeze ↦ true`, `sharedRefUnsafeCell ↦ false`, `rawScalar ↦ false`).

Furthermore, as mechanized in
[`reports/verified-rust-compiler-self-hosting-and-certifying-bootstrap-2026/`](../verified-rust-compiler-self-hosting-and-certifying-bootstrap-2026/REPORT.md)
,
`AnSSA` **cannot** treat `Rvalue::Use(op, WithRetag::Yes)` as a pure SSA
expression:
- Lowering `WithRetag::Yes` to a dedicated side-effectful statement
  `AnSSAStmt.retag dst src` and `WithRetag::No` to a pure binding
  `AnSSAStmt.letCopy dst src` satisfies `Compiles` (`retag_lowering_compiles`),
  and subsequent `WithRetag::No` copies of `dst` can be freely copy-propagated
  (`retag_copy_prop_compiles`).
- Treating `WithRetag::Yes` as a pure duplicable expression and duplicating
  `retag` at downstream uses allocates a second fresh exclusive tag that
  invalidates the first tag (`duplicate_retag_refutes_compiles`), whereas
  erasing `WithRetag::Yes` into a pure copy leaves stale tags active and fails
  refinement (`erase_withRetag_refutes_compiles`).

---

### 5. `Variants::Multiple` and `TagEncoding::Niche` Wrapping Modular Subtraction

`Basis: source + execution + derived`

#### 5.1 Exact Modular Arithmetic Specification Across `rustc_codegen_ssa` and `rustc_codegen_cranelift`

In `compiler/rustc_abi/src/lib.rs:2079-2085` (commit
`8006091eb71ae7d9e9bccb66c6122c9d68af4466`), `TagEncoding::Niche` encodes a
multi-variant enum having one `untagged_variant` (which stores its payload
directly) and a contiguous range of ZST/niche variants
`niche_variants: RangeInclusive<VariantIdx>` mapped into invalid bit patterns of
the untagged payload starting at `niche_start: u128` modulo $2^w$ (where $w$ is
the bitwidth of the `tag` scalar primitive).

Both `compiler/rustc_codegen_ssa/src/mir/operand.rs:556-708`
(`codegen_get_discr`)
and `compiler/rustc_codegen_cranelift/src/discriminant.rs:136-214`
(`codegen_get_discriminant`) implement the identical wrapping modular decoding
algorithm over $w$-bit bitvectors (`BitVec w`):

1. **Tag Encoding (`place.rs:420-439`, `discriminant.rs:58-59`):**
   For any variant $v \in \text{niche\_variants}$ with relative index
   $\text{relIdx} = v - \text{niche\_variants.start}$:
   $$\text{encodeNicheRel}(L, \text{relIdx}) = (\text{nicheStart} + \text{relIdx}) \bmod 2^w$$
2. **Tag Decoding (`operand.rs:621-653`, `discriminant.rs:163-190`):**
   Given a loaded $w$-bit `tag` and
   $\text{nicheSpan} = \text{niche\_variants.end} - \text{niche\_variants.start}$
   :
   $$\text{relDiscr} = (\text{tag} - \text{nicheStart}) \bmod 2^w$$
   $$\text{isNiche} \iff \text{relDiscr} \le_u \text{nicheSpan}$$
   $$\text{decodeNicheTag}(L, \text{tag}) = \begin{cases} (\text{nicheVariantsStart} + \text{relDiscr}) \bmod 2^w & \text{if } \text{relDiscr} \le_u \text{nicheSpan} \\ \text{untaggedVariant} & \text{otherwise} \end{cases}$$

As documented in `compiler/rustc_abi/src/lib.rs:2084` (*"Note that the niche
value might wrap around"*), $\text{nicheStart} + \text{relIdx}$ may wrap past
$2^w - 1$ through $0$ (for example, when an untagged `u8` payload has valid
range `2 ..= 253`, the 4-element niche `[254, 255, 0, 1]` starts at
`nicheStart = 254` with `nicheSpan = 3` and wraps across `0`). Because
$(\text{nicheStart} + \text{relIdx}) - \text{nicheStart} = \text{relIdx}$ holds
unconditionally in the ring $\mathbb{Z}/2^w\mathbb{Z}$
(`bitvec_add_sub_cancel`),
a single wrapping subtraction followed by a single unsigned comparison `≤ᵤ`
decodes both non-wrapping and wrapping niches, whereas an unwrapped two-sided
range check `nicheStart ≤ᵤ tag ∧ tag ≤ᵤ nicheEnd` fails whenever
`nicheStart + nicheSpan` wraps modulo $2^w$.

In Section 3 of
[`support/track3_ssa_mem2reg_niche_probe.lean`](support/track3_ssa_mem2reg_niche_probe.lean)
(lines `1163-1250`), we prove:
- **`bitvec_add_sub_cancel` (lines `1186-1193`):**
  `∀ {w : Nat} (a b : BitVec w), (a + b) - a = b` (proved via
  `BitVec.eq_of_toNat_eq` and `omega`, without `bv_decide`).
- **`decode_encode_niche_tagged` (lines `1200-1203`):**
  Universal round-trip decoding for all bitwidths $w$ and all
  `BitVec.ule relIdx L.nicheSpan = true`.
- **`decode_encode_niche_untagged` (lines `1210-1213`):**
  Universal decoding to `L.untaggedVariant` for all untagged payload values
  satisfying `BitVec.ule (payload - L.nicheStart) L.nicheSpan = false`.
- **`optNonZeroU8_exhaustive_correct` (lines `1224-1227`) &
  `wrappingNiche8_verified` (lines `1241-1250`):**
  Exhaustive verification across all 256 byte values of `Option<NonZeroU8>` and
  of a 4-variant wrapping niche `[254, 255, 0, 1]` modulo 256.

#### 5.2 The Premature Payload Validity-Range Hazard (`premature_payload_range_unsound`)

A subtle soundness hazard arises if an `SROA` or discriminant-lowering pass
loads
the niche tag using the **untagged variant's field layout** (such as `NonZeroU8`
with `valid_range = 1..=255` or `&T` with `!nonnull`) rather than the **outer
enum's `tag` scalar layout** (`Variants::Multiple { tag, .. }`, whose
`valid_range` is the union of the untagged payload's valid range and the niche
range, i.e., `0..=255` for `Option<NonZeroU8>`).

In `compiler/rustc_codegen_ssa/src/mir/operand.rs:502-505`, `codegen_get_discr`
projects `tag_field` from `self.layout` (the outer enum layout) before calling
`bx.load_operand(tag)`. If a pass instead projects into the downcast untagged
variant or attaches `!nonnull` / `!range ![1, 0]` metadata before decoding the
discriminant, evaluating `Rvalue::Discriminant` on `Option<NonZeroU8>::None`
(`tag = 0#8`) triggers immediate target UB (`premature_payload_range_unsound`,
lines `1269-1275`).

---

### 6. Zero-Sized Types (`ZST`) and Uninhabited Types (`!` / `Variants::Empty`)

`Basis: source + execution + derived`

#### 6.1 Zero-Sized Types (`LocalKind::ZST` and `OperandValue::ZeroSized`)

In Rust's operational semantics, any non-null, suitably aligned pointer—such as
`NonNull::<T>::dangling()` at address `align_of::<T>()` with allocation size
`0`—is valid for zero-sized reads, writes, and copies (`size_of::<T>() == 0`),
even when no backing memory allocation exists at that address.

`rustc_codegen_ssa` and `rustc_codegen_llvm` enforce this invariant at four
codegen
boundaries (commit `8006091eb71ae7d9e9bccb66c6122c9d68af4466`):

1. **Local Classification (`compiler/rustc_codegen_ssa/src/mir/analyze.rs:30,
  81, 225`):**
   Every local with `layout.is_zst()` is classified as `LocalKind::ZST`
   (distinct from both `LocalKind::SSA` and `LocalKind::Memory`), so no stack
   slot (`alloca`) or hardware register is allocated for it, even if its address
   is taken in MIR.
2. **Load Elision (`compiler/rustc_codegen_ssa/src/mir/operand.rs:1129-1131`,
   `compiler/rustc_codegen_llvm/src/builder.rs:742-744`):**
   `codegen_consume` and `load_operand` check `if place.layout.is_zst() { return
   OperandRef::zero_sized(place.layout); }` before emitting any backend load.
3. **Store and Copy Elision
  (`compiler/rustc_codegen_ssa/src/mir/operand.rs:1036-1039`,
   `traits/builder.rs:536`):**
   `OperandValue::store_with_flags` and `typed_place_copy_with_flags` return
   immediately as no-ops when `dest.layout.is_zst()`.
4. **Pointer Offset Elision
  (`compiler/rustc_codegen_ssa/src/mir/rvalue.rs:968-971`):**
   `BinOp::Offset` checks `if pointee.is_zst() { return lhs; }` without emitting
   an `inbounds` GEP.

In Section 4 of
[`support/track3_ssa_mem2reg_niche_probe.lean`](support/track3_ssa_mem2reg_niche_probe.lean)
(lines `1281-1346`), we prove `zst_elision_compiles` (for all `typeSize : Nat`)
and `naive_zst_load_refutes_compiles` (witnessed on `addr = 1, size = 0,
allocSize = 0`).

#### 6.2 Uninhabited Types (`!` / `Variants::Empty`) and Trap Generation

Uninhabited types (`!`, `enum Void {}`, or enum variants containing uninhabited
fields where `layout.is_uninhabited() == true`) require active trap insertion
(`bx.abort_immediate()` / `AnSSATerm.trap`) rather than passive omission at five
MIR lowering points in `compiler/rustc_codegen_ssa/src/mir/` (commit
`8006091eb71ae7d9e9bccb66c6122c9d68af4466`):

| MIR Construct | `rustc_codegen_ssa` Lowering | Primary Source Citation | Soundness Requirement |
| :--- | :--- | :--- | :--- |
| `StatementKind::SetDiscriminant` to an uninhabited variant | `bx.abort_immediate()` (`@llvm.trap` / `ud2` / `brk` / `unimp`) | `place.rs:216-221, 396-398` | Prevents fallthrough execution after setting an impossible variant tag. |
| `Rvalue::Aggregate` constructing an uninhabited enum variant | `bx.abort_immediate()` and skip field stores | `rvalue.rs:833-840` | Materializing an uninhabited enum variant in safe or unsafe code is immediate UB. |
| `Rvalue::Discriminant` on an uninhabited enum (`Variants::Empty`) | Returns dummy zero constant (`cx.const_uint(discr_ty, 0)`) | `operand.rs:471-473` | The discriminant read precedes a `SwitchInt` with zero targets (`TerminatorKind::Unreachable`). |
| `TerminatorKind::Return` when `fn_abi.ret.layout.is_uninhabited()` | `bx.abort_immediate(); bx.unreachable();` | `block.rs:585-595` (paired with `FnAttribute::NoReturn` in `rustc_codegen_llvm/src/abi.rs:466-468`) | Functions returning `!` carry `noreturn`; executing a backend `ret` instruction is UB, so trap + `unreachable` maintains the `noreturn` contract. |
| `TerminatorKind::Call` with `target: None` | Emits call followed by `bx.unreachable()` | `block.rs:328-330` | MIR building sets `target: None` when the callee diverges or returns an uninhabited type. |

---

### 7. Complete Theorem Inventory (`support/track3_ssa_mem2reg_niche_probe.lean`)

`Basis: execution`

All 24 theorems in
[`support/track3_ssa_mem2reg_niche_probe.lean`](support/track3_ssa_mem2reg_niche_probe.lean)
(1,494 lines, SHA-256
`b412ca6b6603b08ebfb50e63aa7d184af4b3ee7b4fb0e23e1dcf3cd95e3f0565`) elaborate
under Lean `v4.34.1` (`lean -j1 -M1024`) with exit code `0`, zero `sorryAx`, and
zero `Lean.ofReduceBool`:

| Section | Theorem Name | Lines | Formal Statement Summary | Axiom Footprint (`#print axioms`) |
| :--- | :--- | :--- | :--- | :--- |
| 0 | `Compiles.id` | 114–117 | Reflexivity of `Compiles L L id p p` | `(none)` |
| 0 | `Compiles.trans` | 119–129 | Vertical composition `Compiles L1 L3 (π12 ∘ π23) p1 p3` under `Monotone π12` | `(none)` |
| 0 | `runSteps_reaches` | 217–232 | Fuel evaluator `runSteps m n s` satisfies relational `ReachesPrefix m n s` | `(none)` |
| 1 | `envGet_envSet_self` | 274–276 | `envGet (envSet env x v) x = v` | `(none)` |
| 1 | `envGet_envSet_ne` | 278–281 | `x ≠ y → envGet (envSet env y v) x = envGet env x` | `[propext]` |
| 1 | `mapPrefixOutcome_mono` | 517–522 | Monotonicity of `mapPrefixOutcome f` | `(none)` |
| 1 | `mapExecOut_mono` | 524–532 | Monotonicity of `mapExecOut f` | `(none)` |
| 1 | `π_ssa_monotone` | 534–538 | `Monotone (π_ssa locals blockMap)` | `[propext]` |
| 1 | `checkExpr_sound` | 663–688 | `FrameInv` + `checkExpr = true` implies `evalSSAExpr = evalMirExpr` | `[propext, Quot.sound]` |
| 1 | `checkStmt_assign_promoted_sound` | 695–729 | Promoted `assign` / `letBind` preserves `FrameInv` under `FreshForMap` | `[propext, Classical.choice, Quot.sound]` |
| 1 | `checkStmt_writeRef_unpromoted_sound` | 731–756 | Unpromoted indirect store `writeRef` preserves `FrameInv` | `[propext, Classical.choice, Quot.sound]` |
| 1 | `checkStmt_assign_unpromoted_sound` | 758–783 | Unpromoted `assign` / `storeMem` preserves `FrameInv` | `[propext, Classical.choice, Quot.sound]` |
| 1 | `checkStmt_sound` | 791–835 | Single-step statement validation preserves `FrameInv` | `[propext, Classical.choice, Quot.sound]` |
| 1 | `checkStmts_sound` | 852–870 | Multi-statement block validation preserves `FrameInv` across `stmtsM`/`stmtsS` | `[propext, Classical.choice, Quot.sound]` |
| 1 | `diamond_mem2reg_validated` | 957–959 | `checkAllBlocks` validates the 4-block diamond CFG in linear time | `[propext]` |
| 1 | `diamond_true_branch_equiv` | 963–971 | Exact terminal agreement (`115`) on the diamond true branch | `[propext]` |
| 1 | `diamond_false_branch_equiv` | 973–981 | Exact terminal agreement (`225`) on the diamond false branch | `[propext]` |
| 1 | `diamond_all_steps_exact_simulation` | 986–999 | Exact projected state equality across all steps `f ∈ [0, 1, 2, 3]` on both branches | `[propext]` |
| 1 | `validator_rejects_illegal_promotion` | 1037–1039 | `checkAllBlocks` rejects promoting address-taken local `3` (`= false`) | `[propext]` |
| 1 | `illegal_promotion_refutes_compiles` | 1043–1049 | Promoting address-taken local `3` refutes `Compiles` | `[propext]` |
| 2 | `freeze_copy_prop_sound` | 1092–1110 | Coherent `freezeByte` preserves exact evaluation across copy propagation / CSE | `[propext, Quot.sound]` |
| 2 | `freeze_self_eq_and_sub_zero` | 1115–1121 | After `freezeByte`, `x == x = 1#8` and `x - x = 0#8` for all `ByteVal` | `[propext]` |
| 2 | `multi_undef_refutes_compiles` | 1152–1157 | Multi-valued `undef` promotion refutes `Compiles` under CSE | `(none)` |
| 3 | `bitvec_add_sub_cancel` | 1186–1193 | `∀ {w} (a b : BitVec w), (a + b) - a = b` | `[propext, Quot.sound]` |
| 3 | `decode_encode_niche_tagged` | 1200–1203 | Universal niche round-trip decoding for all bitwidths `w` and `relIdx ≤ᵤ nicheSpan` | `[propext, Quot.sound]` |
| 3 | `decode_encode_niche_untagged` | 1210–1213 | Universal decoding to `untaggedVariant` for all payloads outside the niche range | `[propext]` |
| 3 | `optNonZeroU8_exhaustive_correct` | 1224–1227 | Exhaustive 256-value verification of `Option<NonZeroU8>` | `[propext, Quot.sound]` |
| 3 | `wrappingNiche8_verified` | 1241–1250 | Exhaustive verification of 4-variant wrapping niche `[254, 255, 0, 1]` mod 256 | `[propext, Quot.sound]` |
| 3 | `premature_payload_range_unsound` | 1269–1275 | Attaching payload `!nonnull` / `!range` before niche decoding refutes `Compiles` | `(none)` |
| 4 | `zst_elision_compiles` | 1327–1335 | ZST load elision refines `MirPlaceReadLang` for all `typeSize : Nat` | `[propext]` |
| 4 | `naive_zst_load_refutes_compiles` | 1341–1346 | Emitting a 1-byte load for `ZST` on `NonNull::dangling()` refutes `Compiles` | `(none)` |
| 4B | `retag_eligibility_classification` | 1391–1397 | Exact classification of `noalias`/retag eligibility across `Unpin` and `Freeze` | `[propext]` |

## Boundaries

- **Trusted (`trusted/`) vs. Theory (`theory/`) Placement in Anneal:**
  - Updating `Rvalue.use` in `trusted/lean/Trusted/MirAst.lean` (and its
    serializer in `trusted/rustc-capture/`) to carry `withRetag : Bool` in place
    of `StatementKind.retag` belongs **inside `trusted/`**, because it defines
    the source MIR AST and operational semantics gated by `Trusted.CrateTheorem`
    .
  - The `AnSSA` intermediate representation, `checkMem2Reg`, `SROA`, niche
    discriminant lowering, and their `Compiles` refinement proofs belong
    **outside `trusted/` (`theory/`)**, composed via `Compiles.trans` and
    `π_ssa_monotone`.
- **Known Not to Apply (Multi-Valued `undef` and Unwrapped Niche Range
  Checks):**
  - Promoting `MaybeUninit<T>` (`Scalar::Union`) or uninitialized struct padding
    to multi-valued `undef` SSA registers is **known not to apply** (refuted by
    `multi_undef_refutes_compiles`).
  - Decoding `TagEncoding::Niche` via non-wrapping interval comparisons
    `nicheStart ≤ᵤ tag ∧ tag ≤ᵤ nicheEnd` or after attaching payload `!range` /
    `!nonnull` metadata is **known not to apply** (refuted by
    `wrappingNiche8_verified` and `premature_payload_range_unsound`).
- **Not Examined in This Package (Covered in Companion Reports):**
  - Unwinding landing pads (`UnwindAction::Cleanup`) are **not examined** in
    [`support/track3_ssa_mem2reg_niche_probe.lean`](support/track3_ssa_mem2reg_niche_probe.lean)
    ,
    which targets `-Cpanic=abort` `Runtime(PostCleanup)` MIR.
  - Sub-word niche extraction in `BackendRepr::ScalarPair`, operational borrow
    tracking for `AnSSAStmt.retag`, and Tree Borrows `noalias`/`readonly`/
    `writable` relational simulation are mechanized in the three companion
    Round 2 reports cited under **Applicability**.

## Evidence

1. **Preserved Lean `v4.34.1` Mechanization Probe:**
   - Artifact:
     [`support/track3_ssa_mem2reg_niche_probe.lean`](support/track3_ssa_mem2reg_niche_probe.lean)
   - SHA-256: `b412ca6b6603b08ebfb50e63aa7d184af4b3ee7b4fb0e23e1dcf3cd95e3f0565`
   - Toolchain: `leanprover/lean4` `v4.34.1` (commit
     `5045d0056413266e57c625dcd7c365b10e377c52`)
   - Invocation: `lean -j1 -M1024 support/track3_ssa_mem2reg_niche_probe.lean`
     (exit code `0`, zero warnings, 22 `#guard_msgs in #print axioms` checks
     confirming zero `sorryAx` and zero `Lean.ofReduceBool`).
2. **Anneal Repository Sources (`joshlf/anneal` at
   `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`):**
   - `trusted/lean/Trusted/MirAst.lean:1-355` (`Place`, `PlaceElem`, `Operand`,
     `Rvalue`, `StatementKind`, `TerminatorKind`, `BasicBlockData`, `Body`).
   - `trusted/lean/Trusted/MirSemantics.lean:1-125` (`State`, `initMir`,
     `stepMir`, `mirMachine`, `EvalMir`).
   - `trusted/lean/Trusted/Memory.lean:1-85` (`AllocId`, `Provenance`,
     `Pointer`, `AbstractByte`, `Allocation`, `Memory`).
   - `trusted/lean/Trusted/Refinement.lean:1-177` (`Preorder`, `Partial`,
     `Monotone`, `Language`, `Compiles`, `Compiles.id`, `Compiles.trans`).
   - `trusted/lean/Trusted/StepResult.lean:1-147` (`SmallStepMachine`,
     `StepResult`, `ExecQuery`, `PrefixOutcome`, `ExecOut`, `ReachesPrefix`,
     `BehaviorOf`).
3. **Rust Compiler Sources (`rust-lang/rust` at
   `8006091eb71ae7d9e9bccb66c6122c9d68af4466` and PR `#154341` at
   `e402c1edf047a23b0cfef40c6097d1caa294050b`):**
   - `compiler/rustc_mir_transform/src/sroa.rs:1-432` (`escaping_locals`,
     `compute_flattening`, `ReplacementVisitor`, and `WithRetag` threading on
     flattened field copies).
   - `compiler/rustc_mir_transform/src/ssa.rs:1-455` (`SsaLocals`,
     `DominanceFrontier`, `DirectAssignment` / `AddressTaken` classification).
   - `compiler/rustc_middle/src/mir/syntax.rs:497-511, 1359-1360` (`WithRetag`
     and `Rvalue::Use(Operand, WithRetag)` introduced in PR `#154341`).
   - `compiler/rustc_abi/src/lib.rs:350-650, 1575-2150` (`Scalar::Initialized`
     vs. `Scalar::Union`, `is_uninit_valid`, `BackendRepr`, `Variants`,
     `TagEncoding::Direct` vs. `TagEncoding::Niche`).
   - `compiler/rustc_codegen_ssa/src/mir/analyze.rs:1-268` (`non_ssa_locals` and
     `LocalKind::{ZST, SSA, Memory}`).
   - `compiler/rustc_codegen_ssa/src/mir/operand.rs:1-1160` (`OperandValue`,
     `Scalar::Union` `const_undef` handling, `codegen_get_discr` for
     `TagEncoding::Niche`, and ZST load/store elision).
   - `compiler/rustc_codegen_ssa/src/mir/place.rs:1-520` (`project_field`,
     `codegen_set_discr`, uninhabited variant traps, and niche tag encoding).
   - `compiler/rustc_codegen_ssa/src/mir/rvalue.rs:1-1150` (`Rvalue::Use` with
     `WithRetag`, `Rvalue::Aggregate` uninhabited trap, and `BinOp::Offset` ZST
     short-circuiting).
   - `compiler/rustc_codegen_ssa/src/mir/block.rs:280-610`
     (`TerminatorKind::Call`
     and `TerminatorKind::Return` uninhabited trap + `unreachable`).
   - `compiler/rustc_codegen_ssa/src/mir/retag.rs:1-263` (`RetagVisitor`,
     `UnsafePinned` and `MaybeDangling` exemptions).
   - `compiler/rustc_codegen_cranelift/src/discriminant.rs:1-217`
     (`codegen_set_discriminant` and `codegen_get_discriminant` for
     `TagEncoding::Niche`).
   - `compiler/rustc_codegen_llvm/src/builder.rs:735-795` and
     `compiler/rustc_ty_utils/src/abi.rs:315-430` (`!noundef` / `NoUndef`
     gating on `!scalar.is_uninit_valid()` and `PointerKind` `NoAlias` /
     `NoFree` / `ReadOnly` conditions).
4. **Cranelift and Lean 4 Sources:**
   - `bytecodealliance/wasmtime` at `87282b8fd77fa9fbba6caadb0be690bedec2dc64`:
     `cranelift/frontend/src/ssa.rs:1-658` (`SSABuilder`, `Sealed::No/Yes`,
     `append_block_param`, `append_argument`, `use_var_nonlocal`, `seal_block`).
   - `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`
     (`v4.34.1`):
     `src/Lean/Compiler/LCNF/{Basic.lean:180-360, Check.lean:95-190, JoinPoints.lean:1-260, CSE.lean:1-210, SimpCase.lean:1-180}`
     .

## Revalidation

1. **Re-run the Standalone Lean `v4.34.1` Probe:**
   From this report package directory, run:
   ```console
   lean -j1 -M1024 support/track3_ssa_mem2reg_niche_probe.lean
   ```
   A passing check exits with status `0` and produces no output, confirming that
   all 24 theorems and 22 `#guard_msgs in #print axioms` assertions hold without
   `sorryAx` or `Lean.ofReduceBool`.
2. **Check Upstream `rustc` MIR and ABI Drift:**
   When updating the pinned `rust-lang/rust` revision, diff:
   - `compiler/rustc_middle/src/mir/syntax.rs` and
     `compiler/rustc_mir_transform/src/sroa.rs` for changes to `Rvalue::Use`,
     `WithRetag`, or `SROA` flattening eligibility;
   - `compiler/rustc_abi/src/lib.rs` and
     `compiler/rustc_codegen_ssa/src/mir/operand.rs` for changes to
     `Scalar::Union`, `TagEncoding::Niche`, or `codegen_get_discr`; and
   - `compiler/rustc_ty_utils/src/abi.rs` and
     `compiler/rustc_codegen_ssa/src/mir/retag.rs` for changes to `PointerKind`
     `NoAlias`/`ReadOnly`/`NoFree` and `RetagVisitor` exemptions.
