# Variable-Step Compiler Refinement (`π_opt`, `π_progress K`, `π_elastic`) and Stateful Peephole Passes in Anneal

## Summary

In `joshlf/anneal@4f45f0a391a921ced9c9dc773b9a040dbc215d14` (`mir-to-x86`),
`Trusted/StepResult.lean` and `Trusted/Refinement.lean` index program behaviors
by explicit fuel queries `q : ExecQuery State` (`q.steps : Nat`) and pair each
prefix outcome with a per-step observation list `out.trace : List Unit`. Our
mechanizations in `support/VariableStepCompilesProbe.lean` (2,696 lines, 0
`sorry`) and `support/StatefulVariableStepProbe.lean` (3,362 lines, 980
declarations, 271 theorems, 0 `sorry`) establish five results for verifying
variable-step-count compiler optimizations with **zero modifications to
`trusted/`**:

1. **Exact `ReachesPrefix` Horizon Characterization and Dual Lockstep Obstructions:**
   For any deterministic `Obs = Unit` machine (`detMachine evalStep`) whose
   execution from `s₀` takes $k$ `.step ()` transitions $s_0 \to \dots \to s_k$
   followed by `.terminated term` (`StepsToTerminated evalStep p k s₀ term`),
   `ReachesPrefix` has two exact regimes across all `steps : Nat`:
   - **Pre-termination ($\text{steps} \le k$, `reachesPrefix_iff_of_steps_le`):**
     `tr = List.replicate steps () ∧ out = .running`.
   - **Post-termination ($\text{steps} \ge k + 1$, `reachesPrefix_iff_of_steps_gt`):**
     `tr = List.replicate k () ∧ out = .terminated term`, uniformly for all
     $\text{steps} \ge k + 1$ because `ReachesPrefix.terminated` has an
     unconstrained fuel index `n + 1` (**Terminal Stabilization Law**,
     `reachesPrefix_add_of_terminated`).
   Whenever a compiler pass changes the step count from $k_1$ to $k_2 \neq k_1$,
   lockstep and query-reindexing morphisms fail for two independent reasons:
   (a) at $q.\text{steps} = \min(k_1, k_2) + 1$, one program is `.terminated`
   while the other is `.running` (`not_compiles_lockstep_progWithNop_progWithoutNop`),
   and (b) even for $q.\text{steps} > \max(k_1, k_2)$ where both have stabilized
   at `.terminated term`, their traces `List.replicate k₁ ()` and
   `List.replicate k₂ ()` have distinct lengths, refuting every trace-preserving
   query reindexing `q ↦ f(q)` (`not_compiles_any_trace_preserving_query_map`).
2. **Termination Preservation via `π_opt` and `π_progress K` vs. Unconstrained `π_elastic`:**
   Because `Compiler.π : L₁.Behavior → L₂.Behavior` in `Trusted/Refinement.lean`
   transforms behaviors (`Query → SpecPoint Out`) rather than queries, step-count
   and `List Unit` length abstraction belong in `theory/` via behavior
   morphisms:
   - Unconstrained `π_elastic` ($\exists n_1\ tr_1$) preserves all partial
     correctness specifications (`SpecOn`), but allows a buggy pass to replace a
     terminating program with a silent infinite loop (`bb0: jmp bb0`), because
     `.running` at any target fuel $q_2.\text{steps}$ matches the source
     program's $n_1 = 0$ prefix (`ReachesPrefix.zero`).
   - Constraining the source witness fuel by $q_2.\text{steps} \le n_1$
     (`π_opt = π_progress 1`) or $q_2.\text{steps} \le K \cdot n_1 + (K - 1)$
     (`π_progress K`, $K \ge 1$) **provably forbids introducing infinite loops**
     (`not_compiles_π_opt_infinite_loop`) while supporting arbitrary instruction
     deletion ($K = 1$, using terminal stabilization after target termination)
     and 1-to-$K$ instruction expansion ($n_1 \ge \lfloor q_2.\text{steps} / K
     \rfloor$). Moreover, `π_progress` composes multiplicatively
     (`π_progress_comp`: $\pi_{\text{progress}}\ K_2 \circ \pi_{\text{progress}}\
     K_1 \le \pi_{\text{progress}}\ (K_2 \cdot K_1)$), and `π_opt` is idempotent
     (`π_x86_opt_idem`).
3. **Fixed-Point Preservation of All `Trusted/X86Semantics.lean` Specifications:**
   Every specification constructor in `Trusted/X86Semantics.lean`
   (`WellFormedOn`, `WellFormed`, `EnsuresRetLibInv`, `EnsuresEqArg`,
   `EnsuresConst`, `EnsuresBinOp`) is an instance of `SpecOn body P Q`, whose
   `.defined` predicate depends only on `q.init` and whose `.val` predicate
   depends only on `q.init` and `out.outcome`. We prove
   `π_elastic (SpecOn body P Q) ≤ SpecOn body P Q` (`π_elastic_specOn_le`), so any
   pass verified with `Compiles X86Lang X86Lang π_x86_opt body (opt body)` (or
   `π_progress K` / `π_x86_elastic`) automatically transfers
   `AssemblerCompiler.Verified body spec` to `AssemblerCompiler.Verified (opt
   body) spec` (`verified_of_compiles_elastic`).
4. **Block-Suffix (`blk.instrs.drop s.ip`) Simulation for Stateless and Stateful Variable-Step Passes:**
   Stating the simulation relation on instruction suffixes `(passBlock
   blk).instrs.drop s_tgt.ip = passInstrs (blk.instrs.drop s_src.ip)` eliminates
   all instruction-pointer (`s.ip`) index arithmetic across branches, loops, and
   function calls. Using this pattern, `VariableStepCompilesProbe.lean` proves
   universal correctness for instruction deletion (`stripNops_compiles_opt`,
   $K = 1$), 1-to-2 instruction expansion (`expandImmMov_compiles_progress`,
   $K = 2$), and their composition (`stripNops_then_expandImmMov_compiles_progress`).
5. **Zero-`funext` Extensional Memory Congruence (`MemExtEq` / `MemAgreesExcept`) and Multi-Pass Stateful Peephole Pipeline:**
   In `StatefulVariableStepProbe.lean`, we prove without `funext` that
   `Trusted/X86Semantics.lean` respects pointwise memory equality (`MemExtEq m₁
   m₂ : ∀ i, m₁ i = m₂ i`) and that two memories diverging on a dead slot
   (`MemAgreesExcept d m₁ m₂ : ∀ i ≠ d, m₁ i = m₂ i`) reconverge to full
   `MemExtEq` upon executing `.deallocSlot d`
   (`memExtEq_of_memAgreesExcept_updateSlot`). This powers universal `Compiles
   X86Lang X86Lang π_x86_opt` proofs for:
   - **Pass 1 (`elimDeadStoreDealloc`):** `.mov tmp (.imm v) :: .deallocSlot d ::
     rest` $\mapsto$ `.deallocSlot d :: rest` when `tmp.index == d.index` (2-to-1
     compression).
   - **Pass 2 (`fuseScratchMov`):** `.mov tmp (.imm v) :: .mov dst (.stackSlot s
     consume) :: .deallocSlot d :: rest` $\mapsto$ `.mov dst (.imm v) ::
     .deallocSlot d :: rest` when `tmp.index == s.index && tmp.index == d.index
     && !(dst.index == d.index)` (3-to-2 compression via a two-phase
     `SimPass ∨ SimPendingDealloc` simulation).
   - **Pass 3 (`optPipeline`):** The composed 3-pass pipeline `stripNops ∘
     elimDeadStoreDealloc ∘ fuseScratchMov` (`optPipeline_compiles_opt`).

## Applicability

These findings apply to:

- **Anneal (`joshlf/anneal`):** Commit
  `4f45f0a391a921ced9c9dc773b9a040dbc215d14` (`mir-to-x86`), specifically
  `trusted/lean/Trusted/StepResult.lean` (`StepResult`, `PrefixOutcome`,
  `ExecQuery`, `PrefixOutput`, `Machine`, `ReachesPrefix`, `ExecSem`),
  `trusted/lean/Trusted/Refinement.lean` (`SpecPoint`, `Language`, `Compiler`,
  `Compiles`), `trusted/lean/Trusted/X86Ast.lean`,
  `trusted/lean/Trusted/X86Semantics.lean`, and
  `theory/Anneal/Compiler/Peephole.lean`.
- **Lean 4 (`leanprover/lean4`):** Version `v4.34.1` at commit
  `5045d0056413266e57c625dcd7c365b10e377c52` (`prelude`-only mode with `import
  Init.NotationExtra`).

## Findings

### 1. Exact `ReachesPrefix` Horizon Laws and Why Lockstep Morphisms Fail When $k_1 \neq k_2$

In `Trusted/StepResult.lean:68-89`, `ReachesPrefix` has four constructors:
`zero` (at `steps = 0`, emitting `[]` and `.running`), `terminated n s term` (at
`steps = n + 1`, emitting `[]` and `.terminated term`), `failed n s err` (at
`steps = n + 1`, emitting `[]` and `.failed err`), and `step n s s' obs tr out`
(prepending `obs` to `tr` and incrementing fuel from `n` to `n + 1`).

Because `terminated` and `failed` carry an arbitrary `n : Nat` in their fuel
index `n + 1`, any terminal or failed execution prefix remains valid at all
larger fuel budgets (**Terminal Stabilization Law**,
`reachesPrefix_add_of_terminated` and `reachesPrefix_add_of_failed` in
`support/VariableStepCompilesProbe.lean:380-415`):
$$\text{ReachesPrefix } M\ p\ \text{init}\ n\ s\ tr\ (\text{.terminated } t) \implies \text{ReachesPrefix } M\ p\ \text{init}\ (n + d)\ s\ tr\ (\text{.terminated } t)$$

For a deterministic `Obs = Unit` machine (`detMachine evalStep`) where `s₀`
steps $k$ times via `.step ()` to `s_k` and then steps to `.terminated term`:

- For all $\text{steps} \le k$ (`reachesPrefix_iff_of_steps_le`):
  $$\text{ReachesPrefix } M\ p\ \text{init}\ \text{steps}\ s_0\ tr\ \text{out} \iff tr = \text{List.replicate steps } () \land \text{out} = \text{.running}$$
- For all $\text{steps} \ge k + 1$ (`reachesPrefix_iff_of_steps_gt`):
  $$\text{ReachesPrefix } M\ p\ \text{init}\ \text{steps}\ s_0\ tr\ \text{out} \iff tr = \text{List.replicate } k\ () \land \text{out} = \text{.terminated term}$$

On `progWithNop` ($k_1 = 2$ steps: `.nop`, `.mov r0 42`, `.ret`) and
`progWithoutNop` ($k_2 = 1$ step: `.mov r0 42`, `.ret`),
`not_compiles_lockstep_progWithNop_progWithoutNop` and
`not_compiles_any_trace_preserving_query_map` prove that:

1. Under `π = id` at $q.\text{steps} = 2$, `progWithoutNop` emits `.terminated
   (.normal (.word64 42))` while `progWithNop` emits only `.running`.
2. Under **any** trace-preserving query map `f : ExecQuery X86State → ExecQuery
   X86State` at $q.\text{steps} = 2$, `progWithoutNop` produces `out = ⟨[()],
   .terminated (.normal (.word64 42))⟩`, which never belongs to
   `(X86Sem progWithNop (f q)).val` for any `f q` because `progWithNop` only
   ever pairs `.terminated` with `[(), ()]` (length 2).
3. In `progBranchWithNops` (`bb0` branches on `arg₀ : Bool` to `bb1` with two
   `.nop`s or `bb2` with zero `.nop`s), the step count changes by 2 when `arg₀ =
   true` and by 0 when `arg₀ = false`, so no state-independent step reindexing
   can align both branches.

Basis: **source** (`Trusted/StepResult.lean`, `Trusted/Refinement.lean`) +
**execution** (`support/VariableStepCompilesProbe.lean` Sections 1–4).

### 2. Hierarchy of Step-Abstracting Behavior Morphisms (`π_opt`, `π_progress K`, `π_elastic`)

In `support/VariableStepCompilesProbe.lean` (Sections 5–7), we define three
monotone behavior morphisms in `theory/`:

```lean
def π_elastic (decompileInit : State₂ → State₁)
    (decompileOutcome : PrefixOutcome Term₂ Err₂ → PrefixOutcome Term₁ Err₁)
    (b : ExecBehavior State₁ Unit Term₁ Err₁) :
    ExecBehavior State₂ Unit Term₂ Err₂ :=
  fun q₂ =>
    { defined := ∀ n₁ : Nat, (b ⟨decompileInit q₂.init, n₁⟩).defined
      val := fun out₂ =>
        ∃ (n₁ : Nat) (tr₁ : List Unit),
          (b ⟨decompileInit q₂.init, n₁⟩).val
            ⟨tr₁, decompileOutcome out₂.outcome⟩ }

def π_progress (K : Nat) (decompileInit : State₂ → State₁)
    (decompileOutcome : PrefixOutcome Term₂ Err₂ → PrefixOutcome Term₁ Err₁)
    (b : ExecBehavior State₁ Unit Term₁ Err₁) :
    ExecBehavior State₂ Unit Term₂ Err₂ :=
  fun q₂ =>
    { defined := ∀ n₁ : Nat, (b ⟨decompileInit q₂.init, n₁⟩).defined
      val := fun out₂ =>
        ∃ (n₁ : Nat) (tr₁ : List Unit),
          q₂.steps ≤ K * n₁ + (K - 1) ∧
          (b ⟨decompileInit q₂.init, n₁⟩).val
            ⟨tr₁, decompileOutcome out₂.outcome⟩ }

def π_opt := π_progress 1
```

| Morphism | Witness Fuel Constraint | Preserves `SpecOn` (`WellFormed`, `Ensures*`)? | Prevents Introducing Silent Infinite Loops? | Supported Variable-Step Passes |
| :--- | :--- | :---: | :---: | :--- |
| **`id` (Lockstep)** | $n_1 = q_2.\text{steps}$ and $tr_1 = tr_2$ | Yes | Yes | 1-to-1 instruction rewrites (`simplifyAddZero`) |
| **`π_opt` (`π_progress 1`)** | $q_2.\text{steps} \le n_1$ | Yes | **Yes** (`not_compiles_π_opt_infinite_loop`) | Arbitrary instruction deletion & many-to-1 fusion (`stripNops`, `elimDeadStoreDealloc`, `fuseScratchMov`) |
| **`π_progress K` ($K \ge 1$)** | $q_2.\text{steps} \le K \cdot n_1 + (K - 1)$ | Yes | **Yes** (`not_compiles_π_progress_infinite_loop`) | Deletion + up to 1-to-$K$ instruction expansion (`expandImmMov` with $K = 2$) |
| **`π_elastic`** | Unconstrained $n_1 : \text{Nat}$ | Yes (`π_elastic_specOn_le`) | **No** ($n_1 = 0$ matches `.running` forever) | Arbitrary step rescaling when only partial correctness / safety (`SpecOn`) is required |

Why does `π_opt` ($q_2.\text{steps} \le n_1$) handle instruction **deletion**
when the optimized target program takes *fewer* steps to terminate than the
source program?

- While the target program is still stepping (after $m$ target steps that
  skipped $d$ deleted source instructions), the source program has taken $m + d
  \ge m$ steps, so choosing $n_1 = q_2.\text{steps} + d \ge q_2.\text{steps}$
  matches `.running`.
- Once the target program terminates at step $k_{\text{tgt}}$ and is queried at
  any $q_2.\text{steps} = k_{\text{tgt}} + 1 + r$, the source program terminates
  at step $k_{\text{src}} = k_{\text{tgt}} + d_{\text{total}}$, and by the
  **Terminal Stabilization Law** (`reachesPrefix_add_of_terminated`), the source
  program *also* produces `.terminated term` at fuel $n_1 = q_2.\text{steps} +
  d_{\text{total}} \ge q_2.\text{steps}$.
- Conversely, if a buggy pass replaces `progWithoutNop` ($k_1 = 1$) with
  `progInfiniteLoop` (`bb0: jmp bb0`), querying at $q_2.\text{steps} = 2$
  produces `out₂.outcome = .running`, whereas for every $n_1 \ge 2$,
  `progWithoutNop` produces only `.terminated (.normal (.word64 42))`, refuting
  `Compiles` under `π_opt` (`not_compiles_π_opt_infinite_loop`) and under
  `π_progress K` at $q_2.\text{steps} = 2K$
  (`not_compiles_π_progress_infinite_loop`).

Notice also that modifying `ReachesPrefix` in `Trusted/StepResult.lean` to allow
uncounted silent `.tau` steps would violate `non_vacuity_at_every_depth`
(`theory/Anneal/StepResult.lean`), because a silent infinite loop would have an
empty prefix set (`False`) for all $n \ge 1$ and vacuously refine every
specification. Keeping `Trusted/StepResult.lean` unchanged and placing `π_opt`
and `π_progress K` in `theory/` preserves `non_vacuity_at_every_depth` at every
fuel depth.

Basis: **execution** + **derived** (`support/VariableStepCompilesProbe.lean`
Sections 5–8).

### 3. Block-Suffix Simulation and Stateless + Stateful Variable-Step Passes

Rather than tracking numerical instruction-pointer offsets $i_{\text{src}} \mapsto
i_{\text{tgt}}$ across deleted or expanded instructions, our **Block-Suffix
Simulation Pattern** relates source and target states via the remaining
instruction list `(passBlock blk).instrs.drop s_tgt.ip = passInstrs
(blk.instrs.drop s_src.ip)`, founded on four generic list lemmas (`drop_zero`,
`getElem?_eq_head_drop`, `drop_add_one_of_drop_eq_cons`, and
`getElem?_eq_none_of_drop_nil`). When $s_{\text{src}}.\text{ip} = 0$ and
$s_{\text{tgt}}.\text{ip} = 0$ (at function entry, branch targets, and call/return
boundaries), `.drop 0` reduces definitionally (`rfl`), making control-flow
transitions immediate.

In `support/StatefulVariableStepProbe.lean`, we extend this pattern to
**stateful** peephole passes where intermediate source and target memories
differ on dead temporary slots:

1. **Zero-`funext` Extensional Memory Congruence (`MemExtEq` and `MemAgreesExcept`):**
   - `MemExtEq m₁ m₂ : Prop := ∀ i, m₁ i = m₂ i`
   - `MemAgreesExcept deadSlot m₁ m₂ : Prop := ∀ i, i ≠ deadSlot → m₁ i = m₂ i`
   - `memExtEq_of_memAgreesExcept_updateSlot` proves without `funext` that if
     `MemAgreesExcept d m₁ m₂`, then `MemExtEq (updateSlot m₁ d v) (updateSlot m₂
     d v)`. In particular, executing `.deallocSlot d` (`updateSlot _ d none`) in
     both machines erases the divergence on `d` and restores full `MemExtEq`.
2. **Pass 1 — Dead Store + Dealloc Elimination (`elimDeadStoreDealloc`):**
   Rewrites `.mov tmp (.imm v) :: .deallocSlot d :: rest` (when `tmp.index ==
   d.index`) to `.deallocSlot d :: elimDeadStoreDeallocInstrs rest`. In one
   target step (`.deallocSlot d`), the source executes two steps (`.mov tmp (.imm
   v)` producing `MemAgreesExcept d.index`, followed immediately by
   `.deallocSlot d` reconverging to `MemExtEq`), establishing:
   ```lean
   theorem elimDeadStoreDealloc_compiles_opt (body : X86Body) :
       Compiles X86Lang X86Lang π_x86_opt body (elimDeadStoreDealloc body)
   ```
3. **Pass 2 — Scratch-Register Move Fusion (`fuseScratchMov`):**
   Rewrites `.mov tmp (.imm v) :: .mov dst (.stackSlot s consume) :: .deallocSlot
   d :: rest` (when `tmp.index == s.index && tmp.index == d.index && !(dst.index
   == d.index)`) to `.mov dst (.imm v) :: .deallocSlot d :: fuseScratchMovInstrs
   rest`. Because the 3-to-2 compression leaves `.deallocSlot d` as a second
   target instruction, the simulation invariant is a two-phase disjunction
   `SimFuse root s_tgt s_src := SimPass fuseScratchMovInstrs root s_tgt s_src ∨
   SimPendingDealloc root s_tgt s_src`:
   - **Phase 1 (`stepSim_fuseScratchMov_enter_pending`):** 1 target step (`.mov
     dst (.imm v)`) matches 2 source steps (`.mov tmp (.imm v)` then `.mov dst
     (.stackSlot s consume)`), entering `SimPendingDealloc` with
     `MemAgreesExcept d.index`.
   - **Phase 2 (`stepSim_fuseScratchMov_exit_pending`):** 1 target step
     (`.deallocSlot d`) matches 1 source step (`.deallocSlot d`), reconverging
     to `SimPass` with `MemExtEq`.
4. **Composed 3-Pass Pipeline (`optPipeline`):**
   Composing `fuseScratchMov`, `elimDeadStoreDealloc`, and `stripNops` via
   `compiles_opt_trans` yields `optPipeline_compiles_opt`, verified end-to-end on
   `stage0Body` (`stage0Body_optPipeline_verified`).

Basis: **execution** (`support/VariableStepCompilesProbe.lean` Sections 9–12,
`support/StatefulVariableStepProbe.lean` Sections 1–5,
`support/AuditCheck.lean`).

## Boundaries

- **Known not to apply:** Unconstrained `π_elastic` does not preserve liveness or
  termination; passes that must forbid introducing silent infinite loops must use
  `π_opt` (`q₂.steps ≤ n₁`) or `π_progress K` (`q₂.steps ≤ K * n₁ + (K - 1)`).
- **Known not to apply:** A pass that deletes **all** instructions inside a
  zero-instruction cycle (`bb_loop: .nop; jmp bb_loop` $\mapsto$ `bb_loop: jmp
  bb_loop`) still steps once per `jmp` terminator in `X86Semantics.lean`
  (because `evalX86Term` is a separate step from `evalX86Instr`), so every loop
  iteration in `X86Body` executes at least 1 terminator step and cannot create a
  0-step target loop.
- **Not examined:** Inter-block control-flow restructuring passes (such as
  basic-block merging or loop unrolling) that alter basic-block indices `bb`
  rather than instruction lists within each basic block.

## Evidence

- **Anneal `mir-to-x86` prototype (`joshlf/anneal@4f45f0a391a921ced9c9dc773b9a040dbc215d14`):**
  - `trusted/lean/Trusted/StepResult.lean:1-106` (`StepResult`, `PrefixOutcome`, `ReachesPrefix`, `ExecSem`).
  - `trusted/lean/Trusted/Refinement.lean:1-95` (`SpecPoint`, `Language`, `Compiler`, `Compiles`).
  - `trusted/lean/Trusted/X86Semantics.lean:1-290` (`evalX86Instr`, `evalX86Term`, `evalX86Step`, `WellFormedOn`, `Ensures*`).
  - `theory/Anneal/Compiler/Peephole.lean:1-93` (`simplifyAddZero`).
- **Preserved package artifacts (`reports/anneal-mir-to-x86-variable-step-refinement-and-stateful-passes/support/`):**
  - `support/VariableStepCompilesProbe.lean` (`sha256: 1a042c7ccf780bca4939957659df32c5cf75fc5e5424b85a3c6752f03397ba31`, 2,696 lines, 0 `sorry`).
  - `support/StatefulVariableStepProbe.lean` (`sha256: 7823354cc604db33510ffff5f78add2c23449400e0acf1efd3ba3c1f580a6219`, 3,362 lines, 980 declarations, 271 theorems, 0 `sorry`).
  - `support/AuditCheck.lean` (`sha256: 614715c3808e397609f420a1e71aad1695387cb45b3ee3dbb82898a0ed3a4019`, kernel replay in `287 ms`, 0 `isUnsafe || isPartial`, axioms `[Quot.sound, propext]`).

## Revalidation

Run the two standalone `prelude`-only probes and the boundary audit harness with
Lean 4.34.1:

```bash
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  support/VariableStepCompilesProbe.lean
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  -o /tmp/StatefulVariableStepProbe.olean support/StatefulVariableStepProbe.lean
LEAN_PATH=/tmp lean -DElab.async=false -Ddebug.skipKernelTC=false \
  support/AuditCheck.lean
```
