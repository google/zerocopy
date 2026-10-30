# Register Allocation Translation Validation (`regalloc2`), Public/Private Stack Frame Lowering (`Stacking`), Guard-Page Probing, and Quantitative Stack Bounds (`A-BEH-07`)

## Summary

A formally verified MIR-to-ISA backend for Anneal (`joshlf/anneal`) should
verify register allocation by **translation validation** using a repaired
`regalloc2`-style forward symbolic dataflow checker (`checkRegAlloc`), followed
by a verified **`Stacking` pass** that partitions each activation frame into
public address-taken stack data (`fe_stack_data`) and compiler-private spill,
callee-save, and return-address slots (`fe_local`, `fe_ofs_callee_save`,
`fe_ofs_retaddr`) while emitting a quantitative **Frame-Size Certificate**
$\mathcal{S} : \text{FnId} \to \mathbb{N}$ that discharges Anneal behavioral
assumption `A-BEH-07` (finite-stack overflow freedom).

Synthesis of primary sources across `bytecodealliance/regalloc2` (v0.15.2),
`cranelift-codegen` (v0.132.0), `AbsInt/CompCert` (v3.18), Stack-Aware CompCert
(`ssrg-vt/compcert_stack_aware`), `CakeML/cakeml`, `mit-plv/bedrock2`, and
`rust-lang/rust`, paired with two standalone Lean 4.34.1 mechanizations
(`support/track4_regalloc2_stacking_probe.lean`, 2,476 lines; and
`support/round2_track3_probe.lean`, 1,549 lines; zero `sorryAx`, zero
`Lean.ofReduceBool`), establishes seven core results:

1. **Forward symbolic dataflow validation with untrusted `blockIn` certificates
   dominates solver verification and backward equation solving:**
   `regalloc2`'s Ion allocator (`src/ion/`) exceeds 5,500 lines of heuristic
   live-range splitting, coalescing, and priority-queue eviction, whereas its
   symbolic checker (`src/checker.rs`) is ~600 lines. Unlike CakeML's
   `check_clash_tree` (which requires structured ASTs and cannot validate
   live-range splitting without mutating SSA variables) or CompCert's backward
   Kildall solver over `EqSet` (`backend/Allocation.v`), a forward symbolic
   checker executes moves and instructions in their natural operational
   direction. Emitting the converged `blockIn : List CheckerState` vector from
   the untrusted Rust Kildall pass reduces verification inside the Lean 4
   kernel to a single recursion-free $O(B + I)$ linear pass (`checkBlocks` /
   `checkSubRegFunc`, `checkRegAlloc_sound`, also referred to conceptually as
   `checkCFGWithCert_sound`).
2. **Upstream `regalloc2` v0.15.2 `src/checker.rs` contains four soundness gaps
   that must be repaired before serving as a formal verifier:**
   - *Gap 1 (`src/checker.rs:554-562`):* When `CheckerInst::Move { into, from }`
     reads a source allocation `from` that is not currently tracked in `allocs`,
     `get_value(&from)` returns `None` and the `if let Some(val)` guard skips
     updating `into`, leaving stale virtual-register bindings in `into` instead
     of killing `into`.
   - *Gap 2 (`src/checker.rs:491-493`):* In `CheckerState::check`,
     `if has_reused_input && pos == InstPosition::After { return Ok(()); }`
     returns early from the entire operand loop whenever any `Def` reuses an
     input `Use`, skipping `InstPosition::After` checks for all other `Late`
     `Use` operands and `After`-phase constraints on the same instruction.
   - *Gap 3 (`src/checker.rs:505, 596-622`):* `CheckerState::update` applies
     both `Early` and `Late` `Def`s in a single pass after `Before` and before
     `After`, and `check_val` ignores `OperandKind::Def`, failing to catch
     conflicts between non-reused `Early` `Def`s and `Early` `Use`s or silent
     overwrites when two distinct `Def`s on the same instruction are assigned
     the same physical `Allocation`.
   - *Gap 4 (`src/checker.rs:474-478, 753`):* Entry blocks initialize at
     `CheckerState::Top` ($\top$) rather than the exact entry parameter bindings,
     relying on `become_defined()` inside the first `update` call to leave $\top$.
3. **Sub-register family aliasing (`rax`/`eax`/`ax`/`al`) requires width-tagged
   symbolic bindings with family-wide kills (`killAllocFamily`):**
   On x86-64 and AArch64, 8-bit (`w8`) and 16-bit (`w16`) writes merge into the
   64-bit architectural register while 32-bit (`w32`) writes zero-extend (`canary_subreg_partial_write_clobbers_64bit`).
   Tagging symbolic bindings with `width : RegWidth` (`w8 | w16 | w32 | w64`),
   killing all widths of `dst` upon any write (`killAllocFamily`), requiring
   exact width agreement on reads (`hasVRegWidth`), and requiring explicit
   `zext`/`sext` for widening makes `subreg_checkRegAlloc_sound` hold across all
   sub-register widths (`canary_subreg_width_mismatch_rejected`).
4. **Callee-saved register preservation is verifiable inside `checkRegAlloc` via
   read-only entry `VReg` tokens (`calleeSaveToken`):**
   Seeding `blockIn[entry]` with `{ alloc := .preg r, width := .w64, vreg :=
   calleeSaveToken r }` for every `r ∈ calleeSaved`, clobbering `callerSaved` on
   `Call`, and checking `hasVRegWidth stRet (.preg r) .w64 (calleeSaveToken r)`
   at `Return` verifies both standard prologue/epilogue and shrink-wrapped
   callee-save spills/reloads via ordinary `EditMove`s
   (`callee_saved_preserved_of_checkRegAlloc`, `subreg_and_callee_saved_sound`).
5. **CompCert-style `Stacking` with `fe_stack_data` partitioning and a 1-byte
   unexposed guard slot isolates private spills from user pointers and resolves
   `PNVI-ae-udi` one-past-the-end ambiguity:**
   Partitioning each `PartitionedFrameLayout` into a `.public_` region
   `[ofsPublic, ofsPublic + publicBytes)` for address-taken MIR locals and
   `.private_` regions for `regalloc2` spills (`[ofsSpills, ...)`), saved
   callee-saved registers (`[ofsSaved, ...)`), and the return address
   (`[ofsRetAddr, ...)`), separated by `guardBytes ≥ 1` unexposed padding,
   guarantees that in-bounds user stores preserve all private frame state
   (`public_store_preserves_private_spills_and_saved_regs`) and makes closed-interval
   `[base, base + size]` provenance resolution under `PNVI-ae-udi` deterministic
   (`guard_byte_eliminates_pnvi_boundary_ambiguity`).
6. **`-mno-red-zone` and periodic guard-page probing (`__rust_probestack`)
   enforce hardware interrupt and OS page-fault invariants:**
   Placing all frame slots at non-negative offsets $\ge 0$ from `SP`
   (`no_red_zone_writeMachLoc`) guarantees that asynchronous hardware interrupts
   or signals pushing trap frames below `SP` cannot corrupt active frames
   (`interrupt_preserves_active_frames`, also denoted
   `noRedZone_preserves_frame_under_isr` vs. `redZone_corrupted_by_isr`). When
   stack overflow is trapped dynamically via an OS guard page of size
   $P_{\text{guard}} = 4096\text{ B}$, stepping and touching `SP` in increments
   $\le P_{\text{guard}}$ (`probe_step_bounded`, `probestack_prevents_guard_bypass`)
   prevents Stack Clash (CVE-2017-1000364) from jumping across the guard page.
7. **Quantitative stack certificates $\mathcal{S}(f)$ discharge `A-BEH-07`
   across both direct and indirect (`dyn Trait` / `fn`) calls:**
   Direct call chains with $\sum_i \mathcal{S}(f_i) \le \text{StackBudget}$
   never step to `.failed .stackOverflow` (`callChain_no_stackOverflow`). For
   indirect and virtual calls, a hybrid two-tier discipline combines zero-overhead
   static VTable/`FnPtr` contracts (`IndirectCallContract.wcetStack`,
   `indirect_call_static_contract_no_overflow`, conceptually
   `static_stack_bound_discharges_A_BEH_07`) with dynamic prologue `stackLimit`
   checks (`execDynamicPrologueCheck`, `dynamic_stack_check_preserves_limit`,
   conceptually `dynamic_stack_check_discharges_A_BEH_07`) for open plugins and
   unbounded recursion.

## Applicability

These findings govern:

- **Anneal's MIR-to-ISA backend pipeline (`joshlf/anneal` at
  `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`):** Specifically Phase 3 register
  allocation (lowering unbounded virtual registers `VReg` to bounded physical
  registers `PReg` and `SpillSlot`s via `regalloc2` translation validation) and
  `Stacking` (folding address-taken MIR locals, spill slots, and ABI save areas
  into flat `SP`-relative memory accesses while emitting $\mathcal{S}(f)$).
- **Anneal's trusted behavioral boundary (`A-BEH-07`):** Discharging
  quantitative stack-overflow freedom across direct call graphs, `dyn Trait`
  vtable dispatch, and `fn` pointers, and connecting Phase 1/2 provenance memory
  (`AllocId` + byte offset) to Phase 3/4 flat 64-bit address spaces under both
  Strict Provenance and `PNVI-ae-udi`.
- **Target ISAs and ABIs:** x86-64 System V AMD64 (where the 128-byte red zone
  `[RSP - 128, RSP)` must be disabled via `-mno-red-zone` in kernel/interrupt
  contexts and where 8/16/32/64-bit sub-registers alias), AArch64 (`x19`–`x30`
  callee-saved), and RISC-V (`s0`–`s11`, `ra` callee-saved).

The examined upstream subjects in `REPORT.json` relate as follows:
`bytecodealliance/regalloc2` (`969bad6297dfca4db2db4eeefebba6c1ebafcf27` and
v0.15.2 `2fe490bc9dda433f70c54f90f7633ed929f693d9`) and `cranelift-codegen`
(`83166ba31317afbe1574186798f4db17cd641ab4`) provide the concrete Rust register
allocator, parallel-move resolver, symbolic checker, and prologue stack-check
emission audited for soundness gaps; `AbsInt/CompCert`
(`f9573fb9b8ba4b4cecebe1ef3cb8b2ef9ce1fc03` / v3.18
`74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`), Stack-Aware CompCert
(`0518d9ffb69ec11e79a214df1afc0b0159930478`), `CakeML/cakeml`
(`7b9a722a1d88bc65555110fb6731173cd4be9b34` /
`f73189499bb295f0859dec7ee38c169c48da682c`), and `mit-plv/bedrock2`
(`7cbf3ef1be3c4fa6be792371ab0ec79cf773bd7f` /
`757f17c6083bf8d43b5293a0db545c8d0aa32a13`) provide the reference formal
verification architectures compared against `regalloc2`; `rust-lang/rust`
(`8006091eb71ae7d9e9bccb66c6122c9d68af4466` /
`92b5b8c87c61b20adc9001b41baf587634a74734`) provides the `__rust_probestack`
and `StackProbeType` implementation; and the two preserved probes in `support/`
mechanize the repaired models and proofs in Lean `v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`).

## Findings

### 1. Comparative Register-Allocation Verification Matrix

Basis: **source** + **derived**

| Dimension | `regalloc2` (`v0.15.2`) | CompCert (`v3.18`) | CakeML (`word_alloc`) | Bedrock2 (`RegAlloc.v`) |
| :--- | :--- | :--- | :--- | :--- |
| **Primary Files** | `src/checker.rs`, `src/moves.rs`, `src/ion/` | `backend/Allocation.v`, `Allocproof.v`, `Locations.v` | `reg_allocScript.sml`, `word_allocProofScript.sml` | `compiler/src/compiler/RegAlloc.v` |
| **Source $\to$ Target IR** | `Function` (CFG + SSA/non-SSA `VReg`s) $\to$ `Output` (`Allocation` + `Edit::Move`) | `RTL` (`reg`) $\to$ `LTL` (`loc`: `R mreg` $\mid$ `S slot`) | `wordLang` (SSA `num`) $\to$ `wordLang` (physical/stack `num`) | `FlatImp.stmt` (`srcvar`) $\to$ `FlatImp.stmt` (`impvar`) |
| **Verification Strategy** | Forward symbolic dataflow checker (`Checker`) | Backward symbolic Kildall equation validator (`check_function`) | Syntactic clash-tree coloring validator (`check_clash_tree`) | Forward syntax-directed correspondence checker (`check`) |
| **Control-Flow Scope** | Arbitrary multi-block CFG with edge-split moves | Arbitrary multi-block CFG (`RTL` nodes $\to$ `LTL` blocks) | Structured AST (`Seq`, `If`, `MustTerminate`, `Call`) | Structured AST (`SSeq`, `SIf`, `SLoop`) |
| **Symbolic State / Domain** | `Allocation -> Set<VReg>` (or $\top$ at unvisited blocks) | `EqSet`: dual-indexed set of `(reg, loc, equation_kind)` | `domain live : num_set` (cutset of simultaneously live variables) | `mapping : list (srcvar * impvar)` active pairs |
| **Join / Meet Operator** | Forward intersection: $S_1 \cap S_2$ (`CheckerState::meet`) | Backward union: $E_1 \cup E_2$ (`EqSet.union` at CFG splits) | Tree union of live sets; injectivity checked at each node | Forward list intersection (`list_intersect`) + `loop_inv'` |
| **Parallel Move Handling** | Lowered by `MoveResolver` (`src/moves.rs`) into sequential `Edit::Move`s using a scratch slot; verified sequentially | Lowered to sequential `Lop Omove` instructions in `LTL` blocks; verified backward per move | SSA copy-coalescing moves inserted before coloring; no cyclic parallel move resolver in checker | Single variable-to-variable `SCopy`; no parallel moves |
| **Checker Complexity** | $O(B \cdot K \cdot |A|)$ forward Kildall fixpoint ($O(B + I)$ with `blockIn` certificate) | $O(N \cdot |E| \log |E|)$ backward Kildall fixpoint | $O(|V| \log |V|)$ single tree traversal (`lookup_any`) | $O(|S| \cdot |M|^2)$ syntax-directed pass |

1. **Why translation validation beats verifying the heuristic allocator:**
   In `bytecodealliance/regalloc2`, the untrusted Ion allocator
   (`src/ion/mod.rs:341-376`, `src/ion/spill.rs:94-156`, `src/ion/moves.rs`)
   consists of over 5,500 lines of live-range bundle construction, interference
   graph coloring by spill-slot size, and priority-queue eviction, coupled with
   the DFS cycle-breaking parallel-move resolver `MoveResolver::compute_scheduled_moves`
   (`src/moves.rs:84-308`). By contrast, a forward symbolic checker over basic
   blocks and `Edit::Move` sequences is ~200 lines of pure functional Lean code.
2. **Why forward symbolic validation beats CakeML's `check_clash_tree` and
   CompCert's backward `EqSet` Kildall solver for Anneal:**
   - CakeML (`compiler/backend/word_allocScript.sml:353-604`,
     `compiler/backend/reg_alloc/reg_allocScript.sml:34-146`) transforms the
     source `wordLang` AST into strict SSA with explicit copy-coalescing moves
     (`full_ssa_cc_trans`) and checks that a single global color map
     `total_colour oracle` is injective on every live cutset of the syntactic
     `clash_tree` (`check_clash_tree_domain` in
     `reg_allocProofScript.sml:154-230`). Because it validates a single static
     variable-to-color function, `check_clash_tree` cannot validate live-range
     splitting or mid-lifetime `Edit::Move` spills/reloads without mutating the
     source IR.
   - CompCert (`backend/Allocation.v:60-630`, `backend/Allocproof.v:125-145`)
     propagates required equations `(r, Full/Low/High, l) ∈ EqSet` *backward*
     across the CFG using dual-indexed red-black trees (`eqs1` ordered by `reg`,
     `eqs2` ordered by `loc`) and meets successor sets via set union
     (`EqSet.union`). Backward propagation must invert instruction and move
     semantics at every step (`subst_reg`, `subst_loc`), whereas `regalloc2`'s
     forward symbolic tracker executes moves and definitions in their natural
     forward operational order and checks subset inclusion (`subState`) at CFG
     edges.
   - Bedrock2 (`compiler/src/compiler/RegAlloc.v:123-490`) uses a forward
     relational mapping `mapping := list (srcvar * impvar)` with
     `assignment m x x'` (`RegAlloc.v:123-124`) removing old bindings on both
     sides before inserting `(x, x')`—the exact update discipline generalized to
     multi-block CFGs, `EditMove`s, and sub-registers in our Lean probes.

### 2. Four Soundness Gaps in `regalloc2` v0.15.2 `src/checker.rs` and the Repaired Validator

Basis: **source** + **execution** + **derived**

Our line-by-line audit of `bytecodealliance/regalloc2` (`src/checker.rs:42-793`)
uncovered four concrete soundness gaps that prevent an unmodified port of
`src/checker.rs` from satisfying a formal forward simulation theorem:

1. **Gap 1 — Untracked-Source `Edit::Move` Fails to Kill Destination
   (`src/checker.rs:554-562`):**
   In `CheckerState::update`:
   ```rust
   &CheckerInst::Move { into, from } => {
       if let Some(val) = self.get_value(&from).cloned() {
           self.set_value(into, val);
       }
   }
   ```
   When `from` is not present in `self.allocs` (for example, when an
   uninitialized or previously clobbered physical register is moved into an
   `Allocation` `into` that currently holds a live virtual register $v$),
   `self.get_value(&from)` returns `None`. Instead of removing `into` from
   `self.allocs`, the `if let Some(val)` guard leaves `into` untouched. The
   checker continues to believe `into` holds $v$ after the runtime machine
   instruction `into := from` has overwritten `into` with garbage.
   - **Repair (`updateMove` in `support/track4_regalloc2_stacking_probe.lean:509-514`
     and `updateSubRegMove` in `support/round2_track3_probe.lean:745-752`):**
     Unconditionally kill all existing bindings for `m.into` before copying any
     bindings from `m.from_`. When `m.from_` holds no tracked `VReg`, `m.into`
     becomes empty.
2. **Gap 2 — `has_reused_input` Early Return Skips All `InstPosition::After`
   Checks (`src/checker.rs:491-493`):**
   In `CheckerState::check`:
   ```rust
   for (op, alloc) in operands.iter().zip(allocs.iter()) {
       if has_reused_input && pos == InstPosition::After {
           return Ok(());
       }
       ...
   ```
   On x86-64, where almost every two-address instruction has an
   `OperandConstraint::Reuse(0)` output operand, `has_reused_input` is `true`
   (`src/checker.rs:297-299`). Because `return Ok(())` executes on the first
   iteration of the operand loop, **every instruction with a reused input skips
   all `InstPosition::After` validation for all of its operands**, including
   non-reused `Late` `Use` operands (which can be clobbered by an `Early` `Def`)
   and `After`-phase constraint checks.
   - **Repair:** Never return early from the operand loop; validate all `Early`
     `Use`s before `Early` `Def`s, and validate all `Late` `Use`s after `Early`
     `Def`s and before `Late` `Def`s/clobbers.
3. **Gap 3 — Single-Pass `Early`/`Late` `Def` Update and Missing Multi-`Def`
   Disjointness (`src/checker.rs:505, 596-622`):**
   `CheckerState::update` applies both `OperandPos::Early` and
   `OperandPos::Late` `Def`s in one loop (`src/checker.rs:607-621`) after
   `InstPosition::Before` and before `InstPosition::After`, while `check_val`
   (`src/checker.rs:505`) skips all `OperandKind::Def`s. Thus:
   - An `Early` `Def` assigned to the same `Allocation` as a non-reused `Early`
     `Use` is not rejected at `Before`, violating `regalloc2`'s documented
     operand-phase semantics (`src/lib.rs:340-352`).
   - Two distinct `Def`s $v_1 \ne v_2$ on the same instruction assigned to the
     same `Allocation` $a$ silently overwrite each other in `update`.
   - **Repair:** Separate `Early` `Def` updates from `Late` `Def` updates (or
     enforce pairwise disjointness between `Early` `Def`s and non-reused `Use`s
     and across all `Def` allocations on an instruction).
4. **Gap 4 — Entry-Block `Top` Lattice Initialization
   (`src/checker.rs:474-478, 753`):**
   `Checker::new` initializes `bb_in[entry]` to `CheckerState::Top` ($\top$) and
   relies on `become_defined()` inside the first `update` call to transition to
   an empty map. Initializing `blockIn[0]` directly to the function's entry
   parameter/callee-save bindings (or `[]`) removes the special-case $\top$
   state altogether.

#### Linear-Pass `blockIn` Certificate Checking (`checkRegAlloc_sound` / `checkCFGWithCert_sound`)

Rather than iterating Kildall's worklist to a fixpoint inside the Lean 4 kernel,
the untrusted Rust `regalloc2` pass runs `Checker::analyze` and emits the
converged per-block entry state vector `blockIn : List CheckerState` as an
untrusted certificate:

- For each block $b$, `checkBlock` (`support/track4_regalloc2_stacking_probe.lean:657-665`)
  starts from `st0 = blockIn[b]`, steps through $b$'s `AllocatedInst`s via
  `checkAllocatedInsts`, and obtains `Some stOut`.
- At the block terminator `checkTerm` (`L623-655`), for every control-flow edge
  to a target block `target` with edge moves `edits`, the validator runs
  `checkEditMoves stOut edits = some stEdge` and checks the decidable subset
  inclusion `subState (blockIn[target]) stEdge = true`:
  $$\text{subState}(\text{req}, \text{actual}) \iff \forall (a, v) \in \text{req},\; (a, v) \in \text{actual}$$

Theorem `checkRegAlloc_sound` (`support/track4_regalloc2_stacking_probe.lean:1073-1200`)
proves that whenever `checkRegAlloc vf af blockIn = true`, the allocated CFG
machine `anAllocMachine af` refines the virtual-register CFG machine
`anVRegMachine vf` under lockstep simulation relation `AllocRel vf.numLocals blockIn`
in a single $O(B + I)$ pass with zero fuel parameters.

### 3. Sub-Register Family Aliasing (`w8|w16|w32|w64`) and Callee-Saved Register Entry Tokens

Basis: **source** + **execution** + **derived**

#### 3.1 Width-Tagged Sub-Register Family Aliasing (`killAllocFamily`, `subreg_checkRegAlloc_sound`)

Upstream `regalloc2` (`src/lib.rs:277-315`) and `cranelift-codegen`
(`src/isa/x64/inst/regs.rs:1-120`) assign a single `PReg` index to each
architectural register family (`rax`/`eax`/`ax`/`al`). On x86-64 hardware
(`writeSubReg64` in `support/round2_track3_probe.lean:514-520`):

$$\text{writeSubReg64}(\text{old64}, w, \text{val}) = \begin{cases} (\text{old64} - (\text{old64} \bmod 2^8)) + (\text{val} \bmod 2^8) & w = \texttt{.w8} \\ (\text{old64} - (\text{old64} \bmod 2^{16})) + (\text{val} \bmod 2^{16}) & w = \texttt{.w16} \\ \text{val} \bmod 2^{32} & w = \texttt{.w32} \\ \text{val} \bmod 2^{64} & w = \texttt{.w64} \end{cases}$$

As proved in `canary_subreg_partial_write_clobbers_64bit`
(`support/round2_track3_probe.lean:538-544`), if `rax` holds the 64-bit value
`0x0100_0000_0000_002A`, neither an 8-bit write `mov al, 0xFF` nor a 32-bit
write `mov eax, 0x2A` preserves the 64-bit value in `rax`. Conversely, writing
`al` at `.w8` leaves bits `[63:8]` of `rax` holding stale data, so reading `rax`
at `.w64` without an explicit `movzx` (`.zext .w64 .w8`) is unsound.

In `support/round2_track3_probe.lean:714-766`, we refine symbolic states to
`SubRegCheckerState := List SubRegBinding`, where each binding is a width-tagged
triple `{ alloc : Allocation, width : RegWidth, vreg : VReg }` governed by three
rules:

1. **Family-Wide Kill on Write (`killAllocFamily`, `L732-735`):** Any write or
   `SubRegEditMove` into `dst : Allocation` at any width removes all bindings
   with `b.alloc == dst` across **all** widths `w8 | w16 | w32 | w64`.
2. **Exact-Width Read Verification (`hasVRegWidth`, `L725-729`):** Reading `src`
   at width `w` for virtual register `v` requires
   `{ alloc := src, width := w, vreg := v } ∈ st`.
3. **Explicit Widening (`zext`, `L627, 637, 789-796`):** Widening from `wSrc` to
   `wDst` requires an explicit `.zext wDst wSrc dst src` instruction that checks
   `hasVRegWidth st src wSrc vSrc`, kills `dst`'s family, and records
   `{ alloc := dst, width := wDst, vreg := vDst }`.

Lemma `readSubReg64_writeSubReg64_same` (`L524-530`) proves that reading back the
exact width `w` written always yields `truncateWidth w val`, and theorem
`subreg_checkRegAlloc_sound` (`L1223-1239`) proves semantic preservation across
all four widths. Canary `canary_subreg_width_mismatch_rejected` (`L1289-1295`)
confirms that writing `al` (`.w8`) and returning `rax` (`.w64`) without `zext`
is rejected (`= false`), whereas inserting `zext .w64 .w8` is accepted (`= true`).

#### 3.2 Callee-Saved Register Verification via Read-Only `VReg` Entry Tokens (`callee_saved_preserved_of_checkRegAlloc`)

Rather than verifying prologue/epilogue callee-save preservation (`rbx`, `rbp`,
`r12`–`r15` on x86-64; `x19`–`x30` on AArch64; `s0`–`s11`, `ra` on RISC-V) in a
separate syntactic pass that struggles with shrink-wrapping, we verify
callee-saved registers inside `checkSubRegFunc`
(`support/round2_track3_probe.lean:823-851`):

- **Entry Token Seeding (`initialCalleeSaveState`):** For each `r ∈ calleeSaved`,
  seed the entry state with `{ alloc := .preg r, width := .w64, vreg :=
  calleeSaveToken r }`, where `calleeSaveToken r := 100000 + r.idx` is a
  reserved read-only `VReg` token (`instsPreserveTokens`).
- **Spill, Call Clobber, and Reload:** Saving `r` to `.spill s` is an ordinary
  `SubRegEditMove { into := .spill s, from_ := .preg r, width := .w64 }`,
  copying `calleeSaveToken r` to `.spill s`. `Call` instructions clobber only
  `callerSaved` via `killPRegFamilies`. Restoring `r` before return is an
  ordinary `SubRegEditMove` from `.spill s` back to `.preg r`.
- **Return Check (`checkCalleeSavedAtReturn`):** At `Return`, the checker
  verifies `calleeSaved.all (fun r => hasVRegWidth stRet (.preg r) .w64 (calleeSaveToken r))`.

Theorem `callee_saved_preserved_of_checkRegAlloc` (`L1244-1260`) and master
theorem `subreg_and_callee_saved_sound` (`L1170-1219`) prove that every
`r ∈ calleeSaved` holds its exact entry 64-bit value
`readSubReg64 (pregsFinal r) .w64 = readSubReg64 (pregs r) .w64` upon return,
while `canary_callee_save_protocol_adequacy` (`L1329-1334`) confirms that
clobbering a callee-saved register without restoring it is rejected (`= false`)
and spilling/reloading it around the clobber is accepted (`= true`).

### 4. CompCert-Style `Stacking` Frame Layout, Public/Private Partitioning (`fe_stack_data`), and `PNVI-ae-udi` Guard Slots

Basis: **source** + **execution** + **derived**

#### 4.1 CompCert and Stack-Aware CompCert Frame Separation

In CompCert (`x86/Stacklayout.v:36-62`, `riscV/Stacklayout.v:35-60`,
`backend/Bounds.v:43-59`, `backend/Stackingproof.v:371-382`), `make_env` lays out
each function's activation frame `fe : frame_env` with outgoing arguments, back
link (`fe_ofs_link`), return address (`fe_ofs_retaddr`), saved callee-save
registers (`fe_ofs_callee_save`), local spill slots (`fe_ofs_local`), and
address-taken stack data (`fe_stack_data`). The simulation invariant
`frame_contents` (`Stackingproof.v:378-382`) maps the source stack block `stk`
via memory injection $j(\text{stk}) = \lfloor (\text{sp}, \text{fe\_stack\_data}(\text{fe})) \rfloor$
and separates the private ranges `[0, fe_stack_data)` and
`[fe_stack_data + bound_stack_data, fe_size)` from `minjection j m` using
separating conjunction `**`.

Stack-Aware CompCert (`ssrg-vt/compcert_stack_aware`, `common/StackADT.v:30-116`,
`backend/Stackingproof.v:113-119, 1379-1389`) operationalizes this split when
lowering frames into a single contiguous hardware stack block `bstack`:
`frame_info_of_size_and_pubrange` assigns `Public` permission to offsets in
`[fe_stack_data, fe_stack_data + bound_stack_data)` and `Private` permission
elsewhere, and `public_stack_access` enforces that any cross-frame pointer store
targets only `Public` bytes.

#### 4.2 Anneal's `PartitionedFrameLayout` and `public_store_preserves_private_spills_and_saved_regs`

In Anneal (`support/round2_track3_probe.lean:122-288`), non-address-taken MIR
locals are promoted directly to `VReg`s (whose spills live in private
`[ofsSpills, ofsSpills + spillBytes)`), while address-taken MIR locals
`k < numPublicLocals` receive provenance `FrameAllocId.stackLocal frameId k` inside
the public sub-block `[ofsPublic, ofsPublic + publicBytes)`:

```text
+-------------------------------------------------------------------+ sp + frameSize
| Private: Saved Return Address (RA)          [ofsRetAddr, +8)      | (.private_)
+-------------------------------------------------------------------+ sp + ofsRetAddr
| Private: Saved Callee-Saved Registers       [ofsSaved, +saved)    | (.private_)
+-------------------------------------------------------------------+ sp + ofsSaved
| Private: regalloc2 Spill Slots              [ofsSpills, +spills)  | (.private_)
+-------------------------------------------------------------------+ sp + ofsSpills
| Private: Unexposed Guard Slot (>= 1 byte)   [ofsPublic+pub, ...)  | (.private_)
+-------------------------------------------------------------------+ sp + ofsPublic + publicBytes
| Public: Address-Taken MIR Locals (k = 0..N) [ofsPublic, +pub)     | (.public_)
|   local k at [ofsPublic + localRelOffset k, +localSize k)         |
+-------------------------------------------------------------------+ sp + ofsPublic
| Private: Outgoing Call Arguments            [0, ofsPublic)        | (.private_)
+-------------------------------------------------------------------+ sp
```

Theorem `public_store_preserves_private_spills_and_saved_regs` (`L232-288`)
proves that for any user pointer `p` validated by Phase 1/2 provenance and bounds
(`p.prov = .stackLocal activeFrameId k`, `k < fl.numPublicLocals`, and
`p.offset < fl.localSize k`), the lowered flat byte write at
`addr = sp + fl.ofsPublic + fl.localRelOffset k + p.offset`:
1. Targets a `.public_` byte (`inBounds_local_maps_to_public_region`, `L206-225`),
2. Preserves `PrivateSpillAndSavedInvariant` across all spill bytes
   `sOfs < fl.spillBytes`, all saved callee-save bytes `cOfs < fl.savedBytes`,
   and all 8 return-address bytes `rOfs < 8`,
3. Leaves all memory outside `[sp, sp + fl.frameSize)` unchanged, and
4. Leaves all other public locals `k' ≠ k` in the frame unchanged.

Conversely, `canary_unbounded_ptr_offset_corrupts_spill` (`L322-377`) shows that
an out-of-bounds offset `badOffset = 24` on local `0` overwrites spill slot `0`
at `sp + 24` and falsifies `PrivateSpillAndSavedInvariant`.

#### 4.3 `PNVI-ae-udi` One-Past-The-End Boundary Ambiguity and 1-Byte Unexposed Guard Slots

Under `PNVI-ae-udi` (`core::ptr::with_exposed_provenance`), an integer address
`addr` reconstructed from an exposed allocation `a` is valid for `a` across the
**closed** interval `[base a, base a + size a]` to support round-tripping
one-past-the-end pointers through `usize`.

- **Zero-Padding Ambiguity (`canary_adjacent_exposed_allocs_ambiguous_at_one_past_end`,
  `support/round2_track3_probe.lean:401-410`):** When two exposed allocations
  `a1 = 0` (`[100, 116)`) and `a2 = 1` (`[116, 132)`) are abutting (`base 1 =
  base 0 + size 0 = 116`), the boundary address `116` simultaneously satisfies
  `inExposedFootprint L 0 116` and `inExposedFootprint L 1 116`.
- **1-Byte Unexposed Guard Determinism (`guard_byte_eliminates_pnvi_boundary_ambiguity`,
  `L431-452`):** Enforcing `GuardSeparated L` (`L.base a1 + L.size a1 < L.base a2`
  whenever `L.base a1 ≤ L.base a2` for `a1 ≠ a2`, and `guardBytes ≥ 1` between
  `publicBytes` and `ofsSpills`) guarantees both that `inExposedFootprint`
  determines `a1 = a2` uniquely and that even a one-past-the-end offset
  `ofs ≤ fl.localSize k` on any public local satisfies
  `localByteFlatAddr fl sp k ofs < sp + fl.ofsSpills`.

### 5. Red-Zone Prohibition (`-mno-red-zone`) Under Hardware Interrupts and `__rust_probestack` Guard-Page Probing

Basis: **normative** + **source** + **execution** + **derived**

#### 5.1 `-mno-red-zone` and Asynchronous Interrupt / ISR Safety

The System V AMD64 ABI permits leaf functions in user space to access a 128-byte
**red zone** `[RSP - 128, RSP)` below `RSP` without adjusting `RSP`. If an
asynchronous hardware interrupt, page fault, or signal handler executes on the
active stack while live spill slots reside in `[RSP - 128, RSP)`, the processor
or kernel pushes the interrupt trap frame into `[0, RSP)`, corrupting any frame
data below `RSP` (`redZone_corrupted_by_isr`).

In `support/track4_regalloc2_stacking_probe.lean:2139-2190`:
- `no_red_zone_writeMachLoc` (`L2139-2160`) proves that under `Stacking`'s
  non-negative offset discipline (`0 ≤ offset < frameSize`), `writeMachLoc`
  never modifies any address `addr < sp`.
- `interrupt_preserves_active_frames` (`L2173-2190`, also referred to as
  `noRedZone_preserves_frame_under_isr`) proves that an arbitrary asynchronous
  interrupt `asyncInterruptClobberBelowSP sp intrFrame mem` that overwrites all
  addresses `< sp` preserves `StackFrameCompat fl sp mlocals mspills` for all
  active stack frames in `[sp, stackBase)`.

#### 5.2 `__rust_probestack` and Stack-Clash Guard-Page Invariants

When stack overflow is trapped dynamically by an unmapped OS guard page of size
$P_{\text{guard}} = 4096\text{ B}$ (`STACK_PROBE_SIZE` in `cranelift-codegen`
`src/isa/x64/inst/emit.rs:330-409` and `rust-lang/rust`
`library/compiler-builtins/compiler-builtins/src/probestack.rs:42-118`), a frame
allocation with $\mathcal{S}(f) > P_{\text{guard}}$ that subtracts $\mathcal{S}(f)$
from `SP` in one step can jump across the unmapped guard page into an adjacent
memory mapping (Stack Clash, CVE-2017-1000364).

In `support/track4_regalloc2_stacking_probe.lean:2196-2209`, `probeStep` models
each iteration of the prologue probe loop (`Inst::StackProbeLoop` /
`__rust_probestack`), and theorem `probe_step_bounded` (`L2203-2209`, also
referred to as `probestack_prevents_guard_bypass`) proves that the stack pointer
decrements by at most `guardPageSize` between consecutive memory touches:
$$\text{sp} - (\text{probeStep}(\text{sp}, \text{rem}, P_{\text{guard}})).1 \le P_{\text{guard}}$$

### 6. Quantitative Stack-Usage Certificates $\mathcal{S}(f)$ Discharging `A-BEH-07` Across Direct and Indirect Calls

Basis: **source** + **execution** + **derived**

Following Stack-Aware CompCert (`driver/Compiler.v:150-269`,
`fn_stack_requirements`) and Bedrock2 (`compiler/src/compiler/FitsStack.v:26-103`,
`stack_usage_impl`), `Stacking` exports a computable frame-size certificate
$\mathcal{S}(f) := \text{frameSizeCert}(f)$ (`support/track4_regalloc2_stacking_probe.lean:1381-1384`).

1. **Direct Call Chains (`callChain_no_stackOverflow`):**
   Theorem `callChain_no_stackOverflow`
   (`support/track4_regalloc2_stacking_probe.lean:2113-2135`) proves that for any
   call chain `calls : List FnId` starting at hardware stack pointer `sp`, if
   $$\text{stackLimit} + \sum_{f \in \text{calls}} \mathcal{S}(f) \le \text{sp}$$
   then `allocCallChain cert stackLimit sp calls = .continue_ (sp - totalFrameSize cert calls)`
   and never transitions to `.failed .stackOverflow`. Conversely,
   `canary4_call_exceeding_stack_budget_overflows` (`L2405-2410`) proves that a
   call chain whose cumulative frame size exceeds `sp - stackLimit` transitions
   to `.failed .stackOverflow`.
2. **Indirect and Virtual Calls (`dyn Trait` / `fn`) — Hybrid Two-Tier Discipline
   (`support/round2_track3_probe.lean:1346-1461`):**
   - **Method A — Static VTable / `FnPtr` Contracts (`IndirectCallContract.wcetStack`):**
     Each `dyn Trait` method or `fn` pointer contract carries a worst-case stack
     bound `wcetStack : Nat`. At coercion time, each target `target : FnId`
     discharges `ValidTargetForContract peakStack contract target`
     (`peakStack target ≤ contract.wcetStack`). At the call site, theorem
     `indirect_call_static_contract_no_overflow` (`L1384-1401`, conceptually
     `static_stack_bound_discharges_A_BEH_07`) proves with zero runtime overhead
     that if `usedStack + callerFrameSize + contract.wcetStack ≤ stackBudget`,
     then `evalIndirectCallStatic` succeeds with
     `stackTop - stackBudget ≤ spLowest`. Canary
     `canary_indirect_call_exceeding_contract_caught` (`L1457-1461`) verifies
     that a target exceeding `wcetStack` is rejected at coercion time and overflows
     the caller's budget.
   - **Method B — Dynamic Prologue `stackLimit` Checks (`execDynamicPrologueCheck`):**
     For open plugins, unannotated FFI callbacks, or unbounded recursive cycles,
     emitting Cranelift's `insert_stack_check` (`cranelift-codegen/src/machinst/abi.rs:2263-2266`,
     comparing `sp < stackLimit + frameSize` against a pinned register or TLS
     slot before decrementing `sp`) satisfies theorem
     `dynamic_stack_check_preserves_limit` (`L1433-1448`, conceptually
     `dynamic_stack_check_discharges_A_BEH_07`): every dynamic call chain either
     traps cleanly with `.stackOverflow` before crossing `stackLimit` or
     succeeds with `stackLimit ≤ sp'`.

### 7. Complete Lean 4.34.1 Theorem Inventories

Basis: **execution**

#### 7.1 `support/track4_regalloc2_stacking_probe.lean` (2,476 lines)

| Declaration | Lines | Kind | Description & Axiom Footprint |
| :--- | :--- | :--- | :--- |
| `refines_trans` | `L111-136` | Theorem | Transitivity of step-indexed machine refinement `Refines` |
| `refines_evalSteps` | `L138-174` | Theorem | Multi-step execution preservation under `Refines` |
| `readAlloc_writeAlloc_eq` / `_ne` | `L699-714` | Theorem | Read-over-write laws for `Allocation` (`PReg` and `SpillSlot`) |
| `hasVReg_sound` | `L716-723` | Theorem | `hasVReg st a v = true` implies `readAlloc pregs spills a = vregs v` under `StateCompat` |
| `updateMove_compat` | `L725-755` | Theorem | Repaired `updateMove` (killing `m.into` unconditionally) preserves `StateCompat` |
| `checkEditMoves_compat` | `L757-776` | Theorem | Sequential `EditMove` list validation preserves `StateCompat` |
| `killPReg_compat` / `killClobbers_compat` | `L778-807` | Theorem | Killing clobbered `PReg`s preserves `StateCompat` |
| `updateDef_compat` | `L809-836` | Theorem | Defining `(dst, v)` after killing old `dst`/`v` bindings preserves `StateCompat` |
| `checkMInstOp_sound` | `L838-926` | Theorem | Single-instruction symbolic check implies forward simulation of `execMInstOp` |
| `checkAllocatedInst_sound` / `Insts_sound` | `L928-986` | Theorem | Basic-block instruction sequence symbolic check preserves `StateCompat` and `LocalCompat` |
| `subState_compat` | `L988-999` | Theorem | Subset inclusion `subState req actual = true` weakens `StateCompat` at CFG joins |
| `checkBlocks_get?` / `checkBlocks_get_ab?` | `L1001-1061` | Theorem | Per-block lookup inversion lemmas for `checkBlocks` |
| `checkRegAlloc_sound` | `L1073-1200` | Theorem | **Main RegAlloc Soundness:** `checkRegAlloc vf af blockIn = true` implies `Refines (anVRegMachine vf) (anAllocMachine af) (AllocRel vf.numLocals blockIn)` (`[propext, Classical.choice, Quot.sound]`) |
| `localOffset_lt_frameSize` / `spillOffset_lt_frameSize` / `savedRegOffset_lt_frameSize` | `L1232-1245` | Theorem | All lowered frame slot offsets lie strictly within `[0, fl.frameSize)` |
| `local_spill_disjoint` / `local_saved_disjoint` / `spill_saved_disjoint` | `L1247-1264` | Theorem | Pairwise disjointness of local, spill, and callee-save frame regions |
| `readMachLoc_lowerAlloc` / `writeMachLoc_lowerAlloc` | `L1554-1612` | Theorem | Reading/writing lowered `MachLoc` agrees with `AllocState` and preserves `StackFrameCompat` |
| `readMachLoc_localOffset` / `writeMachLoc_localOffset` | `L1614-1659` | Theorem | Reading/writing lowered local slots preserves `StackFrameCompat` |
| `execMachMoves_lowerEditMoves` | `L1661-1702` | Theorem | Lowered `MachMove` sequence refines `execEditMoves` |
| `execMachInstOp_lowerMInstOp` / `execMachInsts_lowerAllocatedInsts` | `L1704-1884` | Theorem | Lowered `MachInst` sequence refines `execAllocatedInsts` |
| `stacking_sound` | `L1897-2064` | Theorem | **Main `Stacking` Soundness:** `Refines (anAllocMachine af) (anMachMachine (lowerFunc af)) (StackingRel ...)` (`[propext, Classical.choice, Quot.sound]`) |
| `regalloc_and_stacking_sound` | `L2066-2078` | Theorem | **End-to-End Composition:** `AnVReg` $\to$ `AnAlloc` $\to$ `AnMach` refinement (`[propext, Classical.choice, Quot.sound]`) |
| `callChain_no_stackOverflow` | `L2113-2135` | Theorem | Call chain with `stackLimit + totalFrameSize cert calls ≤ sp` never overflows (`[propext, Quot.sound]`) |
| `no_red_zone_writeMachLoc` | `L2139-2160` | Theorem | `-mno-red-zone` frame writes never touch `< sp` (`[propext, Quot.sound]`) |
| `interrupt_preserves_active_frames` | `L2173-2190` | Theorem | Asynchronous interrupts clobbering `< sp` preserve all active frames (`[propext, Quot.sound]`) |
| `probe_step_bounded` | `L2203-2209` | Theorem | Guard-page probe step advances `sp` by at most `guardPageSize` (`[propext, Quot.sound]`) |
| `canary1_aliasing_live_vregs_rejected` | `L2245-2249` | Canary | Two live `VReg`s mapped to `PReg 0` rejected (`= false`, no axioms) |
| `canary2_cyclic_move_without_scratch_rejected` / `_with_scratch_accepted` | `L2311-2321` | Canary | Parallel swap `PReg 0 ↔ PReg 1` without scratch rejected (`= false`) and with scratch `PReg 2` accepted (`= true`, no axioms) |
| `canary3_cfg_join_mismatch_rejected` / `_with_edge_move_accepted` | `L2383-2393` | Canary | Diamond CFG join mismatch rejected (`= false`) and with edge move accepted (`= true`, no axioms) |
| `canary4_call_exceeding_stack_budget_overflows` | `L2405-2410` | Canary | Call chain exceeding budget steps to `.failed .stackOverflow` (no axioms) |

#### 7.2 `support/round2_track3_probe.lean` (1,549 lines)

| Declaration | Lines | Kind | Description & Axiom Footprint |
| :--- | :--- | :--- | :--- |
| `inBounds_local_maps_to_public_region` | `L206-225` | Theorem | In-bounds address-taken local byte offset maps to `.public_` frame permission (`[propext, Classical.choice, Quot.sound]`) |
| `public_store_preserves_private_spills_and_saved_regs` | `L232-288` | Theorem | **Public/Private Frame Isolation:** In-bounds store to public local preserves all private spills, saved callee-saved registers, return address, and other locals (`[propext, Classical.choice, Quot.sound]`) |
| `canary_unbounded_ptr_offset_corrupts_spill` | `L322-377` | Canary | Unbounded offset `24` on local `0` overwrites private spill slot `0` (`[propext, Classical.choice, Quot.sound]`) |
| `canary_adjacent_exposed_allocs_ambiguous_at_one_past_end` | `L401-410` | Canary | Adjacent exposed allocations (`guardBytes = 0`) have ambiguous `PNVI-ae-udi` provenance at boundary `116` (no axioms) |
| `guard_byte_eliminates_pnvi_boundary_ambiguity` | `L431-452` | Theorem | **Guard-Byte Determinism:** `GuardSeparated L` makes `inExposedFootprint` uniquely deterministic (`a1 = a2`) and keeps one-past-the-end public pointers below `ofsSpills` (`[propext, Quot.sound]`) |
| `readSubReg64_writeSubReg64_same` | `L524-530` | Theorem | Reading width `w` after `writeSubReg64` at width `w` yields `truncateWidth w val` (`[propext, Quot.sound]`) |
| `canary_subreg_partial_write_clobbers_64bit` | `L538-544` | Canary | Both `.w8` merge and `.w32` zero-extension clobber a live `.w64` value in `rax` (no axioms) |
| `readAllocWidth_writeAllocWidth_same` / `_ne` | `L566-586` | Theorem | Width-indexed `Allocation` read-over-write laws |
| `hasVRegWidth_sound` | `L864-872` | Theorem | `hasVRegWidth st a w v = true` implies `readAllocWidth pregs spills a w = truncateWidth w (vregs v)` |
| `updateSubRegMove_compat` / `Moves_compat` | `L874-921` | Theorem | Width-tagged `SubRegEditMove` with `killAllocFamily` preserves `SubRegStateCompat` |
| `killAllocFamily_preg_compat` / `killPRegFamilies_compat` | `L923-958` | Theorem | Killing all widths `{w8, w16, w32, w64}` of clobbered registers preserves `SubRegStateCompat` |
| `updateSubRegDef_compat` | `L960-989` | Theorem | Width-tagged definition update preserves `SubRegStateCompat` |
| `checkSubMInstOp_sound` / `checkSubAllocatedInsts_sound` | `L991-1113` | Theorem | Forward simulation of width-tagged instructions (`const`, `add`, `zext`, `callClobber`) |
| `initialCalleeSaveState_compat` / `execSubVInsts_preserves_token` | `L1115-1160` | Theorem | Entry `calleeSaveToken` seeding satisfies `SubRegStateCompat` and survives body instructions |
| `subreg_and_callee_saved_sound` | `L1170-1219` | Theorem | **Combined Sub-Register & Callee-Save Soundness** (`[propext, Quot.sound]`) |
| `subreg_checkRegAlloc_sound` | `L1223-1239` | Theorem | Width-accurate return value preservation under `checkSubRegFunc` (`[propext, Quot.sound]`) |
| `callee_saved_preserved_of_checkRegAlloc` | `L1244-1260` | Theorem | Every `r ∈ calleeSaved` holds its entry 64-bit value at `Return` (`[propext, Quot.sound]`) |
| `canary_subreg_width_mismatch_rejected` | `L1289-1295` | Canary | `.w8` write read at `.w64` without `zext` rejected (`= false`) and with `zext` accepted (`= true`, `[propext]`) |
| `canary_callee_save_protocol_adequacy` | `L1329-1334` | Canary | Unrestored callee-saved clobber rejected (`= false`) and spilled/reloaded clobber accepted (`= true`, `[propext]`) |
| `indirect_call_static_contract_no_overflow` | `L1384-1401` | Theorem | **Static Indirect-Call Bound (`Method A`):** `ValidTargetForContract` + budget check guarantees no stack overflow (`[propext, Quot.sound]`) |
| `dynamic_stack_check_preserves_limit` | `L1433-1448` | Theorem | **Dynamic Prologue Check (`Method B`):** `execDynamicIndirectChain` never crosses `stackLimit` (`[propext, Quot.sound]`) |
| `canary_indirect_call_exceeding_contract_caught` | `L1457-1461` | Canary | Callee exceeding `wcetStack` refutes `ValidTargetForContract` and triggers `.stackOverflow` (no axioms) |

## Boundaries

- **Overlapping high-byte x86-64 sub-registers (`ah`/`bh`/`ch`/`dh`, known not
  to apply without extension):** Our `RegWidth` model (`w8 | w16 | w32 | w64` in
  `support/round2_track3_probe.lean:478-484`) covers low-bit-aligned sub-register
  views (`al`/`ax`/`eax`/`rax`) where `killAllocFamily` maps all widths of the
  same `PReg` family. If an instruction selector emits legacy high-byte
  registers (`ah`, bits `[15:8]` of `rax`) as distinct `PReg` indices, `ah` and
  `al` must map to the same `PReg` family ID so `killAllocFamily` invalidates
  both.
- **Dynamic alloca / variable-length stack frames (`alloca` / `VLA`,
  unsupported in static $\mathcal{S}(f)$):** `PartitionedFrameLayout` and
  `frameSizeCert` assume compile-time constant sizes for `publicBytes`,
  `spillBytes`, and `savedBytes` per function (matching standard Rust MIR, which
  forbids C-style VLAs outside unstable `alloca` intrinsics). Functions using
  dynamic stack allocation cannot be discharged by static `IndirectCallContract`
  alone and must use Method B (`execDynamicPrologueCheck`) paired with periodic
  guard-page probing (`probeStep`).
- **Asynchronous signal handlers sharing the user-space stack (not examined for
  budget accounting):** While `interrupt_preserves_active_frames` proves that an
  interrupt/signal frame pushed below `SP` does not corrupt active frames when
  `-mno-red-zone` is enabled, discharging `A-BEH-07` in user space when OS
  signals are delivered on the *same* stack (rather than an alternate signal
  stack `sigaltstack`) requires reserving `SignalFrameMargin` inside
  `StackBudget`.

## Evidence

### Primary upstream sources

1. **`bytecodealliance/regalloc2`** (v0.15.2,
   `2fe490bc9dda433f70c54f90f7633ed929f693d9` and upstream
   `969bad6297dfca4db2db4eeefebba6c1ebafcf27`):
   - `src/checker.rs:42-99` (`CheckerState`, `CheckerValue`),
     `src/checker.rs:102-225` (`CheckerInst`, `Checker::analyze` Kildall
     workqueue loop), `src/checker.rs:474-661` (`CheckerState::check`,
     `CheckerState::update`, `CheckerState::step`, and the 4 soundness gaps at
     `L474-478`, `L491-493`, `L505`, `L554-562`, `L596-622`, `L753`).
   - `src/moves.rs:84-308` (`MoveResolver::compute_scheduled_moves` parallel-move
     DFS tree/cycle scheduler).
   - `src/lib.rs:260-520` (`PReg`, `VReg`, `Allocation`, `Operand`,
     `OperandPos::Early`/`Late`, `Edit::Move`).
   - `src/ion/mod.rs:341-376`, `src/ion/spill.rs:94-156`.
2. **`bytecodealliance/wasmtime`** (`cranelift-codegen` v0.132.0,
   `83166ba31317afbe1574186798f4db17cd641ab4`):
   - `cranelift/codegen/src/machinst/abi.rs:2200-2310` (`Callee::gen_prologue`,
     `clobbered_callee_saves`, and `insert_stack_check` via `stack_limit_arg`).
   - `cranelift/codegen/src/isa/x64/inst/emit.rs:330-409`
     (`Inst::StackProbeLoop` emission for frames $\ge 4096\text{ B}$).
   - `cranelift/codegen/src/isa/x64/inst/regs.rs:1-120` (x86-64 GPR family to
     `regalloc2::PReg` mapping).
3. **`AbsInt/CompCert`** (v3.18, `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6` and
   `f9573fb9b8ba4b4cecebe1ef3cb8b2ef9ce1fc03`):
   - `backend/Allocation.v:60-630` and `backend/Allocproof.v:125-145` (backward
     Kildall `EqSet` validation and `satisf` invariant).
   - `backend/Bounds.v:43-145` (`bounds_of_function`),
     `backend/Stacking.v:1-244`, `backend/Stackingproof.v:63-91, 371-382`
     (`frame_inject`, `frame_contents_1`, `frame_contents` public/private
     separation), `x86/Stacklayout.v:36-62`, `riscV/Stacklayout.v:35-60`.
4. **`ssrg-vt/compcert_stack_aware`** (`0518d9ffb69ec11e79a214df1afc0b0159930478`,
   Wang et al., POPL 2019, DOI `10.1145/3290382`):
   - `common/StackADT.v:30-116` (`frame_perm := Public | Private`,
     `frame_info_of_size_and_pubrange`, `public_stack_access`).
   - `backend/Stackingproof.v:113-119, 1379-1389` (`frame_Public_stack_data`).
   - `x86/RealAsm.v:122-145` and `driver/Compiler.v:150-269`
     (`fn_stack_requirements` and `final_theorem`).
5. **`CakeML/cakeml`** (`f73189499bb295f0859dec7ee38c169c48da682c` and
   `7b9a722a1d88bc65555110fb6731173cd4be9b34`):
   - `compiler/backend/reg_alloc/reg_allocScript.sml:34-146` (`clash_tree`,
     `check_clash_tree`),
     `compiler/backend/reg_alloc/reg_allocProofScript.sml:154-230`
     (`check_clash_tree_domain`), and
     `compiler/backend/word_allocScript.sml:353-604` (`full_ssa_cc_trans`,
     `get_clash_tree`, `oracle_colour_ok`).
6. **`mit-plv/bedrock2`** (`757f17c6083bf8d43b5293a0db545c8d0aa32a13` and
   `7cbf3ef1be3c4fa6be792371ab0ec79cf773bd7f`):
   - `compiler/src/compiler/RegAlloc.v:123-490` (`assignment`, `check`,
     `states_compat`).
   - `compiler/src/compiler/FitsStack.v:26-103` (`framelength`,
     `stack_usage_impl`).
7. **`rust-lang/rust`** (`92b5b8c87c61b20adc9001b41baf587634a74734` and
   `8006091eb71ae7d9e9bccb66c6122c9d68af4466`):
   - `library/compiler-builtins/compiler-builtins/src/probestack.rs:42-118`
     (`__rust_probestack` 4096-byte loop).
   - `compiler/rustc_target/src/spec/mod.rs` (`StackProbeType`).

### Preserved Lean 4.34.1 support artifacts

- `support/track4_regalloc2_stacking_probe.lean` (SHA-256
  `89b955c52defcb9e47403dddf9846976d5d6ba1418675c0b4e43f0421df19b37`, 2,476
  lines).
- `support/round2_track3_probe.lean` (SHA-256
  `7f3aaf1f1e8dd2917c1ac460bb614c8b77082a3bf786de25bba51d8effd830c0`, 1,549
  lines).

## Revalidation

To re-verify both standalone Lean 4.34.1 mechanizations and their `#guard_msgs
in #print axioms` checks from the package directory:

```bash
lean -j1 -M1024 support/track4_regalloc2_stacking_probe.lean
lean -j1 -M1024 support/round2_track3_probe.lean
```

Both commands must exit with code `0` and produce empty output (confirming all
embedded `#guard_msgs in #print axioms` assertions match and neither `sorryAx`
nor `Lean.ofReduceBool` appears in any theorem's axiom footprint).

Revalidate the upstream findings if:

1. `bytecodealliance/regalloc2` modifies `CheckerState::check` or
   `CheckerState::update` in `src/checker.rs` (diff `src/checker.rs:470-665`
   against `2fe490bc9dda433f70c54f90f7633ed929f693d9`).
2. Anneal introduces dynamically sized stack locals or targets an ISA with
   register windows or non-zero-extended sub-register lanes not covered by
   `RegWidth`.
3. Anneal changes the `A-BEH-07` behavioral contract in `joshlf/anneal`.
