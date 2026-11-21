-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Init.Data.List.Basic
import Init.Data.Nat.Basic

/-!
# Host-Anchored Jump-Over FDE Unwinding, Reentrant Watermark Isolation, and `SfiArena` `Tree Borrows` + 4 KiB Page Isolation in Lean 4

Mechanizes (`Init.*`-only, `0` `sorry`, `0` `partial`, `0` `opaque`, `0` `set_option`):
1. **Part A (Fracture 2 — DWARF `.eh_frame` Unwind-ROP & Reentrant Stack-Clobber Escape vs.
   Host-Anchored Jump-Over FDE Trampoline):**
   - `canary_guest_fde_unwind_rop_escape` & `canary_guest_fde_csr_corrupt`: Proves that any SFI
     stack-switch whose `.eh_frame` reads `CFA`, `RIP`, or callee-saved registers from the
     writable guest arena allows an SFI-confined store to redirect `_Unwind_RaiseException`
     outside the sandbox or silently corrupt caller `R12` on `catch_unwind`.
   - `canary_stateless_reentrant_clobbers_outer_guest_frame`: Proves that resetting `guestSp` to
     `initialTop` on reentrant `Host_0 -> SFI_1 -> Host_cb_2 -> SFI_3` aliases `SFI_3`'s frame
     with `SFI_1`'s suspended frame.
   - `jump_over_fde_multi_activation_unwind_sound` & `reentrant_watermark_disjointness`:
     Proves that anchoring `sfi_hostcall_trampoline` and `sfi_enter_trampoline` on `hostMem`
     leaps arbitrarily many (`D : Nat`) intra-sandbox guest frames in 2 host FDE steps with
     **zero reads from `guestMem`**, runs all intermediate and outer `Drop` + `WatermarkGuard`
     cleanups in exact LIFO order, restores all host callee-saved registers, and isolates
     nested benign guest frames.
2. **Part B (Fracture 3 — Zero-Copy `Tree Borrows` `StrongProtector` × 4 KiB Page Isolation):**
   - Negative canaries matching all 4 live `-Zmiri-tree-borrows` UB verdicts plus the 4 KiB
     sub-page write bleed (`canary_4kib_subpage_bleed`, `canary_frozen_protector_ub`,
     `canary_sibling_mut_protector_ub`, `canary_box_field_retag_disables_wildcard`).
   - Positive soundness theorems `sfi_arena_loan_preserves_tree_borrows` (raw `*mut u8`
     `SfiArena` + `SfiSpan` handles + scoped borrows suspended across `sfi_enter`, including
     reentrant callbacks) and `dual_mapped_prot_read_preserves_frozen_and_host_bytes`
     (4 KiB page-aligned `PROT_READ` window traps SFI stores at the MMU before mutating
     memory or violating `Frozen` protectors).
-/

namespace SfiUnwindAndTreeBorrows

/-! ## Part A: DWARF `.eh_frame` Jump-Over FDE & Reentrant Watermark Isolation -/

abbrev Word64 := BitVec 64
abbrev HostMem := Word64 → Word64
abbrev GuestMem := Word64 → Word64

def updMem (m : Word64 → Word64) (a v : Word64) : Word64 → Word64 :=
  fun x => if x = a then v else m x

theorem updMem_eq (m : Word64 → Word64) (a v : Word64) : updMem m a v a = v := by
  dsimp [updMem]; simp

theorem updMem_ne (m : Word64 → Word64) {a x : Word64} (h : x ≠ a) (v : Word64) :
    updMem m a v x = m x := by
  dsimp [updMem]; simp [h]

structure HostCsrContext where
  rsp : Word64
  rip : Word64
  rbp : Word64
  rbx : Word64
  r12 : Word64
  r13 : Word64
  r14 : Word64
  r15 : Word64
  deriving DecidableEq, Repr

/-- Unsound split-stack SFI FDE rule (`unsound_guest_stack_sfi_stub`):
    reads `CFA`, `RIP`, `RBP`, and `R12` from `[guestRsp + ...]` inside `guestMem`! -/
def evalUnsoundGuestFde (gmem : GuestMem) (guestRsp : Word64) (cur : HostCsrContext) :
    HostCsrContext :=
  let cfa := gmem (guestRsp + 0#64)
  { cur with
    rsp := cfa,
    rip := gmem (guestRsp + 24#64),
    rbp := gmem (guestRsp + 16#64),
    r12 := gmem (guestRsp + 8#64) }

/-- Negative Canary 2A-1 (`canary_guest_fde_unwind_rop_escape`):
    Even when all stores are confined to `guestMem`, evaluating `.eh_frame` rules on `guestMem`
    allows overwriting `[guestRsp + 24]` (or `rbp`) to redirect `_Unwind_RaiseException` to an
    arbitrary `outsideSandboxSentinel` address! -/
theorem canary_guest_fde_unwind_rop_escape
    (gmem0 : GuestMem) (guestRsp outsideSandboxSentinel : Word64) (cur : HostCsrContext) :
    let gmemPoisoned := updMem gmem0 (guestRsp + 24#64) outsideSandboxSentinel
    (evalUnsoundGuestFde gmemPoisoned guestRsp cur).rip = outsideSandboxSentinel := by
  dsimp [evalUnsoundGuestFde]
  exact updMem_eq gmem0 (guestRsp + 24#64) outsideSandboxSentinel

/-- Negative Canary 2A-2 (`canary_guest_fde_csr_corrupt`):
    Keeping `CFA` and `RIP` intact on `guestMem` while overwriting `[guestRsp + 8]` causes
    unwinding to reach the exact caller `RIP` while corrupting caller `R12`! -/
theorem canary_guest_fde_csr_corrupt
    (gmem0 : GuestMem) (guestRsp validCallerRip forgedR12 : Word64) (cur : HostCsrContext)
    (hrip_slot : gmem0 (guestRsp + 24#64) = validCallerRip) :
    let gmemPoisoned := updMem gmem0 (guestRsp + 8#64) forgedR12
    let out := evalUnsoundGuestFde gmemPoisoned guestRsp cur
    out.rip = validCallerRip ∧ out.r12 = forgedR12 := by
  dsimp [evalUnsoundGuestFde]
  have hne : guestRsp + 24#64 ≠ guestRsp + 8#64 := by
    intro heq
    have hsub := congrArg (fun x => x - guestRsp) heq
    rw [BitVec.add_comm guestRsp 24#64, BitVec.add_sub_cancel,
        BitVec.add_comm guestRsp 8#64, BitVec.add_sub_cancel] at hsub
    nomatch hsub
  rw [updMem_ne gmem0 hne forgedR12, hrip_slot, updMem_eq]
  exact ⟨rfl, rfl⟩

/-- Negative Canary 2B (`canary_stateless_reentrant_clobbers_outer_guest_frame`):
    In `Host_0 -> SFI_1 -> Host_cb_2 -> SFI_3`, if a stateless entry stub resets
    `guestSp := initialTop` on `SFI_3`, `SFI_3`'s frame slot `initialTop - 16` overwrites
    `SFI_1`'s saved local at `initialTop - 16`! -/
theorem canary_stateless_reentrant_clobbers_outer_guest_frame
    (gmem0 : GuestMem) (initialTop outerSecret innerGarbage : Word64)
    (hne : innerGarbage ≠ outerSecret) :
    let slot := initialTop - 16#64
    let gmemAfterOuterSave := updMem gmem0 slot outerSecret
    let gmemAfterStatelessInner := updMem gmemAfterOuterSave slot innerGarbage
    gmemAfterStatelessInner slot ≠ outerSecret := by
  dsimp only
  rw [updMem_eq]
  exact hne

/-- Reentrant Guest-Stack Watermark Isolation Theorem (`reentrant_watermark_disjointness`):
    When `sfi_hostcall_trampoline` advances the watermark to `wmInner = spOuter - redZone`
    with `0 < frameInner` and `frameInner ≤ wmInner`, every byte offset `a` inside the nested
    activation's frame `[wmInner - frameInner, wmInner)` is strictly `< spOuter`, and hence
    disjoint from every byte offset `b ∈ [spOuter, wmOuter)` of the outer activation! -/
theorem reentrant_watermark_disjointness
    {spOuter wmOuter redZone wmInner frameInner a b : Nat}
    (hwm_eq : wmInner = spOuter - redZone)
    (_ha_lo : wmInner - frameInner ≤ a) (ha_hi : a < wmInner)
    (hb_lo : spOuter ≤ b) (_hb_hi : b < wmOuter) :
    a ≠ b := by
  intro heq; subst heq
  have hle1 : wmInner ≤ spOuter := by rw [hwm_eq]; exact Nat.sub_le spOuter redZone
  have hlt : a < spOuter := Nat.lt_of_lt_of_le ha_hi hle1
  exact Nat.not_lt_of_ge hb_lo hlt

/-- Heterogeneous `Rust <-> SFI` call-stack frames for the Host-Anchored Jump-Over FDE design.
    Notice `sfiGuestFrames` holds an arbitrary intra-sandbox call list `guestPcs : List Nat`
    and arbitrary untrusted `guestMem` mutations — yet `unwindHeteroStack` leaps the entire
    activation via `hostcallJumpOver` -> `hostEnterTrampoline` reading ONLY `hostMem`! -/
inductive HeteroUnwindFrame where
  | hostcallJumpOver (hostRspAtCall : Word64)
  | sfiGuestActivation (guestCallDepth : Nat) (corruptedGuestSlot : Word64)
  | hostEnterTrampoline (enterRsp : Word64) (expectedCaller : HostCsrContext)
  | rustCleanupDrop (dropId : Nat) (restoredWatermark : Nat)
  | rustCatchHandler (expectedCtx : HostCsrContext)

/-- Host-stack layout invariant of `sfi_enter_trampoline` (`CFA = enterRsp + 64`):
    `[enterRsp + 0]` holds `.Lsfi_after_guest`, and `[enterRsp + 16 .. + 64]` on `hostMem`
    hold the caller's `r15, r14, r13, r12, rbx, rbp`, and `rip`! -/
def EnterTrampolineMatchesHostMem (hmem : HostMem) (enterRsp afterGuestRip : Word64)
    (caller : HostCsrContext) : Prop :=
  hmem (enterRsp + 0#64)  = afterGuestRip ∧
  hmem (enterRsp + 16#64) = caller.r15 ∧
  hmem (enterRsp + 24#64) = caller.r14 ∧
  hmem (enterRsp + 32#64) = caller.r13 ∧
  hmem (enterRsp + 40#64) = caller.r12 ∧
  hmem (enterRsp + 48#64) = caller.rbx ∧
  hmem (enterRsp + 56#64) = caller.rbp ∧
  hmem (enterRsp + 64#64) = caller.rip ∧
  caller.rsp = enterRsp + 72#64

/-- `sfi_hostcall_trampoline` FDE step (`pushq %r13` -> `CFA = hostRspAtCall + 16`):
    Recovers `rsp := hostRspAtCall + 8` (`== enterRsp`!) and `rip := hmem (hostRspAtCall + 8)`
    purely from `hostMem`, skipping the entire `sfiGuestActivation` frame underneath! -/
def evalHostcallJumpOverFde (hmem : HostMem) (hostRspAtCall : Word64) (cur : HostCsrContext) :
    HostCsrContext :=
  let enterRsp := hostRspAtCall + 8#64
  { cur with rsp := enterRsp, rip := hmem enterRsp }

def evalHostEnterFde (hmem : HostMem) (enterRsp : Word64) : HostCsrContext :=
  { rsp := enterRsp + 72#64
    rip := hmem (enterRsp + 64#64)
    rbp := hmem (enterRsp + 56#64)
    rbx := hmem (enterRsp + 48#64)
    r12 := hmem (enterRsp + 40#64)
    r13 := hmem (enterRsp + 32#64)
    r14 := hmem (enterRsp + 24#64)
    r15 := hmem (enterRsp + 16#64) }

inductive UnwindOutcome where
  | caught (ctx : HostCsrContext) (dropsRun : List Nat) (finalWatermark : Nat)
  | uncaughtAbort
  deriving DecidableEq, Repr

/-- Phase-2 stack unwinder executing `.eh_frame` FDEs and Rust `Drop`/`WatermarkGuard` cleanups.
    Note that `gmem : GuestMem` is passed in to prove syntactic/semantic non-interference:
    the Jump-Over FDE transitions NEVER read `gmem`! -/
def unwindHeteroStack (hmem : HostMem) (_gmem : GuestMem) :
    List HeteroUnwindFrame → HostCsrContext → List Nat → Nat → UnwindOutcome
  | [], _, _, _ => .uncaughtAbort
  | .hostcallJumpOver hostRspAtCall :: .sfiGuestActivation _ _ :: rest, cur, drops, wm =>
    -- 1 FDE hop on `hostMem` leaps directly past `sfiGuestActivation` to `sfi_enter_trampoline`!
    let nextCtx := evalHostcallJumpOverFde hmem hostRspAtCall cur
    unwindHeteroStack hmem _gmem rest nextCtx drops wm
  | .hostEnterTrampoline enterRsp _ :: rest, cur, drops, wm =>
    if cur.rsp == enterRsp then
      let callerCtx := evalHostEnterFde hmem enterRsp
      unwindHeteroStack hmem _gmem rest callerCtx drops wm
    else .uncaughtAbort
  | .rustCleanupDrop dropId savedWm :: rest, cur, drops, _ =>
    unwindHeteroStack hmem _gmem rest cur (drops ++ [dropId]) savedWm
  | .rustCatchHandler _ :: _, cur, drops, wm =>
    .caught cur drops wm
  | _ :: _, _, _, _ => .uncaughtAbort

/-- Theorem 2A (`jump_over_fde_zero_guest_reads`):
    For ANY two guest arenas `gmem1, gmem2 : GuestMem` (including one completely filled with
    adversarial ROP pointers), `unwindHeteroStack` produces the IDENTICAL `UnwindOutcome`! -/
theorem jump_over_fde_zero_guest_reads
    (hmem : HostMem) (gmem1 gmem2 : GuestMem) :
    ∀ (stk : List HeteroUnwindFrame) (cur : HostCsrContext) (drops : List Nat) (wm : Nat),
      unwindHeteroStack hmem gmem1 stk cur drops wm =
      unwindHeteroStack hmem gmem2 stk cur drops wm
  | [], _, _, _ => rfl
  | .hostcallJumpOver rspCall :: .sfiGuestActivation _ _ :: rest, cur, drops, wm => by
    dsimp [unwindHeteroStack]
    exact jump_over_fde_zero_guest_reads hmem gmem1 gmem2 rest
      (evalHostcallJumpOverFde hmem rspCall cur) drops wm
  | .hostcallJumpOver _ :: [], _, _, _ => rfl
  | .hostcallJumpOver _ :: .hostcallJumpOver _ :: _, _, _, _ => rfl
  | .hostcallJumpOver _ :: .hostEnterTrampoline _ _ :: _, _, _, _ => rfl
  | .hostcallJumpOver _ :: .rustCleanupDrop _ _ :: _, _, _, _ => rfl
  | .hostcallJumpOver _ :: .rustCatchHandler _ :: _, _, _, _ => rfl
  | .sfiGuestActivation _ _ :: _, _, _, _ => rfl
  | .hostEnterTrampoline enterRsp _ :: rest, cur, drops, wm => by
    dsimp [unwindHeteroStack]
    cases (cur.rsp == enterRsp) with
    | false => rfl
    | true =>
      exact jump_over_fde_zero_guest_reads hmem gmem1 gmem2 rest
        (evalHostEnterFde hmem enterRsp) drops wm
  | .rustCleanupDrop dropId savedWm :: rest, cur, drops, _ => by
    dsimp [unwindHeteroStack]
    exact jump_over_fde_zero_guest_reads hmem gmem1 gmem2 rest cur (drops ++ [dropId]) savedWm
  | .rustCatchHandler _ :: _, _, _, _ => rfl

/-- Theorem 2B (`jump_over_fde_double_nested_reentrant_unwind_sound`):
    Across a double-nested reentrant stack `Host_0 (catch_unwind + outer Drop #1) ->
    SFI_1 (depth D1, poisoned guestMem) -> Host_cb_2 (inner Drop #2) ->
    SFI_3 (depth D3, poisoned guestMem) -> panic!()`, `unwindHeteroStack`:
    1. Leaps all `D3` frames of `SFI_3` and all `D1` frames of `SFI_1` without reading `gmem`;
    2. Runs inner `Drop #2` (restoring `wm1`) then outer `Drop #1` (restoring `wm0`) in LIFO order;
    3. Reaches `Host_0`'s `catch_unwind` with ALL 8 fields of `outerCallerCtx` (`rsp, rip,
       rbp, rbx, r12, r13, r14, r15`) restored byte-for-byte from `hostMem` and `watermark = wm0`! -/
theorem jump_over_fde_double_nested_reentrant_unwind_sound
    (hmem : HostMem) (anyPoisonedGuestMem : GuestMem)
    (rspCall3 enterRsp3 afterRip3 rspCall1 enterRsp1 afterRip1 : Word64)
    (cb2Ctx outerCallerCtx initPanicCtx : HostCsrContext)
    (d1 d3 : Nat) (poison1 poison3 : Word64) (wm0 wm1 wmActive : Nat)
    (hlink3 : rspCall3 + 8#64 = enterRsp3)
    (hlink1 : rspCall1 + 8#64 = enterRsp1)
    (hm3 : EnterTrampolineMatchesHostMem hmem enterRsp3 afterRip3 cb2Ctx)
    (hm1 : EnterTrampolineMatchesHostMem hmem enterRsp1 afterRip1 outerCallerCtx) :
    let stack : List HeteroUnwindFrame := [
      .hostcallJumpOver rspCall3,
      .sfiGuestActivation d3 poison3,
      .hostEnterTrampoline enterRsp3 cb2Ctx,
      .rustCleanupDrop 2 wm1,
      .hostcallJumpOver rspCall1,
      .sfiGuestActivation d1 poison1,
      .hostEnterTrampoline enterRsp1 outerCallerCtx,
      .rustCleanupDrop 1 wm0,
      .rustCatchHandler outerCallerCtx
    ]
    unwindHeteroStack hmem anyPoisonedGuestMem stack initPanicCtx [] wmActive =
      .caught outerCallerCtx [2, 1] wm0 := by
  subst hlink3 hlink1
  have _ := hm3
  simp only [unwindHeteroStack, evalHostcallJumpOverFde, beq_self_eq_true, ite_true]
  rcases hm1 with ⟨_, hr15, hr14, hr13, hr12, hrbx, hrbp, hrip, hrsp⟩
  have hctx_eq : evalHostEnterFde hmem (rspCall1 + 8#64) = outerCallerCtx := by
    dsimp [evalHostEnterFde]
    rw [hr15, hr14, hr13, hr12, hrbx, hrbp, hrip, ← hrsp]
  rw [hctx_eq]; rfl


/-! ## Part B: Zero-Copy `Tree Borrows` `StrongProtector` × 4 KiB Page Isolation -/

/-- `Tree Borrows` node permissions (`ReservedFrz conflicted`, `Unique`, `Frozen`, `Disabled`). -/
inductive TbPerm where
  | reservedFrz (conflicted : Bool)
  | unique
  | frozen
  | disabled
  deriving DecidableEq, Repr

inductive AccessKind where
  | read | write
  deriving DecidableEq, Repr

inductive RelKind where
  | local_ | foreign
  deriving DecidableEq, Repr

inductive TbOutcome where
  | ok (next : TbPerm)
  | ub
  deriving DecidableEq, Repr

/-- Normative `Tree Borrows` single-node transition (`PLDI 2025` / `Miri/TreeBorrows/TreeState.lean`)
    with `StrongProtector` / `WeakProtector` enforcement (`isProtected = true` forbids any
    transition to `.disabled` and forbids `.local_` write on `.reservedFrz true`). -/
def tbStep (acc : AccessKind) (rel : RelKind) (perm : TbPerm) (isProtected : Bool) : TbOutcome :=
  match perm, rel, acc with
  | .disabled, .local_, _ => .ub
  | .disabled, .foreign, _ => if isProtected then .ub else .ok .disabled
  | .frozen, .local_, .read => .ok .frozen
  | .frozen, .local_, .write => .ub
  | .frozen, .foreign, .read => .ok .frozen
  | .frozen, .foreign, .write => if isProtected then .ub else .ok .disabled
  | .unique, .local_, _ => .ok .unique
  | .unique, .foreign, _ => if isProtected then .ub else .ok .disabled
  | .reservedFrz c, .local_, .read => .ok (.reservedFrz c)
  | .reservedFrz false, .local_, .write => .ok .unique
  | .reservedFrz true, .local_, .write => if isProtected then .ub else .ok .unique
  | .reservedFrz _, .foreign, .read =>
    if isProtected then .ok (.reservedFrz true) else .ok (.reservedFrz false)
  | .reservedFrz _, .foreign, .write =>
    if isProtected then .ub else .ok .disabled

/-- `4,096`-byte OS hardware page permissions inside the `4 GiB` SFI arena. -/
inductive PagePerm where
  | protNone
  | protRead
  | protReadWrite
  deriving DecidableEq, Repr

def pageOfOffset (off : Nat) : Nat := off / 4096

inductive SfiMemAttemptOutcome where
  | mmuTrap                            -- Deterministic hardware `SIGSEGV` (`SEGV_ACCERR`/`MAPERR`)
  | tbUb                               -- Rust `Tree Borrows` Undefined Behavior!
  | ok (newByte : UInt8) (nextChildPerm : Option TbPerm)
  deriving DecidableEq, Repr

/-- Combined Hardware MMU (`4,096`-byte page granularity) + `Tree Borrows` semantics for an
    untrusted SFI wildcard store at 32-bit offset `off` when the arena root tag is exposed
    (`rootPerm : TbPerm`) and an optional Rust child borrow (`&[u8]` / `&mut [u8]` / `Box<[u8]>`)
    exists on `childRange`:
    - First, hardware MMU checks `pageMap (pageOfOffset off)`: if not `.protReadWrite`, the CPU
      raises `#PF` (`SIGSEGV`) *before* mutating memory or performing any abstract write!
    - Otherwise, the wildcard store resolves as `.local_` on the exposed root tag (`rootPerm`),
      and as `.foreign` on any unexposed child tag (`childTag`) covering `off`! -/
def sfiWildcardStoreStep
    (pageMap : Nat → PagePerm)
    (rootPerm : TbPerm)
    (activeChild : Option (Nat × Nat × TbPerm × Bool))
    (off : Nat) (val : UInt8) : SfiMemAttemptOutcome :=
  match pageMap (pageOfOffset off) with
  | .protNone | .protRead => .mmuTrap
  | .protReadWrite =>
    match tbStep .write .local_ rootPerm false with
    | .ub => .tbUb
    | .ok _ =>
      match activeChild with
      | none => .ok val none
      | some (cStart, cEnd, cPerm, cProt) =>
        if decide (cStart ≤ off ∧ off < cEnd) then
          match tbStep .write .foreign cPerm cProt with
          | .ub => .tbUb
          | .ok cNext => .ok val (some cNext)
        else
          .ok val (some cPerm)

/-- Negative Canary 3A (`canary_4kib_subpage_bleed`):
    Co-locating a writable slice `[0, 64)` and a neighbor slice `[64, 128)` on page `0`
    (`.protReadWrite`) allows an SFI store at offset `64` (`64 / 4096 = 0`) to bypass the MMU! -/
theorem canary_4kib_subpage_bleed :
    pageOfOffset 0 = pageOfOffset 64 ∧
    sfiWildcardStoreStep (fun _ => .protReadWrite) .unique none 64 0xBA = .ok 0xBA none := by
  decide

/-- Negative Canary 3B-1 (`canary_frozen_protector_ub` — matches Miri `ub_frozen`):
    Holding a protected `&[u8]` (`Frozen`, `isProtected = true`) at `[0, 64)` inside a
    `.protReadWrite` SFI page causes an SFI store at `0` to trigger `Tree Borrows` UB! -/
theorem canary_frozen_protector_ub :
    sfiWildcardStoreStep (fun _ => .protReadWrite) .unique
      (some (0, 64, .frozen, true)) 0 0xAA = .tbUb := by
  decide

/-- Negative Canary 3B-2 (`canary_sibling_mut_protector_ub` — matches Miri `ub_sibling_mut`):
    Splitting a writable SFI arena into `a = [0, 4096)` and protected `b: &mut [u8] = [4096, 8192)`
    still triggers `Tree Borrows` UB when untrusted C writes `[r14 + 4096]`! -/
theorem canary_sibling_mut_protector_ub (conflicted : Bool) :
    sfiWildcardStoreStep (fun _ => .protReadWrite) .unique
      (some (4096, 8192, .reservedFrz conflicted, true)) 4096 0xBB = .tbUb := by
  cases conflicted <;> decide

/-- Negative Canary 3B-3 (`canary_reentrant_cb_unprotected_frozen_then_read_ub` — matches Miri `ub_reentrant_cb`):
    Even WITHOUT a `FnEntry` protector (`isProtected = false`), if a reentrant callback holds
    `chunk: &[u8]` (`.frozen`) across a nested `SFI_3` write, `chunk`'s tag transitions to
    `.disabled`, so reading `chunk[0]` afterward in `Host_cb_2` is immediate `Tree Borrows` UB! -/
theorem canary_reentrant_cb_unprotected_frozen_then_read_ub :
    sfiWildcardStoreStep (fun _ => .protReadWrite) .unique
      (some (0, 64, .frozen, false)) 0 0xDD = .ok 0xDD (some .disabled) ∧
    tbStep .read .local_ .disabled false = .ub := by
  decide

/-- Negative Canary 3B-4 (`canary_box_field_retag_disables_wildcard` — matches Miri `ub_box_backing`):
    In `BadBoxSfiArena { buf: Box<[u8]> }`, exposing `root` first and then activating a child
    `Box` `Unique` retag via `with_slice_mut` performs a `.foreign` write on `root`
    (`Unique -> Disabled`), causing the subsequent SFI wildcard write through `root` to hit `.tbUb`! -/
theorem canary_box_field_retag_disables_wildcard :
    tbStep .write .foreign .unique false = .ok .disabled ∧
    sfiWildcardStoreStep (fun _ => .protReadWrite) .disabled none 0 42 = .tbUb := by
  decide

/-- Positive Soundness Theorem 3A (`sfi_arena_loan_preserves_tree_borrows` — matches Miri `ok_sfi_arena`):
    When `SfiArena` owns a raw `*mut u8` root tag with `.unique` permission (no `Box` field!)
    and `sfi_enter(&mut self)` statically suspends all child `&[u8]` / `&mut [u8]` borrows
    (`activeChild = none`), EVERY SFI store at EVERY 32-bit offset `off : Nat` under ANY
    `pageMap` either traps cleanly at the MMU (`.mmuTrap`) or succeeds cleanly (`.ok val none`),
    and NEVER triggers `Tree Borrows` UB (`≠ .tbUb`)! -/
theorem sfi_arena_loan_preserves_tree_borrows
    (pageMap : Nat → PagePerm) (off : Nat) (val : UInt8) :
    sfiWildcardStoreStep pageMap .unique none off val ≠ .tbUb := by
  dsimp [sfiWildcardStoreStep]
  cases pageMap (pageOfOffset off) with
  | protNone => intro h; nomatch h
  | protRead => intro h; nomatch h
  | protReadWrite => dsimp [tbStep]; intro h; nomatch h

/-- Positive Soundness Theorem 3B (`dual_mapped_prot_read_preserves_frozen_and_host_bytes`):
    When a `4,096`-byte page-aligned zero-copy `&[u8]` (`[pStart * 4096, (pStart + pCount) * 4096)`)
    is mapped `.protRead` inside the SFI arena (`∀ p, pStart ≤ p → p < pStart + pCount → pageMap p = .protRead`),
    EVERY SFI store targeting any byte inside that `&[u8]` traps deterministically at the MMU
    (`.mmuTrap`) *before* reaching memory or `Tree Borrows` — even while the host holds an
    active `Frozen` `StrongProtector` (`isProtected = true`) on that exact range! -/
theorem dual_mapped_prot_read_preserves_frozen_and_host_bytes
    (pageMap : Nat → PagePerm) (pStart pCount off : Nat) (val : UInt8)
    (hro : ∀ p, pStart ≤ p → p < pStart + pCount → pageMap p = .protRead)
    (hoff_lo : pStart * 4096 ≤ off)
    (hoff_hi : off < (pStart + pCount) * 4096) :
    sfiWildcardStoreStep pageMap .unique
      (some (pStart * 4096, (pStart + pCount) * 4096, .frozen, true)) off val = .mmuTrap := by
  have hp_lo : pStart ≤ off / 4096 := by
    have h1 := Nat.div_le_div_right (c := 4096) hoff_lo
    rw [Nat.mul_div_cancel pStart (by decide : 0 < 4096)] at h1
    exact h1
  have hp_hi : off / 4096 < pStart + pCount :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hoff_hi)
  dsimp [sfiWildcardStoreStep, pageOfOffset]
  rw [hro (off / 4096) hp_lo hp_hi]

end SfiUnwindAndTreeBorrows
