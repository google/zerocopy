-- Copyright 2026 The Authors
-- SPDX-License-Identifier: Apache-2.0 OR MIT

/-!
# Mechanized Soundness of Edition 2024 `gen` & `async gen` Coroutines:
# Movability (`E0626` + `mem::swap`), `storage_conflicts` Slot Coloring (`#73137`),
# and `RETURNED ∪ POISONED` Fused-Generator Transitions

Pinned to `Lean v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`).

Strict constructive kernel discipline (matching `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`
`TrustedBoundary.lean` hygiene):
- Purely constructive kernel proofs depending at most on `propext` (zero unfinished proof
  obligations, zero classical choice axioms, zero decision-procedure or native reflection axioms).
- Structural recursion only; every `def` carries `noncomputable` and zero compiler-synthesized
  instances are attached to inductives so the Lean 4 IR compiler emits zero auxiliary unsafe
  recursion helpers.

## Primary-Source Correspondence (`rust-lang/rust`)
1. 4-way ABI & movability split:
   - `compiler/rustc_hir/src/hir.rs:1976-1983` (`CoroutineKind::movability`: `Gen => Movable`,
     `Async | AsyncGen => Static`),
   - `compiler/rustc_ty_utils/src/abi.rs:119-215` (`CoroutineDesugaring::Gen` uniquely
     taking unpinned `&mut Self` rather than `Pin<&mut Self>`),
   - `compiler/rustc_borrowck/src/lib.rs:462-463, 1003-1011` and `path_utils.rs:124-128`
     (`check_for_local_borrow` / `borrow_of_local_data` -> `E0626`).
2. `BitMatrix` `storage_conflicts`, early statement effects, and layout packing:
   - `compiler/rustc_mir_transform/src/coroutine/layout.rs:235-341` (`compute_storage_conflicts`
     via `StorageConflictVisitor::visit_after_early_statement_effect`),
   - `compiler/rustc_mir_dataflow/src/impls/storage_liveness.rs:177-241`
     (`MaybeRequiresStorage::apply_early_statement_effect` vs `apply_primary_statement_effect`),
   - `compiler/rustc_mir_transform/src/coroutine/mod.rs:1136-1144, 1260-1385`
     (`EnsureCoroutineFieldAssignmentsNeverAlias`, `rust-lang/rust#73137`),
   - `compiler/rustc_abi/src/layout/coroutine.rs:62-339` (`coroutine_saved_local_eligibility`).
3. Post-panic `gen` fusing bug & repaired `RETURNED ∪ POISONED` transition:
   - `compiler/rustc_mir_transform/src/coroutine/mod.rs:877-936` at
     `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` / `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`
     (`mod.rs:888-914` at `49d734536222bf28bb6d07d885b3a81d145981da`;
     `coroutine.rs:1243-1270` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`),
   - `library/core/src/panicking.rs:205` (`3ef0c22cd` / `14210df0e`) / `:206` (`342d74463`)
     (`panic_const_gen_fn_none_panic = "`gen fn` should just keep returning `None` after panicking"`),
   - `compiler/rustc_mir_transform/src/coroutine/drop.rs:194-202` (`create_coroutine_drop_shim`).
-/

namespace GenAsyncGenMovabilityAndFusingSoundness

/-! ## Section 1: Constructive Boolean, Nat, and Structural DecidableEq Primitives -/

/-- Structural boolean equality on `Nat` using primitive constructor recursion. -/
noncomputable def natBeq : Nat → Nat → Bool
  | 0, 0 => true
  | m + 1, n + 1 => natBeq m n
  | _, _ => false

theorem natBeq_refl (n : Nat) : natBeq n n = true := by
  induction n with
  | zero => rfl
  | succ _ ih => exact ih

theorem natBeq_symm (m n : Nat) : natBeq m n = natBeq n m := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => rfl
    | succ _ => rfl
  | succ _ ih =>
    cases n with
    | zero => rfl
    | succ k => exact ih k

theorem natBeq_eq_of_true {m n : Nat} (h : natBeq m n = true) : m = n := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => rfl
    | succ _ => contradiction
  | succ _ ih =>
    cases n with
    | zero => contradiction
    | succ _ => rw [ih h]

theorem natBeq_false_of_ne {m n : Nat} (hne : m ≠ n) : natBeq m n = false := by
  cases h : natBeq m n with
  | false => rfl
  | true => exact False.elim (hne (natBeq_eq_of_true h))

theorem natBeq_ne_of_false {m n : Nat} (h : natBeq m n = false) : m ≠ n := by
  intro heq
  subst heq
  rw [natBeq_refl] at h
  contradiction

/-- Manual structural `DecidableEq` on `Nat` without compiler-derived helpers. -/
noncomputable def decEqNat (m n : Nat) : Decidable (m = n) :=
  match h : natBeq m n with
  | true => isTrue (natBeq_eq_of_true h)
  | false => isFalse (natBeq_ne_of_false h)

theorem bool_and_eq_true {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a with
  | false => contradiction
  | true => exact ⟨rfl, h⟩

theorem bool_or_eq_true {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  cases a with
  | true => exact Or.inl rfl
  | false => exact Or.inr h

theorem bool_not_eq_true {a : Bool} (h : (!a) = true) : a = false := by
  cases a with
  | false => rfl
  | true => contradiction

/-! ## Section 2: Movable `Gen` `mem::swap` Relocation Soundness -/

abbrev Addr := Nat
abbrev LocalId := Nat
abbrev SlotId := Nat

/-- Values stored in a coroutine frame's saved-local table.
- `.scalar n`: plain copied/moved integer value.
- `.extRef a`: reference to external memory outside the coroutine frame
  (`place.is_indirect()` in `rustc_borrowck::path_utils::borrow_of_local_data`).
- `.selfPtr frameAddr slot`: self-referential pointer into the coroutine frame itself,
  which requires `Pin<&mut Self>` (`Movability::Static`) and is rejected across `yield`
  by `E0626` in `Movable` `gen` blocks. -/
inductive FrameVal where
  | scalar (n : Nat)
  | extRef (extAddr : Addr)
  | selfPtr (frameAddr : Addr) (slot : LocalId)

/-- Predicate stating a value does not point into a coroutine frame (enforced by `E0626`). -/
noncomputable def NoSelfPtrVal : FrameVal → Prop
  | .scalar _ => True
  | .extRef _ => True
  | .selfPtr _ _ => False

/-- A suspended or unresumed coroutine frame residing at memory address `base`. -/
structure CoroFrame where
  base : Addr
  discr : Nat
  locals : LocalId → Option FrameVal

/-- All saved locals currently stored in `f` are free of self-referential pointers. -/
noncomputable def NoSelfBorrowFrame (f : CoroFrame) : Prop :=
  ∀ l v, f.locals l = some v → NoSelfPtrVal v

/-- Bitwise frame relocation to `newBase` (Rust move / `core::mem::swap` semantics:
copies the frame payload verbatim without rewriting any interior pointers). -/
noncomputable def relocateFrame (newBase : Addr) (f : CoroFrame) : CoroFrame :=
  { base := newBase, discr := f.discr, locals := f.locals }

/-- `core::mem::swap(&mut g1, &mut g2)`: swaps the coroutine states stored at addresses
`g1.base` and `g2.base`, relocating `g2` into `g1.base` and `g1` into `g2.base`. -/
noncomputable def memSwapFrames (g1 g2 : CoroFrame) : CoroFrame × CoroFrame :=
  (relocateFrame g1.base g2, relocateFrame g2.base g1)

/-- Operations executed inside a coroutine resume segment between suspension points. -/
inductive FrameOp where
  | writeScalar (dst : LocalId) (v : Nat)
  | copyLocal (dst : LocalId) (src : LocalId)
  | addScalars (dst : LocalId) (lhs : LocalId) (rhs : LocalId)
  | storeExtRef (dst : LocalId) (extAddr : Addr)
  | derefExtRef (dst : LocalId) (refLocal : LocalId)
  | takeSelfPtr (dst : LocalId) (targetSlot : LocalId)
  | derefSelfPtr (dst : LocalId) (ptrLocal : LocalId)

/-- `E0626` syntactic gate for a `Movable` `gen` segment: no interior self-borrow is formed
to survive across suspension points. -/
noncomputable def OpNoSelfBorrow : FrameOp → Prop
  | .takeSelfPtr _ _ => False
  | _ => True

noncomputable def OpsNoSelfBorrow : List FrameOp → Prop
  | [] => True
  | op :: rest => OpNoSelfBorrow op ∧ OpsNoSelfBorrow rest

/-- One resume segment executed from an active discriminant state. -/
structure FrameSegment where
  ops : List FrameOp
  yieldLocal : LocalId
  nextDiscr : Nat

/-- A coroutine resume program mapping discriminant states (`0` = UNRESUMED, `3+k` = Suspend k)
to resume segments; `1` = RETURNED returns `None`. -/
abbrev FrameProgram := Nat → Option FrameSegment
abbrev ExtMem := Addr → Option Nat

noncomputable def ProgNoSelfBorrow (prog : FrameProgram) : Prop :=
  ∀ d seg, prog d = some seg → OpsNoSelfBorrow seg.ops

/-- Outcome of executing a sequence of `FrameOp`s on a coroutine frame. -/
inductive OpsOutcome where
  | ok (frame : CoroFrame)
  | ubDanglingSelfRef
  | faultTypeOrMissing

/-- Update one local slot in a `CoroFrame`. -/
noncomputable def setFrameLocal (f : CoroFrame) (dst : LocalId) (v : FrameVal) : CoroFrame :=
  { base := f.base
    discr := f.discr
    locals := fun l => if natBeq l dst then some v else f.locals l }

theorem setFrameLocal_relocate (b : Addr) (f : CoroFrame) (dst : LocalId) (v : FrameVal) :
    setFrameLocal (relocateFrame b f) dst v = relocateFrame b (setFrameLocal f dst v) :=
  rfl

theorem noSelfBorrow_setFrameLocal {f : CoroFrame} {dst : LocalId} {v : FrameVal}
    (hf : NoSelfBorrowFrame f) (hv : NoSelfPtrVal v) :
    NoSelfBorrowFrame (setFrameLocal f dst v) := by
  intro l w hw
  change (if natBeq l dst then some v else f.locals l) = some w at hw
  cases hEq : natBeq l dst with
  | true =>
    rw [hEq] at hw
    cases hw
    exact hv
  | false =>
    rw [hEq] at hw
    exact hf l w hw

/-- Execute one `FrameOp`. Note that `.derefSelfPtr` checks `natBeq ptrBase f.base`:
if the frame was relocated (`mem::swap`) after forming `.selfPtr ptrBase slot`,
`ptrBase ≠ f.base` triggers `.ubDanglingSelfRef`. -/
noncomputable def execFrameOp (ext : ExtMem) (op : FrameOp) (f : CoroFrame) : OpsOutcome :=
  match op with
  | .writeScalar dst v => .ok (setFrameLocal f dst (.scalar v))
  | .copyLocal dst src =>
    match f.locals src with
    | some v => .ok (setFrameLocal f dst v)
    | none => .faultTypeOrMissing
  | .addScalars dst lhs rhs =>
    match f.locals lhs, f.locals rhs with
    | some (.scalar a), some (.scalar b) => .ok (setFrameLocal f dst (.scalar (a + b)))
    | _, _ => .faultTypeOrMissing
  | .storeExtRef dst extAddr => .ok (setFrameLocal f dst (.extRef extAddr))
  | .derefExtRef dst refLocal =>
    match f.locals refLocal with
    | some (.extRef a) =>
      match ext a with
      | some v => .ok (setFrameLocal f dst (.scalar v))
      | none => .faultTypeOrMissing
    | _ => .faultTypeOrMissing
  | .takeSelfPtr dst targetSlot => .ok (setFrameLocal f dst (.selfPtr f.base targetSlot))
  | .derefSelfPtr dst ptrLocal =>
    match f.locals ptrLocal with
    | some (.selfPtr ptrBase slot) =>
      match natBeq ptrBase f.base with
      | true =>
        match f.locals slot with
        | some v => .ok (setFrameLocal f dst v)
        | none => .faultTypeOrMissing
      | false => .ubDanglingSelfRef
    | _ => .faultTypeOrMissing

noncomputable def execFrameOps (ext : ExtMem) : List FrameOp → CoroFrame → OpsOutcome
  | [], f => .ok f
  | op :: rest, f =>
    match execFrameOp ext op f with
    | .ok f' => execFrameOps ext rest f'
    | .ubDanglingSelfRef => .ubDanglingSelfRef
    | .faultTypeOrMissing => .faultTypeOrMissing

/-- Observable outcome of a single `Iterator::next(&mut Self)` step. -/
inductive TraceObs where
  | obsYield (v : Nat)
  | obsNone
  | obsUbDanglingSelfRef
  | obsFault

/-- Single `Iterator::next` step on a `CoroFrame`. -/
noncomputable def stepFrame (prog : FrameProgram) (ext : ExtMem) (f : CoroFrame) :
    TraceObs × CoroFrame :=
  match natBeq f.discr 1 with
  | true => (.obsNone, f)
  | false =>
    match prog f.discr with
    | none => (.obsNone, { base := f.base, discr := 1, locals := f.locals })
    | some seg =>
      match execFrameOps ext seg.ops f with
      | .ubDanglingSelfRef => (.obsUbDanglingSelfRef, f)
      | .faultTypeOrMissing => (.obsFault, f)
      | .ok f' =>
        match f'.locals seg.yieldLocal with
        | some (.scalar v) =>
          (.obsYield v, { base := f'.base, discr := seg.nextDiscr, locals := f'.locals })
        | _ => (.obsFault, f')

/-- Multi-step iterator observation trace over `n` calls to `Iterator::next`. -/
noncomputable def evalTrace (prog : FrameProgram) (ext : ExtMem) :
    Nat → CoroFrame → List TraceObs
  | 0, _ => []
  | n + 1, f =>
    let step := stepFrame prog ext f
    step.1 :: evalTrace prog ext n step.2

/-- Predicate stating no `.obsUbDanglingSelfRef` occurs in a trace. -/
noncomputable def TraceNoDanglingUb : List TraceObs → Prop
  | [] => True
  | .obsUbDanglingSelfRef :: _ => False
  | _ :: rest => TraceNoDanglingUb rest

/-- One-op relocation simulation lemma for `E0626`-clean frames. -/
theorem execFrameOp_relocate_bisim (ext : ExtMem) (op : FrameOp) (f : CoroFrame) (b2 : Addr)
    (hOp : OpNoSelfBorrow op) (hFrame : NoSelfBorrowFrame f) :
    (execFrameOp ext op (relocateFrame b2 f) =
      match execFrameOp ext op f with
      | .ok f' => .ok (relocateFrame b2 f')
      | .ubDanglingSelfRef => .ubDanglingSelfRef
      | .faultTypeOrMissing => .faultTypeOrMissing) ∧
    (execFrameOp ext op f ≠ .ubDanglingSelfRef) ∧
    (∀ f', execFrameOp ext op f = .ok f' → NoSelfBorrowFrame f') := by
  cases op with
  | writeScalar dst v =>
    refine ⟨rfl, ?_, ?_⟩
    · intro h; cases h
    · intro f' hf'; cases hf'; exact noSelfBorrow_setFrameLocal hFrame trivial
  | copyLocal dst src =>
    dsimp only [execFrameOp, relocateFrame]
    cases hSrc : f.locals src with
    | none =>
      refine ⟨rfl, ?_, ?_⟩
      · intro h; cases h
      · intro f' hf'; cases hf'
    | some v =>
      refine ⟨rfl, ?_, ?_⟩
      · intro h; cases h
      · intro f' hf'
        cases hf'
        exact noSelfBorrow_setFrameLocal hFrame (hFrame src v hSrc)
  | addScalars dst lhs rhs =>
    dsimp only [execFrameOp, relocateFrame]
    cases hL : f.locals lhs with
    | none =>
      refine ⟨rfl, ?_, ?_⟩
      · intro h; cases h
      · intro f' hf'; cases hf'
    | some vl =>
      cases vl with
      | scalar a =>
        cases hR : f.locals rhs with
        | none =>
          refine ⟨rfl, ?_, ?_⟩
          · intro h; cases h
          · intro f' hf'; cases hf'
        | some vr =>
          cases vr with
          | scalar b =>
            refine ⟨rfl, ?_, ?_⟩
            · intro h; cases h
            · intro f' hf'
              cases hf'
              exact noSelfBorrow_setFrameLocal hFrame trivial
          | extRef _ =>
            refine ⟨rfl, ?_, ?_⟩
            · intro h; cases h
            · intro f' hf'; cases hf'
          | selfPtr _ _ =>
            exact False.elim (hFrame rhs _ hR)
      | extRef _ =>
        refine ⟨rfl, ?_, ?_⟩
        · intro h; cases h
        · intro f' hf'; cases hf'
      | selfPtr _ _ =>
        exact False.elim (hFrame lhs _ hL)
  | storeExtRef dst extAddr =>
    refine ⟨rfl, ?_, ?_⟩
    · intro h; cases h
    · intro f' hf'; cases hf'; exact noSelfBorrow_setFrameLocal hFrame trivial
  | derefExtRef dst refLocal =>
    dsimp only [execFrameOp, relocateFrame]
    cases hRef : f.locals refLocal with
    | none =>
      refine ⟨rfl, ?_, ?_⟩
      · intro h; cases h
      · intro f' hf'; cases hf'
    | some rv =>
      cases rv with
      | extRef a =>
        dsimp only []
        cases hMem : ext a with
        | none =>
          refine ⟨rfl, ?_, ?_⟩
          · intro h; cases h
          · intro f' hf'; cases hf'
        | some v =>
          refine ⟨rfl, ?_, ?_⟩
          · intro h; cases h
          · intro f' hf'
            cases hf'
            exact noSelfBorrow_setFrameLocal hFrame trivial
      | scalar _ =>
        refine ⟨rfl, ?_, ?_⟩
        · intro h; cases h
        · intro f' hf'; cases hf'
      | selfPtr _ _ =>
        exact False.elim (hFrame refLocal _ hRef)
  | takeSelfPtr _ _ =>
    exact False.elim hOp
  | derefSelfPtr dst ptrLocal =>
    dsimp only [execFrameOp, relocateFrame]
    cases hPtr : f.locals ptrLocal with
    | none =>
      refine ⟨rfl, ?_, ?_⟩
      · intro h; cases h
      · intro f' hf'; cases hf'
    | some pv =>
      cases pv with
      | selfPtr _ _ => exact False.elim (hFrame ptrLocal _ hPtr)
      | scalar _ =>
        refine ⟨rfl, ?_, ?_⟩
        · intro h; cases h
        · intro f' hf'; cases hf'
      | extRef _ =>
        refine ⟨rfl, ?_, ?_⟩
        · intro h; cases h
        · intro f' hf'; cases hf'

/-- Multi-op relocation simulation lemma for `E0626`-clean frames. -/
theorem execFrameOps_relocate_bisim (ext : ExtMem) (ops : List FrameOp) (f : CoroFrame) (b2 : Addr)
    (hOps : OpsNoSelfBorrow ops) (hFrame : NoSelfBorrowFrame f) :
    (execFrameOps ext ops (relocateFrame b2 f) =
      match execFrameOps ext ops f with
      | .ok f' => .ok (relocateFrame b2 f')
      | .ubDanglingSelfRef => .ubDanglingSelfRef
      | .faultTypeOrMissing => .faultTypeOrMissing) ∧
    (execFrameOps ext ops f ≠ .ubDanglingSelfRef) ∧
    (∀ f', execFrameOps ext ops f = .ok f' → NoSelfBorrowFrame f') := by
  induction ops generalizing f with
  | nil =>
    refine ⟨rfl, ?_, ?_⟩
    · intro h; cases h
    · intro f' hf'; cases hf'; exact hFrame
  | cons op rest ih =>
    rcases hOps with ⟨hOp, hRest⟩
    rcases execFrameOp_relocate_bisim ext op f b2 hOp hFrame with ⟨hRel, hNoUb, hPres⟩
    dsimp only [execFrameOps]
    rw [hRel]
    cases hStep : execFrameOp ext op f with
    | ubDanglingSelfRef => exact False.elim (hNoUb hStep)
    | faultTypeOrMissing =>
      refine ⟨rfl, ?_, ?_⟩
      · intro h; cases h
      · intro f' hf'; cases hf'
    | ok f1 =>
      have hF1 : NoSelfBorrowFrame f1 := hPres f1 hStep
      exact ih f1 hRest hF1

/-- Single-step relocation simulation lemma for `stepFrame`. -/
theorem stepFrame_relocate_bisim (prog : FrameProgram) (ext : ExtMem) (f : CoroFrame) (b2 : Addr)
    (hProg : ProgNoSelfBorrow prog) (hFrame : NoSelfBorrowFrame f) :
    (stepFrame prog ext (relocateFrame b2 f)).1 = (stepFrame prog ext f).1 ∧
    (stepFrame prog ext (relocateFrame b2 f)).2 = relocateFrame b2 (stepFrame prog ext f).2 ∧
    (stepFrame prog ext f).1 ≠ .obsUbDanglingSelfRef ∧
    NoSelfBorrowFrame (stepFrame prog ext f).2 := by
  dsimp only [stepFrame]
  have hDiscrRel : (relocateFrame b2 f).discr = f.discr := rfl
  rw [hDiscrRel]
  cases hDiscr : natBeq f.discr 1 with
  | true =>
    refine ⟨rfl, rfl, ?_, hFrame⟩
    intro h; cases h
  | false =>
    dsimp only []
    cases hSeg : prog f.discr with
    | none =>
      refine ⟨rfl, rfl, ?_, hFrame⟩
      intro h; cases h
    | some seg =>
      dsimp only []
      have hOps := hProg f.discr seg hSeg
      rcases execFrameOps_relocate_bisim ext seg.ops f b2 hOps hFrame with ⟨hRel, hNoUb, hPres⟩
      rw [hRel]
      cases hExec : execFrameOps ext seg.ops f with
      | ubDanglingSelfRef => exact False.elim (hNoUb hExec)
      | faultTypeOrMissing =>
        refine ⟨rfl, rfl, ?_, hFrame⟩
        intro h; cases h
      | ok f' =>
        have hF' : NoSelfBorrowFrame f' := hPres f' hExec
        dsimp only [relocateFrame]
        cases hY : f'.locals seg.yieldLocal with
        | none =>
          refine ⟨rfl, rfl, ?_, hF'⟩
          intro h; cases h
        | some yv =>
          cases yv with
          | scalar v =>
            refine ⟨rfl, rfl, ?_, hF'⟩
            intro h; cases h
          | extRef _ =>
            refine ⟨rfl, rfl, ?_, hF'⟩
            intro h; cases h
          | selfPtr _ _ =>
            exact False.elim (hF' seg.yieldLocal _ hY)

/-- **Main Theorem 1 (`movable_gen_no_self_borrow_relocation_bisim`):**
When `rustc_borrowck` enforces `E0626` (`ProgNoSelfBorrow prog` and `NoSelfBorrowFrame f`),
relocating a suspended `Movable` `gen` coroutine frame from address `f.base` to ANY address
`b2` is observationally bisimilar for all `n`-step `Iterator::next(&mut Self)` traces and
never triggers dangling self-reference UB. -/
theorem movable_gen_no_self_borrow_relocation_bisim
    (prog : FrameProgram) (ext : ExtMem) (f : CoroFrame) (b2 : Addr) (n : Nat)
    (hProg : ProgNoSelfBorrow prog) (hFrame : NoSelfBorrowFrame f) :
    evalTrace prog ext n (relocateFrame b2 f) = evalTrace prog ext n f ∧
    TraceNoDanglingUb (evalTrace prog ext n f) := by
  induction n generalizing f with
  | zero => exact ⟨rfl, trivial⟩
  | succ k ih =>
    rcases stepFrame_relocate_bisim prog ext f b2 hProg hFrame with
      ⟨hObs, hNext, hNoUb, hPres⟩
    rcases ih (stepFrame prog ext f).2 hPres with ⟨hTailEq, hTailNoUb⟩
    constructor
    · dsimp only [evalTrace]
      rw [hObs, hNext, hTailEq]
    · dsimp only [evalTrace]
      cases hO : (stepFrame prog ext f).1 with
      | obsUbDanglingSelfRef => exact False.elim (hNoUb hO)
      | obsYield _ => exact hTailNoUb
      | obsNone => exact hTailNoUb
      | obsFault => exact hTailNoUb

/-- Corollary: mid-yield `core::mem::swap(&mut g1, &mut g2)` between two `E0626`-clean
suspended `gen` frames exchanges their future observation streams bit-for-bit without UB. -/
theorem movable_gen_mem_swap_interleaving_bisim
    (prog : FrameProgram) (ext : ExtMem) (g1 g2 : CoroFrame) (n : Nat)
    (hProg : ProgNoSelfBorrow prog)
    (h1 : NoSelfBorrowFrame g1) (h2 : NoSelfBorrowFrame g2) :
    let swapped := memSwapFrames g1 g2
    evalTrace prog ext n swapped.1 = evalTrace prog ext n g2 ∧
    evalTrace prog ext n swapped.2 = evalTrace prog ext n g1 ∧
    TraceNoDanglingUb (evalTrace prog ext n swapped.1) ∧
    TraceNoDanglingUb (evalTrace prog ext n swapped.2) := by
  have hSwap1 := movable_gen_no_self_borrow_relocation_bisim prog ext g2 g1.base n hProg h2
  have hSwap2 := movable_gen_no_self_borrow_relocation_bisim prog ext g1 g2.base n hProg h1
  refine ⟨hSwap1.1, hSwap2.1, ?_, ?_⟩
  · change TraceNoDanglingUb (evalTrace prog ext n (relocateFrame g1.base g2))
    rw [hSwap1.1]
    exact hSwap1.2
  · change TraceNoDanglingUb (evalTrace prog ext n (relocateFrame g2.base g1))
    rw [hSwap2.1]
    exact hSwap2.2

/-! ## Section 3: `BitMatrix` `storage_conflicts` Coloring & `#73137` Non-Self-Aliasing Soundness -/

/-- Coroutine MIR statements modeling storage liveness, assignments, and suspension yields.
In particular, `.assignMove dst src` models a move/copy assignment where `dst` is generated
in `MaybeRequiresStorage::apply_early_statement_effect` BEFORE `src` is killed in
`apply_primary_statement_effect` (`storage_liveness.rs:189-225`), matching `#73137`. -/
inductive CoroStmt where
  | storageLive (l : LocalId)
  | storageDead (l : LocalId)
  | writeConst (dst : LocalId) (v : Nat)
  | assignMove (dst : LocalId) (src : LocalId)
  | addAssign (dst : LocalId) (lhs : LocalId) (rhs : LocalId)
  | yieldLocal (src : LocalId)

abbrev LiveSet := LocalId → Bool
abbrev ConflictMatrix := LocalId → LocalId → Bool
abbrev UnpackedStore := LocalId → Option Nat
abbrev PackedStore := SlotId → Option Nat
abbrev SlotColoring := LocalId → SlotId

noncomputable def liveInsert (live : LiveSet) (l : LocalId) : LiveSet :=
  fun x => if natBeq x l then true else live x

noncomputable def liveRemove (live : LiveSet) (l : LocalId) : LiveSet :=
  fun x => if natBeq x l then false else live x

/-- `MaybeRequiresStorage::apply_early_statement_effect` (`storage_liveness.rs:177-208`):
generates `dst` BEFORE killing any moved-from `src`! -/
noncomputable def earlyLive (live : LiveSet) : CoroStmt → LiveSet
  | .storageLive l => liveInsert live l
  | .storageDead l => liveRemove live l
  | .writeConst dst _ => liveInsert live dst
  | .assignMove dst _ => liveInsert live dst
  | .addAssign dst _ _ => liveInsert live dst
  | .yieldLocal _ => live

/-- `MaybeRequiresStorage::apply_primary_statement_effect` (`storage_liveness.rs:210-241`):
kills moved-from `src` (when `src ≠ dst`), then ensures `dst` remains live. -/
noncomputable def primaryLive (live : LiveSet) : CoroStmt → LiveSet
  | .storageLive l => liveInsert live l
  | .storageDead l => liveRemove live l
  | .writeConst dst _ => liveInsert live dst
  | .assignMove dst src => liveInsert (liveRemove live src) dst
  | .addAssign dst _ _ => liveInsert live dst
  | .yieldLocal _ => live

/-- `StorageConflictVisitor::visit_after_early_statement_effect` (`coroutine/layout.rs:308-340`):
records a conflict between EVERY pair of locals simultaneously present in `earlyLive`. -/
noncomputable def EarlyConflictsCover (conflicts : ConflictMatrix) (live : LiveSet) : List CoroStmt → Prop
  | [] => True
  | s :: rest =>
    (∀ a b, earlyLive live s a = true → earlyLive live s b = true → conflicts a b = true) ∧
    EarlyConflictsCover conflicts (primaryLive live s) rest

/-- `rustc_abi::layout::coroutine::layout` non-overlapping slot invariant:
distinct locals marked conflicting in `storage_conflicts` receive distinct physical slots. -/
noncomputable def ValidSlotColoring (conflicts : ConflictMatrix) (color : SlotColoring) : Prop :=
  ∀ a b, a ≠ b → conflicts a b = true → color a ≠ color b

/-- Simulation invariant: packed slot memory agrees with unpacked per-local memory
on every currently storage-live local. -/
noncomputable def StoreAgreesOnLive (live : LiveSet) (unpacked : UnpackedStore) (packed : PackedStore)
    (color : SlotColoring) : Prop :=
  ∀ l, live l = true → packed (color l) = unpacked l

inductive CoroExecResult where
  | ok (yields : List Nat)
  | ubAliasingAssign
  | ubDeadOrUninitRead

noncomputable def writeUnpacked (env : UnpackedStore) (dst : LocalId) (v : Nat) : UnpackedStore :=
  fun x => if natBeq x dst then some v else env x

noncomputable def clearUnpacked (env : UnpackedStore) (dst : LocalId) : UnpackedStore :=
  fun x => if natBeq x dst then none else env x

noncomputable def writePacked (slots : PackedStore) (slot : SlotId) (v : Nat) : PackedStore :=
  fun s => if natBeq s slot then some v else slots s

noncomputable def clearPacked (slots : PackedStore) (slot : SlotId) : PackedStore :=
  fun s => if natBeq s slot then none else slots s

/-- Reference unpacked MIR semantics (every `LocalId` has its own disjoint storage).
`StorageLive(l)` allocates uninitialized storage (`none`), matching `rustc_const_eval`
and `joshlf/anneal` `Trusted.MirSemantics`. -/
noncomputable def execUnpacked (live : LiveSet) (env : UnpackedStore) :
    List CoroStmt → CoroExecResult
  | [] => .ok []
  | s :: rest =>
    match s with
    | .storageLive l => execUnpacked (primaryLive live s) (clearUnpacked env l) rest
    | .storageDead _ => execUnpacked (primaryLive live s) env rest
    | .writeConst dst v =>
      execUnpacked (primaryLive live s) (writeUnpacked env dst v) rest
    | .assignMove dst src =>
      match live src with
      | false => .ubDeadOrUninitRead
      | true =>
        match env src with
        | none => .ubDeadOrUninitRead
        | some v => execUnpacked (primaryLive live s) (writeUnpacked env dst v) rest
    | .addAssign dst lhs rhs =>
      match live lhs && live rhs with
      | false => .ubDeadOrUninitRead
      | true =>
        match env lhs, env rhs with
        | some a, some b => execUnpacked (primaryLive live s) (writeUnpacked env dst (a + b)) rest
        | _, _ => .ubDeadOrUninitRead
    | .yieldLocal src =>
      match live src with
      | false => .ubDeadOrUninitRead
      | true =>
        match env src with
        | none => .ubDeadOrUninitRead
        | some v =>
          match execUnpacked (primaryLive live s) env rest with
          | .ok ys => .ok (v :: ys)
          | err => err

/-- Packed coroutine-frame semantics under `color : LocalId → SlotId`.
Explicitly enforces MIR's non-aliasing assignment rule (`#73137`): if `dst ≠ src` (or
`dst ≠ lhs` / `dst ≠ rhs`) map to the same physical slot, execution faults with
`.ubAliasingAssign`! -/
noncomputable def execPacked (color : SlotColoring) (live : LiveSet) (slots : PackedStore) :
    List CoroStmt → CoroExecResult
  | [] => .ok []
  | s :: rest =>
    match s with
    | .storageLive l => execPacked color (primaryLive live s) (clearPacked slots (color l)) rest
    | .storageDead _ => execPacked color (primaryLive live s) slots rest
    | .writeConst dst v =>
      execPacked color (primaryLive live s) (writePacked slots (color dst) v) rest
    | .assignMove dst src =>
      match live src with
      | false => .ubDeadOrUninitRead
      | true =>
        match (!natBeq dst src) && natBeq (color dst) (color src) with
        | true => .ubAliasingAssign
        | false =>
          match slots (color src) with
          | none => .ubDeadOrUninitRead
          | some v =>
            execPacked color (primaryLive live s) (writePacked slots (color dst) v) rest
    | .addAssign dst lhs rhs =>
      match live lhs && live rhs with
      | false => .ubDeadOrUninitRead
      | true =>
        match ((!natBeq dst lhs) && natBeq (color dst) (color lhs)) ||
              ((!natBeq dst rhs) && natBeq (color dst) (color rhs)) with
        | true => .ubAliasingAssign
        | false =>
          match slots (color lhs), slots (color rhs) with
          | some a, some b =>
            execPacked color (primaryLive live s) (writePacked slots (color dst) (a + b)) rest
          | _, _ => .ubDeadOrUninitRead
    | .yieldLocal src =>
      match live src with
      | false => .ubDeadOrUninitRead
      | true =>
        match slots (color src) with
        | none => .ubDeadOrUninitRead
        | some v =>
          match execPacked color (primaryLive live s) slots rest with
          | .ok ys => .ok (v :: ys)
          | err => err

theorem liveInsert_self (live : LiveSet) (x : LocalId) :
    liveInsert live x x = true := by
  unfold liveInsert
  rw [natBeq_refl]
  rfl

theorem liveInsert_of_live {live : LiveSet} {x y : LocalId} (h : live y = true) :
    liveInsert live x y = true := by
  unfold liveInsert
  cases hEq : natBeq y x with
  | true => rfl
  | false => exact h

theorem liveRemove_implies_live {live : LiveSet} {x y : LocalId}
    (h : liveRemove live x y = true) : live y = true := by
  unfold liveRemove at h
  cases hEq : natBeq y x with
  | true => rw [hEq] at h; cases h
  | false => rw [hEq] at h; exact h

/-- Key framing lemma: writing `dst` into `slots (color dst)` preserves agreement on every
local `l` in `liveInsert live dst` (and hence any subset such as `primaryLive`), because
`EarlyConflictsCover` ensures every `l ≠ dst` live at the early point has `color l ≠ color dst`. -/
theorem storeAgrees_write {live : LiveSet} {unpacked : UnpackedStore} {packed : PackedStore}
    {conflicts : ConflictMatrix} {color : SlotColoring} {dst : LocalId} {v : Nat}
    (hAgree : StoreAgreesOnLive live unpacked packed color)
    (hValid : ValidSlotColoring conflicts color)
    (hEarly : ∀ a b, liveInsert live dst a = true → liveInsert live dst b = true →
      conflicts a b = true) :
    StoreAgreesOnLive (liveInsert live dst) (writeUnpacked unpacked dst v)
      (writePacked packed (color dst) v) color := by
  intro l hLive
  dsimp only [writePacked, writeUnpacked]
  cases hEqL : natBeq l dst with
  | true =>
    have hL : l = dst := natBeq_eq_of_true hEqL
    subst hL
    rw [natBeq_refl]
    rfl
  | false =>
    have hNe : l ≠ dst := natBeq_ne_of_false hEqL
    have hConf : conflicts l dst = true := hEarly l dst hLive (liveInsert_self live dst)
    have hColorNe : color l ≠ color dst := hValid l dst hNe hConf
    rw [natBeq_false_of_ne hColorNe]
    dsimp only [liveInsert] at hLive
    rw [hEqL] at hLive
    exact hAgree l hLive

/-- Framing lemma for `StorageLive(dst)`: clearing `dst` to uninitialized (`none`) preserves
agreement on all live locals without clobbering any other live local `l ≠ dst`. -/
theorem storeAgrees_clear {live : LiveSet} {unpacked : UnpackedStore} {packed : PackedStore}
    {conflicts : ConflictMatrix} {color : SlotColoring} {dst : LocalId}
    (hAgree : StoreAgreesOnLive live unpacked packed color)
    (hValid : ValidSlotColoring conflicts color)
    (hEarly : ∀ a b, liveInsert live dst a = true → liveInsert live dst b = true →
      conflicts a b = true) :
    StoreAgreesOnLive (liveInsert live dst) (clearUnpacked unpacked dst)
      (clearPacked packed (color dst)) color := by
  intro l hLive
  dsimp only [clearPacked, clearUnpacked]
  cases hEqL : natBeq l dst with
  | true =>
    have hL : l = dst := natBeq_eq_of_true hEqL
    subst hL
    rw [natBeq_refl]
    rfl
  | false =>
    have hNe : l ≠ dst := natBeq_ne_of_false hEqL
    have hConf : conflicts l dst = true := hEarly l dst hLive (liveInsert_self live dst)
    have hColorNe : color l ≠ color dst := hValid l dst hNe hConf
    rw [natBeq_false_of_ne hColorNe]
    dsimp only [liveInsert] at hLive
    rw [hEqL] at hLive
    exact hAgree l hLive

theorem storeAgrees_subset {live1 live2 : LiveSet} {unpacked : UnpackedStore}
    {packed : PackedStore} {color : SlotColoring}
    (hSub : ∀ l, live1 l = true → live2 l = true)
    (hAgree : StoreAgreesOnLive live2 unpacked packed color) :
    StoreAgreesOnLive live1 unpacked packed color :=
  fun l hl => hAgree l (hSub l hl)

/-- **Main Theorem 2 (`conflict_free_slot_coloring_preserves_semantics`):**
If `conflicts` covers all simultaneous pairs in `earlyLive` (`StorageConflictVisitor` on
`MaybeRequiresStorage::apply_early_statement_effect`) and `color` assigns distinct physical
slots to every conflicting pair (`ValidSlotColoring`), then packed coroutine-frame execution
is bit-for-bit identical to unpacked execution (zero `#73137` self-aliasing faults and zero
cross-variant slot clobbering). -/
theorem conflict_free_slot_coloring_preserves_semantics
    (stmts : List CoroStmt) (live : LiveSet) (env : UnpackedStore) (slots : PackedStore)
    (conflicts : ConflictMatrix) (color : SlotColoring)
    (hCover : EarlyConflictsCover conflicts live stmts)
    (hValid : ValidSlotColoring conflicts color)
    (hAgree : StoreAgreesOnLive live env slots color) :
    execPacked color live slots stmts = execUnpacked live env stmts := by
  induction stmts generalizing live env slots with
  | nil => rfl
  | cons s rest ih =>
    rcases hCover with ⟨hEarlyS, hCoverRest⟩
    cases s with
    | storageLive l =>
      dsimp only [execPacked, execUnpacked]
      exact ih (primaryLive live (.storageLive l)) (clearUnpacked env l)
        (clearPacked slots (color l)) hCoverRest
        (storeAgrees_clear hAgree hValid hEarlyS)
    | storageDead l =>
      dsimp only [execPacked, execUnpacked]
      exact ih (primaryLive live (.storageDead l)) env slots hCoverRest
        (storeAgrees_subset (fun x hx => liveRemove_implies_live hx) hAgree)
    | writeConst dst v =>
      dsimp only [execPacked, execUnpacked]
      exact ih (primaryLive live (.writeConst dst v)) (writeUnpacked env dst v)
        (writePacked slots (color dst) v) hCoverRest
        (storeAgrees_write hAgree hValid hEarlyS)
    | assignMove dst src =>
      dsimp only [execPacked, execUnpacked]
      cases hLiveSrc : live src with
      | false => rfl
      | true =>
        have hNoAlias : ((!natBeq dst src) && natBeq (color dst) (color src)) = false := by
          cases hEqDS : natBeq dst src with
          | true => rfl
          | false =>
            have hNe : dst ≠ src := natBeq_ne_of_false hEqDS
            have hConf : conflicts dst src = true :=
              hEarlyS dst src (liveInsert_self live dst) (liveInsert_of_live hLiveSrc)
            have hColNe : color dst ≠ color src := hValid dst src hNe hConf
            change natBeq (color dst) (color src) = false
            exact natBeq_false_of_ne hColNe
        rw [hNoAlias]
        dsimp only []
        rw [hAgree src hLiveSrc]
        cases hVal : env src with
        | none => rfl
        | some v =>
          have hAgreeNext :
              StoreAgreesOnLive (primaryLive live (.assignMove dst src))
                (writeUnpacked env dst v) (writePacked slots (color dst) v) color := by
            apply storeAgrees_subset _ (storeAgrees_write hAgree hValid hEarlyS)
            intro x hx
            dsimp only [primaryLive, liveInsert] at hx
            dsimp only [liveInsert]
            cases hEqXD : natBeq x dst with
            | true => rfl
            | false =>
              rw [hEqXD] at hx
              exact liveRemove_implies_live hx
          exact ih (primaryLive live (.assignMove dst src)) (writeUnpacked env dst v)
            (writePacked slots (color dst) v) hCoverRest hAgreeNext
    | addAssign dst lhs rhs =>
      dsimp only [execPacked, execUnpacked]
      cases hLiveBoth : (live lhs && live rhs) with
      | false => rfl
      | true =>
        rcases bool_and_eq_true hLiveBoth with ⟨hLiveL, hLiveR⟩
        have hNoAliasL : ((!natBeq dst lhs) && natBeq (color dst) (color lhs)) = false := by
          cases hEqDL : natBeq dst lhs with
          | true => rfl
          | false =>
            have hNe : dst ≠ lhs := natBeq_ne_of_false hEqDL
            have hConf : conflicts dst lhs = true :=
              hEarlyS dst lhs (liveInsert_self live dst) (liveInsert_of_live hLiveL)
            change natBeq (color dst) (color lhs) = false
            exact natBeq_false_of_ne (hValid dst lhs hNe hConf)
        have hNoAliasR : ((!natBeq dst rhs) && natBeq (color dst) (color rhs)) = false := by
          cases hEqDR : natBeq dst rhs with
          | true => rfl
          | false =>
            have hNe : dst ≠ rhs := natBeq_ne_of_false hEqDR
            have hConf : conflicts dst rhs = true :=
              hEarlyS dst rhs (liveInsert_self live dst) (liveInsert_of_live hLiveR)
            change natBeq (color dst) (color rhs) = false
            exact natBeq_false_of_ne (hValid dst rhs hNe hConf)
        rw [hNoAliasL, hNoAliasR]
        dsimp only [Bool.false_or]
        rw [hAgree lhs hLiveL, hAgree rhs hLiveR]
        cases hVL : env lhs with
        | none => rfl
        | some a =>
          cases hVR : env rhs with
          | none => rfl
          | some b =>
            exact ih (primaryLive live (.addAssign dst lhs rhs))
              (writeUnpacked env dst (a + b)) (writePacked slots (color dst) (a + b))
              hCoverRest (storeAgrees_write hAgree hValid hEarlyS)
    | yieldLocal src =>
      dsimp only [execPacked, execUnpacked]
      cases hLiveSrc : live src with
      | false => rfl
      | true =>
        rw [hAgree src hLiveSrc]
        cases hV : env src with
        | none => rfl
        | some v =>
          dsimp only [primaryLive] at hCoverRest ⊢
          rw [ih live env slots hCoverRest hAgree]

/-! ## Section 4: Repaired `RETURNED ∪ POISONED` Fused-Generator Transition -/

/-- The 4-way `rustc` coroutine classification (`compiler/rustc_hir/src/hir.rs:1967-2057`). -/
inductive CoroutineKind where
  | coroutine
  | asyncFn
  | gen
  | asyncGen

noncomputable def CoroutineKind.beq : CoroutineKind → CoroutineKind → Bool
  | .coroutine, .coroutine => true
  | .asyncFn, .asyncFn => true
  | .gen, .gen => true
  | .asyncGen, .asyncGen => true
  | _, _ => false

/-- Manual structural `DecidableEq` on `CoroutineKind` (no compiler-derived instance). -/
noncomputable def decEqCoroutineKind (a b : CoroutineKind) : Decidable (a = b) :=
  match a, b with
  | .coroutine, .coroutine => isTrue rfl
  | .asyncFn, .asyncFn => isTrue rfl
  | .gen, .gen => isTrue rfl
  | .asyncGen, .asyncGen => isTrue rfl
  | .coroutine, .asyncFn => isFalse (fun h => by cases h)
  | .coroutine, .gen => isFalse (fun h => by cases h)
  | .coroutine, .asyncGen => isFalse (fun h => by cases h)
  | .asyncFn, .coroutine => isFalse (fun h => by cases h)
  | .asyncFn, .gen => isFalse (fun h => by cases h)
  | .asyncFn, .asyncGen => isFalse (fun h => by cases h)
  | .gen, .coroutine => isFalse (fun h => by cases h)
  | .gen, .asyncFn => isFalse (fun h => by cases h)
  | .gen, .asyncGen => isFalse (fun h => by cases h)
  | .asyncGen, .coroutine => isFalse (fun h => by cases h)
  | .asyncGen, .asyncFn => isFalse (fun h => by cases h)
  | .asyncGen, .gen => isFalse (fun h => by cases h)

/-- `CoroutineArgs` discriminants (`compiler/rustc_middle/src/ty/sty.rs`):
`0 = UNRESUMED`, `1 = RETURNED`, `2 = POISONED`, `3 + k = Suspend(k)`. -/
inductive CoroutineDiscr where
  | unresumed
  | returned
  | poisoned
  | suspended (k : Nat)

noncomputable def discrIndex : CoroutineDiscr → Nat
  | .unresumed => 0
  | .returned => 1
  | .poisoned => 2
  | .suspended k => 3 + k

/-- Manual structural `DecidableEq` on `CoroutineDiscr` (no compiler-derived instance). -/
noncomputable def decEqCoroutineDiscr (a b : CoroutineDiscr) : Decidable (a = b) :=
  match a, b with
  | .unresumed, .unresumed => isTrue rfl
  | .returned, .returned => isTrue rfl
  | .poisoned, .poisoned => isTrue rfl
  | .suspended k1, .suspended k2 =>
    match decEqNat k1 k2 with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun heq => by cases heq; exact h rfl)
  | .unresumed, .returned => isFalse (fun h => by cases h)
  | .unresumed, .poisoned => isFalse (fun h => by cases h)
  | .unresumed, .suspended _ => isFalse (fun h => by cases h)
  | .returned, .unresumed => isFalse (fun h => by cases h)
  | .returned, .poisoned => isFalse (fun h => by cases h)
  | .returned, .suspended _ => isFalse (fun h => by cases h)
  | .poisoned, .unresumed => isFalse (fun h => by cases h)
  | .poisoned, .returned => isFalse (fun h => by cases h)
  | .poisoned, .suspended _ => isFalse (fun h => by cases h)
  | .suspended _, .unresumed => isFalse (fun h => by cases h)
  | .suspended _, .returned => isFalse (fun h => by cases h)
  | .suspended _, .poisoned => isFalse (fun h => by cases h)

/-- `LangItem` panic functions corresponding to `AssertKind::{ResumedAfterReturn, ResumedAfterPanic}`
(`compiler/rustc_middle/src/mir/terminator.rs:198-217`, `library/core/src/panicking.rs:198-206`). -/
inductive PanicLangItem where
  | panicCoroutineResumed
  | panicAsyncFnResumed
  | panicAsyncGenFnResumed
  | panicGenFnNone
  | panicCoroutineResumedPanic
  | panicAsyncFnResumedPanic
  | panicAsyncGenFnResumedPanic
  | panicGenFnNonePanic

noncomputable def resumedAfterReturnLangItem : CoroutineKind → PanicLangItem
  | .coroutine => .panicCoroutineResumed
  | .asyncFn => .panicAsyncFnResumed
  | .gen => .panicGenFnNone
  | .asyncGen => .panicAsyncGenFnResumed

noncomputable def resumedAfterPanicLangItem : CoroutineKind → PanicLangItem
  | .coroutine => .panicCoroutineResumedPanic
  | .asyncFn => .panicAsyncFnResumedPanic
  | .gen => .panicGenFnNonePanic
  | .asyncGen => .panicAsyncGenFnResumedPanic

/-- Body transition for active (`unresumed` or `suspended k`) coroutine states. -/
inductive BodyStep where
  | yieldNext (v : Nat) (nextSusp : Nat)
  | finishReturn (retVal : Nat)
  | unwindUserPanic (errCode : Nat)

abbrev CoroBody := CoroutineDiscr → BodyStep

/-- Observable outcome of a resume call (`Iterator::next`, `AsyncIterator::poll_next`,
`Future::poll`, or `Coroutine::resume`). -/
inductive ResumeOutcome where
  | yielded (v : Nat)
  | returnedNone
  | completed (v : Nat)
  | unwoundUserPanic (errCode : Nat)
  | panickedResumed (item : PanicLangItem)

/-- Execution of an active body step (shared by both unpatched and repaired dispatch):
unwinding always transitions the discriminant to `CoroutineArgs::POISONED`
(`generate_poison_block_and_redirect_unwinds_there`, `coroutine/mod.rs:845-874`),
and returning transitions to `CoroutineArgs::RETURNED` (`mod.rs:481-494`). -/
noncomputable def runActiveBody (kind : CoroutineKind) (body : CoroBody) (d : CoroutineDiscr) :
    ResumeOutcome × CoroutineDiscr :=
  match body d with
  | .yieldNext v k' => (.yielded v, .suspended k')
  | .finishReturn rv =>
    match kind with
    | .gen | .asyncGen => (.returnedNone, .returned)
    | .coroutine | .asyncFn => (.completed rv, .returned)
  | .unwindUserPanic code => (.unwoundUserPanic code, .poisoned)

/-- **Live Unpatched `rustc` `create_coroutine_resume_function` Dispatch**
(`coroutine/mod.rs:897-933` at `3ef0c22cd`/`342d74463`; `mod.rs:888-914` at `49d734536`;
`coroutine.rs:1243-1270` at `14210df0e` with default `-Zasync-panic=true`):
`RETURNED` routes `Gen`/`AsyncGen` to `insert_none_ret_block`, whereas `POISONED` routes
UNCONDITIONALLY to `insert_panic_block(..., ResumedAfterPanic(kind))`! -/
noncomputable def unpatchedResumeStep (kind : CoroutineKind) (body : CoroBody)
    (d : CoroutineDiscr) : ResumeOutcome × CoroutineDiscr :=
  match d with
  | .returned =>
    match kind with
    | .gen | .asyncGen => (.returnedNone, .returned)
    | .coroutine | .asyncFn => (.panickedResumed (resumedAfterReturnLangItem kind), .returned)
  | .poisoned =>
    (.panickedResumed (resumedAfterPanicLangItem kind), .poisoned)
  | .unresumed => runActiveBody kind body .unresumed
  | .suspended k => runActiveBody kind body (.suspended k)

/-- **Repaired `create_coroutine_resume_function` Dispatch**:
routes `POISONED` for `CoroutineDesugaring::Gen` to `insert_none_ret_block` (satisfying
built-in `FusedIterator` and `panicking.rs:205-206`'s stated invariant ``"`gen fn` should
just keep returning `None` after panicking"``), while leaving `Async`, `Coroutine`, and
`AsyncGen` post-panic panic behavior (and `RETURNED` fusing) intact. -/
noncomputable def repairedResumeStep (kind : CoroutineKind) (body : CoroBody)
    (d : CoroutineDiscr) : ResumeOutcome × CoroutineDiscr :=
  match d with
  | .returned =>
    match kind with
    | .gen | .asyncGen => (.returnedNone, .returned)
    | .coroutine | .asyncFn => (.panickedResumed (resumedAfterReturnLangItem kind), .returned)
  | .poisoned =>
    match kind with
    | .gen => (.returnedNone, .poisoned)
    | .coroutine | .asyncFn | .asyncGen =>
      (.panickedResumed (resumedAfterPanicLangItem kind), .poisoned)
  | .unresumed => runActiveBody kind body .unresumed
  | .suspended k => runActiveBody kind body (.suspended k)

/-- Drop shim dispatch (`coroutine/drop.rs:194-202`): both `RETURNED` and `POISONED`
fall through to the default no-op `Return` block (zero double-drop). -/
inductive DropAction where
  | dropUpvars
  | dropSuspendLocals (k : Nat)
  | noopReturn

noncomputable def coroDropStep : CoroutineDiscr → DropAction
  | .unresumed => .dropUpvars
  | .returned => .noopReturn
  | .poisoned => .noopReturn
  | .suspended k => .dropSuspendLocals k

noncomputable def replicateObs : Nat → ResumeOutcome → List ResumeOutcome
  | 0, _ => []
  | n + 1, x => x :: replicateObs n x

noncomputable def iteratedResume
    (dispatch : CoroutineKind → CoroBody → CoroutineDiscr → ResumeOutcome × CoroutineDiscr)
    (kind : CoroutineKind) (body : CoroBody) :
    Nat → CoroutineDiscr → List ResumeOutcome × CoroutineDiscr
  | 0, d => ([], d)
  | n + 1, d =>
    let step := dispatch kind body d
    let rest := iteratedResume dispatch kind body n step.2
    (step.1 :: rest.1, rest.2)

/-- **Main Theorem 3 (`repaired_gen_poisoned_fuses_to_none`):**
Under `repairedResumeStep`, a `gen` coroutine in EITHER `RETURNED` (`1`) OR `POISONED` (`2`):
1. Returns `.returnedNone` on every subsequent `Iterator::next` call across arbitrary `n : Nat`,
   preserving its terminal discriminant (full `FusedIterator` contract on `RETURNED ∪ POISONED`),
2. Drops with `.noopReturn` (zero double-drop), and
3. Preserves post-panic panicking for `Async` and `Coroutine` kinds unchanged. -/
theorem repaired_gen_poisoned_fuses_to_none (body : CoroBody) (d : CoroutineDiscr) (n : Nat)
    (hTerm : d = .returned ∨ d = .poisoned) :
    iteratedResume repairedResumeStep .gen body n d =
      (replicateObs n .returnedNone, d) ∧
    coroDropStep d = .noopReturn ∧
    repairedResumeStep .asyncFn body .poisoned =
      (.panickedResumed .panicAsyncFnResumedPanic, .poisoned) ∧
    repairedResumeStep .coroutine body .poisoned =
      (.panickedResumed .panicCoroutineResumedPanic, .poisoned) := by
  have hStep : repairedResumeStep .gen body d = (.returnedNone, d) := by
    cases hTerm with
    | inl hR => subst hR; rfl
    | inr hP => subst hP; rfl
  have hDrop : coroDropStep d = .noopReturn := by
    cases hTerm with
    | inl hR => subst hR; rfl
    | inr hP => subst hP; rfl
  refine ⟨?_, hDrop, rfl, rfl⟩
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold iteratedResume replicateObs
    rw [hStep]
    change (.returnedNone :: (iteratedResume repairedResumeStep .gen body k d).1,
            (iteratedResume repairedResumeStep .gen body k d).2) = _
    rw [ih]

/-! ## Section 5: Three Constructive Sharpness Counterexamples (`ce1`, `ce2`, `ce3`) -/

/-- Counterexample 1 program: segment `0` writes `x = 42`, forms `r = &x` (`.selfPtr base 0`),
yields `1`, transitions to `Suspend0 (3)`; segment `3` dereferences `r` and yields `*r`. -/
noncomputable def ce1SelfBorrowProg : FrameProgram
  | 0 => some {
      ops := [.writeScalar 0 42, .takeSelfPtr 1 0, .writeScalar 2 1]
      yieldLocal := 2
      nextDiscr := 3
    }
  | 3 => some {
      ops := [.derefSelfPtr 3 1]
      yieldLocal := 3
      nextDiscr := 1
    }
  | _ => none

noncomputable def ce1EmptyExt : ExtMem := fun _ => none
noncomputable def ce1InitFrame : CoroFrame :=
  { base := 1, discr := 0, locals := fun _ => none }

/-- **Counterexample 1 (`ce1_unpinned_next_with_self_borrow_dangles_after_swap`):**
If `E0626` (`NoSelfBorrowAcrossYield`) is bypassed on a `Movable` `gen` block taking unpinned
`&mut Self`, resuming without moving succeeds (`[obsYield 1, obsYield 42]`), whereas
relocating the suspended frame via `mem::swap` from `base = 1` to `base = 2` immediately
dangles the saved `.selfPtr 1 0` and triggers `.obsUbDanglingSelfRef` on the second `.next()`! -/
theorem ce1_unpinned_next_with_self_borrow_dangles_after_swap :
    let step1 := stepFrame ce1SelfBorrowProg ce1EmptyExt ce1InitFrame
    let unmovedStep2 := stepFrame ce1SelfBorrowProg ce1EmptyExt step1.2
    let swappedFrame := relocateFrame 2 step1.2
    let swappedStep2 := stepFrame ce1SelfBorrowProg ce1EmptyExt swappedFrame
    step1.1 = .obsYield 1 ∧
    unmovedStep2.1 = .obsYield 42 ∧
    swappedStep2.1 = .obsUbDanglingSelfRef ∧
    ¬ NoSelfBorrowFrame step1.2 := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro hNoSelf
  have h1 : (stepFrame ce1SelfBorrowProg ce1EmptyExt ce1InitFrame).2.locals 1 =
      some (.selfPtr 1 0) := rfl
  exact hNoSelf 1 (.selfPtr 1 0) h1

/-- Counterexample 2 (`#73137`): `a` (local 0) is initialized and yielded across yield 1,
then handed off via `assignMove 1 0` (`b = move a`) in a single MIR statement, then `b`
(local 1) is yielded across yield 2. `a` and `b` are NEVER simultaneously live in `primaryLive`,
yet ARE simultaneously live in `earlyLive` of `assignMove 1 0`! -/
noncomputable def ce2Handoff73137Trace : List CoroStmt :=
  [ .writeConst 0 7
  , .yieldLocal 0
  , .assignMove 1 0
  , .yieldLocal 1
  ]

noncomputable def emptyLive : LiveSet := fun _ => false
noncomputable def emptyUnpacked : UnpackedStore := fun _ => none
noncomputable def emptyPacked : PackedStore := fun _ => none

/-- Buggy conflict detector that checks ONLY `primaryLive` (after `assignMove` kills `src`),
missing the `#73137` conflict between `dst = 1` and `src = 0`. -/
noncomputable def BuggyPostPrimaryConflictsCover (conflicts : ConflictMatrix) (live : LiveSet) :
    List CoroStmt → Prop
  | [] => True
  | s :: rest =>
    (∀ a b, primaryLive live s a = true → primaryLive live s b = true → conflicts a b = true) ∧
    BuggyPostPrimaryConflictsCover conflicts (primaryLive live s) rest

/-- Diagonal-only conflict matrix (`a == b`): marks `0` and `1` as non-conflicting! -/
noncomputable def diagOnlyConflicts : ConflictMatrix := fun a b => natBeq a b

/-- Single-slot coloring mapping both `0` and `1` to slot `0` (257 B layout). -/
noncomputable def singleSlotColor : SlotColoring := fun _ => 0

/-- Two-slot coloring mapping `0 -> 0` and `1 -> 1` (513 B layout). -/
noncomputable def twoSlotColor : SlotColoring := fun l => l

/-- Full conflict matrix covering `earlyLive` (marks `(0, 1)` and `(1, 0)` conflicting). -/
noncomputable def earlyHandoffConflicts : ConflictMatrix := fun _ _ => true

/-- **Counterexample 2 (`ce2_stmt_lhs_rhs_missing_conflict_self_aliases_issue_73137`):**
For the `#73137` handoff trace `[writeConst 0 7, yieldLocal 0, assignMove 1 0, yieldLocal 1]`:
1. `diagOnlyConflicts` satisfies `BuggyPostPrimaryConflictsCover` (because `0` and `1` are
   never simultaneously live after primary effects!) and admits `singleSlotColor` (`0 ↦ 0, 1 ↦ 0`);
2. Executing under `singleSlotColor` immediately hits `.ubAliasingAssign` on `assignMove 1 0`
   (whereas unpacked execution succeeds with `.ok [7, 7]`);
3. Under `rustc`'s `EarlyConflictsCover` (`visit_after_early_statement_effect`), ANY matrix
   covering `ce2Handoff73137Trace` MUST satisfy `conflicts 1 0 = true`, forcing `color 1 ≠ color 0`
   (`twoSlotColor`, modeling `SZ_HANDOFF_73137 = 513 B`), under which packed execution equals
   `.ok [7, 7]`! -/
theorem ce2_stmt_lhs_rhs_missing_conflict_self_aliases_issue_73137 :
    BuggyPostPrimaryConflictsCover diagOnlyConflicts emptyLive ce2Handoff73137Trace ∧
    ValidSlotColoring diagOnlyConflicts singleSlotColor ∧
    execUnpacked emptyLive emptyUnpacked ce2Handoff73137Trace = .ok [7, 7] ∧
    execPacked singleSlotColor emptyLive emptyPacked ce2Handoff73137Trace = .ubAliasingAssign ∧
    (∀ conflicts color,
      EarlyConflictsCover conflicts emptyLive ce2Handoff73137Trace →
      ValidSlotColoring conflicts color →
      color 1 ≠ color 0) ∧
    execPacked twoSlotColor emptyLive emptyPacked ce2Handoff73137Trace = .ok [7, 7] := by
  refine ⟨?_, ?_, rfl, rfl, ?_, rfl⟩
  · -- BuggyPostPrimaryConflictsCover diagOnlyConflicts on ce2Handoff73137Trace
    unfold ce2Handoff73137Trace BuggyPostPrimaryConflictsCover
    refine ⟨?_, ?_, ?_, ?_, trivial⟩
    · intro a b ha hb
      cases a with
      | zero =>
        cases b with
        | zero => rfl
        | succ _ => cases hb
      | succ _ => cases ha
    · intro a b ha hb
      cases a with
      | zero =>
        cases b with
        | zero => rfl
        | succ _ => cases hb
      | succ _ => cases ha
    · intro a b ha hb
      cases a with
      | zero => cases ha
      | succ a' =>
        cases a' with
        | zero =>
          cases b with
          | zero => cases hb
          | succ b' =>
            cases b' with
            | zero => rfl
            | succ _ => cases hb
        | succ _ => cases ha
    · intro a b ha hb
      cases a with
      | zero => cases ha
      | succ a' =>
        cases a' with
        | zero =>
          cases b with
          | zero => cases hb
          | succ b' =>
            cases b' with
            | zero => rfl
            | succ _ => cases hb
        | succ _ => cases ha
  · -- ValidSlotColoring diagOnlyConflicts singleSlotColor
    intro a b hne hconf
    exact False.elim (hne (natBeq_eq_of_true hconf))
  · -- EarlyConflictsCover forces color 1 ≠ color 0
    intro conflicts color hCover hValid
    rcases hCover with ⟨_, _, hEarlyAssign, _, _⟩
    have hConf10 : conflicts 1 0 = true := hEarlyAssign 1 0 rfl rfl
    exact hValid 1 0 (fun h => by cases h) hConf10

/-- Concrete panicking `gen` body matching Part B (`yield 1; panic!("mid-gen-boom");`). -/
noncomputable def ce3PanickingGenBody : CoroBody
  | .unresumed => .yieldNext 1 0
  | .suspended 0 => .unwindUserPanic 42
  | _ => .finishReturn 0

/-- **Counterexample 3 (`ce3_unpatched_poisoned_arm_panics_instead_of_fusing`):**
On `ce3PanickingGenBody`:
1. Call 1 yields `1` and enters `Suspend0`;
2. Call 2 unwinds with user panic `42` and transitions discriminant to `POISONED` (`2`);
3. Call 3 under `unpatchedResumeStep .gen` PANICS with `.panicGenFnNonePanic`
   (emitting ``"`gen fn` should just keep returning `None` after panicking"``), whereas
   `repairedResumeStep .gen` cleanly fuses and returns `.returnedNone`! -/
theorem ce3_unpatched_poisoned_arm_panics_instead_of_fusing :
    let u1 := unpatchedResumeStep .gen ce3PanickingGenBody .unresumed
    let u2 := unpatchedResumeStep .gen ce3PanickingGenBody u1.2
    let u3 := unpatchedResumeStep .gen ce3PanickingGenBody u2.2
    let r3 := repairedResumeStep .gen ce3PanickingGenBody u2.2
    u1 = (.yielded 1, .suspended 0) ∧
    u2 = (.unwoundUserPanic 42, .poisoned) ∧
    u3 = (.panickedResumed .panicGenFnNonePanic, .poisoned) ∧
    r3 = (.returnedNone, .poisoned) ∧
    u3.1 ≠ r3.1 := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro h
  cases h

/-- Bonus: disjoint two-phase generator (`a` dropped via `storageDead 0` before `b` written)
admits `singleSlotColor` (`0 ↦ 0, 1 ↦ 0`, modeling `SZ_DISJOINT = 257 B`) with exact
semantic preservation! -/
noncomputable def disjointTwoPhaseTrace : List CoroStmt :=
  [ .writeConst 0 3
  , .yieldLocal 0
  , .storageDead 0
  , .writeConst 1 5
  , .yieldLocal 1
  ]

theorem disjoint_two_phase_coloring_fits_in_one_slot :
    EarlyConflictsCover diagOnlyConflicts emptyLive disjointTwoPhaseTrace ∧
    ValidSlotColoring diagOnlyConflicts singleSlotColor ∧
    execPacked singleSlotColor emptyLive emptyPacked disjointTwoPhaseTrace = .ok [3, 5] ∧
    execUnpacked emptyLive emptyUnpacked disjointTwoPhaseTrace = .ok [3, 5] := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · unfold disjointTwoPhaseTrace EarlyConflictsCover
    refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩
    · intro a b ha hb
      cases a with
      | zero =>
        cases b with
        | zero => rfl
        | succ _ => cases hb
      | succ _ => cases ha
    · intro a b ha hb
      cases a with
      | zero =>
        cases b with
        | zero => rfl
        | succ _ => cases hb
      | succ _ => cases ha
    · intro a b ha _
      cases a with
      | zero => cases ha
      | succ _ => cases ha
    · intro a b ha hb
      cases a with
      | zero => cases ha
      | succ a' =>
        cases a' with
        | zero =>
          cases b with
          | zero => cases hb
          | succ b' =>
            cases b' with
            | zero => rfl
            | succ _ => cases hb
        | succ _ => cases ha
    · intro a b ha hb
      cases a with
      | zero => cases ha
      | succ a' =>
        cases a' with
        | zero =>
          cases b with
          | zero => cases hb
          | succ b' =>
            cases b' with
            | zero => rfl
            | succ _ => cases hb
        | succ _ => cases ha
  · intro a b hne hconf
    exact False.elim (hne (natBeq_eq_of_true hconf))

/-! ## Section 6: Kernel Axiom Footprint Audit -/

#print axioms movable_gen_no_self_borrow_relocation_bisim
#print axioms movable_gen_mem_swap_interleaving_bisim
#print axioms conflict_free_slot_coloring_preserves_semantics
#print axioms disjoint_two_phase_coloring_fits_in_one_slot
#print axioms repaired_gen_poisoned_fuses_to_none
#print axioms ce1_unpinned_next_with_self_borrow_dangles_after_swap
#print axioms ce2_stmt_lhs_rhs_missing_conflict_self_aliases_issue_73137
#print axioms ce3_unpatched_poisoned_arm_panics_instead_of_fusing

end GenAsyncGenMovabilityAndFusingSoundness
