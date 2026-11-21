/-
  RemoveZstsSroaAndRefPropSoundness.lean

  Standalone Lean 4 (v4.34.1) mechanization of:
    1. `Layout` (`{ size : Nat, align : Nat }`), indirect zero-sized type (ZST)
       pointer access validity (`size == 0` skips allocation bounds/liveness
       resolution so `null` and `NonNull::dangling` at `addr % align == 0` are
       valid, while `addr % align != 0` and uninitialized pointer locals remain
       Undefined Behavior), `PassPolicy` / `MIRI_DEFAULT_ARGS` override
       precedence (`-Zmir-enable-passes=-CheckAlignment`), and `RemoveZsts`:
         - Forward codegen refinement (`removeZstsStmt_forward_codegen_refinement`)
         - Bidirectional equivalence for initialized `align == 1` indirect ZST
           accesses (`removeZsts_indirect_align_one_bidirectional_iff`) and for
           alignment/UB-preservation-guarded `removeZstsCertifiedStmt`
           (`removeZstsCertifiedStmt_bidirectional_equivalence`)
         - Constructive Counterexample 1
           (`ce1_remove_zsts_erases_misaligned_align64_zst_ub`)
    2. `ScalarReplacementOfAggregates` (`sroaFlattenStmt` / `sroaFlattenProg`)
       exact step and multi-statement bisimulation
       (`sroaFlattenStmt_exact_bisimulation`, `sroaFlattenProg_exact_bisimulation`),
       parametric in `deinitOnMove : Bool` (covering both upstream Miri `false`
       and Anneal `Trusted.MirSemantics`'s conservative `deinitMovedPlace = true`),
       under non-escaping struct eligibility (`!addressTaken && !isUnionOrEnum &&
       !isMaybeDangling && local > argCount`), plus `MaybeDangling` validity
       relaxation boundary (`sroa_maybeDangling_exclusion_necessary`).
    3. `ReferencePropagation` (`refPropSharedStmt` / `refPropMutStmt`) exact
       bidirectional simulation under place stability (`singleStorageLive`),
       target liveness (`!maybeStorageDead`), and all-or-nothing `&mut`
       uniqueness across copy-equivalence classes
       (`refProp_shared_exact_bisimulation`,
        `refProp_mut_all_or_nothing_exact_bisimulation`), plus constructive
       sharpness counterexamples:
         - Constructive Counterexample 2
           (`ce2_refprop_into_storage_dead_target_dangling_ub`)
         - Constructive Counterexample 3
           (`ce3_partial_mut_refprop_interleaving_aliasing_unsound`)

  Verification discipline:
    - 0 `sorry` / `admit`
    - 0 `Classical.choice`
    - 0 `omega` / `bv_decide` / `native_decide`
    - 0 `partial def` / `._unsafe_rec` / `axiom` / `@[extern]`
-/

set_option autoImplicit false

namespace RemoveZstsSroaAndRefPropSoundness

/-! ============================================================================
    Section 1. Layouts, Indirect ZST Pointer Validity, `PassPolicy` Precedence,
               and `RemoveZsts` Refinement vs. Bidirectional Equivalence
    ============================================================================ -/

/-- Byte size and byte alignment of a sized Rust type (`rustc_abi::LayoutData`). -/
structure Layout where
  size : Nat
  align : Nat
  deriving DecidableEq, Repr

namespace Layout

/-- True iff `size == 0` (`TyAndLayout::is_zst`). -/
def isZst (L : Layout) : Bool :=
  Nat.beq L.size 0

/-- Well-formedness of a concrete ABI layout: alignment is strictly positive. -/
def wf (L : Layout) : Prop :=
  0 < L.align

end Layout

/-- Boolean alignment check `align > 0 && addr % align == 0`, matching
`is_offset_misaligned` in `compiler/rustc_const_eval/src/interpret/memory.rs:589-597`. -/
def isAligned (addr align : Nat) : Bool :=
  !Nat.beq align 0 && Nat.beq (addr % align) 0

/-- Constructive proof (without `omega`) that every `addr : Nat` satisfies `addr % 1 = 0`. -/
theorem nat_mod_one_eq_zero (addr : Nat) : addr % 1 = 0 := by
  have hlt : addr % 1 < 1 := Nat.mod_lt addr (Nat.zero_lt_succ 0)
  match hrem : addr % 1 with
  | 0 => rfl
  | n + 1 =>
    rw [hrem] at hlt
    exact False.elim (Nat.not_lt_zero n (Nat.lt_of_succ_lt_succ hlt))

/-- Every address is 1-byte aligned (`isAligned addr 1 = true`). -/
theorem isAligned_one (addr : Nat) : isAligned addr 1 = true := by
  unfold isAligned
  rw [nat_mod_one_eq_zero addr]
  rfl

/-- `Nat.beq a b = true` iff `a = b`. -/
theorem nat_beq_eq_true_iff (a b : Nat) : (Nat.beq a b = true) ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => by subst h; exact Nat.beq_refl a⟩

/-- `Nat.beq a b = false` iff `a ≠ b`. -/
theorem nat_beq_eq_false_iff (a b : Nat) : (Nat.beq a b = false) ↔ a ≠ b := by
  constructor
  · intro h heq
    subst heq
    rw [Nat.beq_refl a] at h
    contradiction
  · intro hne
    cases h : Nat.beq a b with
    | false => rfl
    | true => exact False.elim (hne (Nat.eq_of_beq_eq_true h))

theorem bool_not_eq_true_to_eq_false {b : Bool} (h : (!b) = true) : b = false := by
  cases b with
  | false => rfl
  | true => contradiction

theorem not_beq_true_to_ne {a b : Nat} (h : (!Nat.beq a b) = true) : a ≠ b := by
  apply (nat_beq_eq_false_iff a b).mp
  cases hb : Nat.beq a b with
  | false => rfl
  | true => rw [hb] at h; contradiction

/-! ### 1.1 `PassPolicy` and `MIRI_DEFAULT_ARGS` Override Precedence -/

/-- Mirrors `rustc_mir_transform::pass_manager::PassPolicy` (`pass_manager.rs:88-100`). -/
inductive PassPolicy where
  | required
  | optional (enabledByDefault : Bool)
  deriving DecidableEq, Repr

/-- Mirrors `rustc_mir_transform::pass_manager::PassCtx` (`pass_manager.rs:132-165`). -/
structure PassCtx where
  mirOptLevel : Nat
  mirPreserveUb : Bool
  ubChecks : Bool
  mirEnablePasses : List (String × Bool)

/-- Mirrors `MirPass` identity and policy hook. -/
structure MirPassSpec where
  passName : String
  policy : PassCtx → PassPolicy

/-- Rightmost CLI flag wins, matching `mir_enable_passes.iter().rev().find_map(...)`
in `compiler/rustc_mir_transform/src/pass_manager.rs:261-268`. -/
noncomputable def lookupPassOverrideAux (target : String) :
    List (String × Bool) → Option Bool
  | [] => none
  | (nm, pol) :: rest =>
    if target == nm then some pol else lookupPassOverrideAux target rest

noncomputable def lookupPassOverride (target : String)
    (overrides : List (String × Bool)) : Option Bool :=
  lookupPassOverrideAux target overrides.reverse

/-- Mirrors `should_run_pass` (`pass_manager.rs:256-285`). -/
noncomputable def shouldRunPass (p : MirPassSpec) (ctx : PassCtx) : Bool :=
  match p.policy ctx with
  | .required => true
  | .optional enabledByDefault =>
    match lookupPassOverride p.passName ctx.mirEnablePasses with
    | some o => o
    | none => enabledByDefault

/-- Upstream `CheckAlignment` (`check_alignment.rs:15-18`):
`PassPolicy::optional(ctx.ub_checks())`. -/
def checkAlignmentPass : MirPassSpec :=
  { passName := "CheckAlignment"
  , policy := fun ctx => .optional ctx.ubChecks }

/-- Upstream `RemovePlaceMention` (`remove_place_mention.rs:12-14`):
`PassPolicy::optional(!ctx.opts.unstable_opts.mir_preserve_ub)`. -/
def removePlaceMentionPass : MirPassSpec :=
  { passName := "RemovePlaceMention"
  , policy := fun ctx => .optional (!ctx.mirPreserveUb) }

/-- Upstream `RemoveZsts` (`remove_zsts.rs:12-14`):
`PassPolicy::optional(ctx.mir_opt_level() >= 1)` — ignores `mirPreserveUb`. -/
def removeZstsPass : MirPassSpec :=
  { passName := "RemoveZsts"
  , policy := fun ctx => .optional (Nat.ble 1 ctx.mirOptLevel) }

/-- Default pass overrides spliced at `argv[1..1]` by `MIRI_DEFAULT_ARGS`
(`src/tools/miri/src/lib.rs:200-218`): disables `CheckAlignment`, `CheckNull`,
`CheckEnums`, `ReferencePropagation`, and `GVN`, while omitting `RemoveZsts`. -/
def miriDefaultPassOverrides : List (String × Bool) :=
  [ ("CheckAlignment", false)
  , ("CheckNull", false)
  , ("CheckEnums", false)
  , ("ReferencePropagation", false)
  , ("GVN", false) ]

/-- Effective `PassCtx` inside Miri when user supplies `mirOptLevel`, `ubChecks`,
and `userOverrides` after `MIRI_DEFAULT_ARGS`. -/
def miriPassCtx (mirOptLevel : Nat) (ubChecks : Bool)
    (userOverrides : List (String × Bool)) : PassCtx :=
  { mirOptLevel := mirOptLevel
  , mirPreserveUb := true
  , ubChecks := ubChecks
  , mirEnablePasses := miriDefaultPassOverrides ++ userOverrides }

/-- Theorem: Under `MIRI_DEFAULT_ARGS` (without an explicit `+CheckAlignment`),
`CheckAlignment` is suppressed for EVERY `ubChecks` value (including `-Zub-checks=yes`),
`RemovePlaceMention` stays suppressed via `mirPreserveUb = true`, yet `RemoveZsts`
runs unconditionally as soon as `mirOptLevel >= 1`. -/
theorem miri_default_args_suppress_checkAlignment_and_run_removeZsts
    (ubChecks : Bool) :
    shouldRunPass checkAlignmentPass (miriPassCtx 1 ubChecks []) = false ∧
    shouldRunPass removePlaceMentionPass (miriPassCtx 1 ubChecks []) = false ∧
    shouldRunPass removeZstsPass (miriPassCtx 1 ubChecks []) = true :=
  ⟨rfl, rfl, rfl⟩

/-- Theorem: Appending `-Zmir-enable-passes=+CheckAlignment` after `MIRI_DEFAULT_ARGS`
overrides the earlier `-CheckAlignment` entry via reverse-list precedence. -/
theorem miri_force_enable_checkAlignment_restores_pass :
    shouldRunPass checkAlignmentPass
      (miriPassCtx 1 true [("CheckAlignment", true)]) = true :=
  rfl

/-! ### 1.2 Indirect ZST Pointer Semantics and `RemoveZsts` Soundness Boundary -/

abbrev LocalId := Nat
abbrev AllocId := Nat

/-- Pointer value: optional provenance `AllocId` (`none` for integer/null/dangling
pointers) paired with byte address `addr`. -/
structure PtrVal where
  alloc : Option AllocId
  addr : Nat
  deriving DecidableEq, Repr

/-- Allocation metadata in abstract memory. -/
structure AllocEntry where
  live : Bool
  writable : Bool
  size : Nat
  deriving DecidableEq, Repr

/-- First-order types for the Section 1 ZST / pointer MIR fragment. -/
inductive ZstMirTy where
  | zst (align : Nat)
  | scalar
  | rawPtr (pointee : ZstMirTy)

namespace ZstMirTy

noncomputable def beq : ZstMirTy → ZstMirTy → Bool
  | .zst a, .zst b => Nat.beq a b
  | .scalar, .scalar => true
  | .rawPtr a, .rawPtr b => beq a b
  | _, _ => false

noncomputable instance : BEq ZstMirTy := ⟨beq⟩

theorem beq_refl (t : ZstMirTy) : beq t t = true := by
  induction t with
  | zst a => exact Nat.beq_refl a
  | scalar => rfl
  | rawPtr _ ih => exact ih

theorem eq_of_beq_true {t1 t2 : ZstMirTy} (h : beq t1 t2 = true) : t1 = t2 := by
  induction t1 generalizing t2 with
  | zst a =>
    cases t2 with
    | zst b => exact congrArg ZstMirTy.zst (Nat.eq_of_beq_eq_true h)
    | scalar | rawPtr _ => contradiction
  | scalar =>
    cases t2 with
    | scalar => rfl
    | zst _ | rawPtr _ => contradiction
  | rawPtr _ ih =>
    cases t2 with
    | rawPtr inner2 => exact congrArg ZstMirTy.rawPtr (ih h)
    | zst _ | scalar => contradiction

instance : LawfulBEq ZstMirTy where
  eq_of_beq := eq_of_beq_true
  rfl := beq_refl _

noncomputable def layout : ZstMirTy → Layout
  | .zst a => { size := 0, align := a }
  | .scalar => { size := 8, align := 8 }
  | .rawPtr _ => { size := 8, align := 8 }

noncomputable def isKnownZst (ty : ZstMirTy) : Bool :=
  (ty.layout).isZst

end ZstMirTy

/-- Runtime values in local slots and memory. -/
inductive ZstVal where
  | zstVal
  | scalarVal (n : Nat)
  | ptrVal (pv : PtrVal)
  deriving DecidableEq, Repr

/-- Local slot state: dead, live-uninitialized (`live none`), or live-initialized
(`live (some v)`), matching `Trusted.MirSemantics.LocalSlot`. -/
inductive LocalSlot (V : Type) where
  | dead
  | live (val : Option V)
  deriving DecidableEq, Repr

/-- Post-`StorageLive` / post-`Move` slot state (`Trusted.MirSemantics.liveUninitSlot`):
inhabited ZST slots remain inhabited (`live (some .zstVal)`), while non-ZST slots
become uninitialized (`live none`). -/
noncomputable def liveUninitZstSlot (ty : ZstMirTy) : LocalSlot ZstVal :=
  if ty.isKnownZst then .live (some .zstVal) else .live none

/-- Modeled Undefined Behavior / fault kinds in Section 1. -/
inductive ZstUbKind where
  | deadLocalAccess (l : LocalId)
  | uninitOperandRead (l : LocalId)
  | danglingOrOobAccess (pv : PtrVal) (size : Nat)
  | misalignedAccess (addr : Nat) (requiredAlign : Nat)
  | failedAlignmentAssert (addr : Nat) (requiredAlign : Nat)
  | illTypedProgram
  deriving DecidableEq, Repr

/-- Execution outcome of a statement or block. -/
inductive ExecOutcome (S E : Type) where
  | ok (state : S)
  | ub (err : E)
  deriving DecidableEq, Repr

/-- Memory and local-frame state for Section 1. -/
structure ZstState where
  locals : LocalId → LocalSlot ZstVal
  memVars : AllocId → Option (AllocEntry × ZstVal)

/-- Functional update on `LocalId → α`. -/
def updateFn {α : Type} (f : LocalId → α) (k : LocalId) (v : α) : LocalId → α :=
  fun x => if Nat.beq x k then v else f x

theorem updateFn_self {α : Type} (f : LocalId → α) (k : LocalId) (v : α) :
    updateFn f k v k = v := by
  unfold updateFn
  rw [Nat.beq_refl k]
  rfl

theorem updateFn_ne {α : Type} (f : LocalId → α) (k x : LocalId) (v : α)
    (hne : x ≠ k) : updateFn f k v x = f x := by
  unfold updateFn
  have hfalse : Nat.beq x k = false := (nat_beq_eq_false_iff x k).mpr hne
  rw [hfalse]
  rfl

/-- Allocation dereference and bounds check (`check_and_deref_ptr` in
`compiler/rustc_const_eval/src/interpret/memory.rs:519-566` and
`Miri.Memory.Access.checkAndDerefPtr`):
  - When `L.size == 0`, returns `.ok ()` without resolving `pv.alloc`.
  - When `L.size > 0`, requires a live allocation of sufficient size (and
    `writable` on stores). -/
def checkDerefAlloc (mem : AllocId → Option (AllocEntry × ZstVal))
    (pv : PtrVal) (L : Layout) (isWrite : Bool) : ExecOutcome Unit ZstUbKind :=
  if Nat.beq L.size 0 then
    .ok ()
  else
    match pv.alloc with
    | none => .ub (.danglingOrOobAccess pv L.size)
    | some aid =>
      match mem aid with
      | none => .ub (.danglingOrOobAccess pv L.size)
      | some (entry, _) =>
        if entry.live && (!isWrite || entry.writable) && Nat.ble L.size entry.size then
          .ok ()
        else
          .ub (.danglingOrOobAccess pv L.size)

/-- Complete indirect load/store pointer check (`get_place_alloc` /
`get_place_alloc_mut` in `place.rs:541-572` + `is_ptr_misaligned` in
`memory.rs:579-624`):
  1. Checks bounds/allocation liveness (`checkDerefAlloc`, skipped when `size == 0`),
  2. Checks pointer alignment `isAligned pv.addr L.align` EVEN WHEN `size == 0`! -/
def checkIndirectLoadStore (mem : AllocId → Option (AllocEntry × ZstVal))
    (pv : PtrVal) (L : Layout) (isWrite : Bool) : ExecOutcome Unit ZstUbKind :=
  match checkDerefAlloc mem pv L isWrite with
  | .ub err => .ub err
  | .ok () =>
    if isAligned pv.addr L.align then
      .ok ()
    else
      .ub (.misalignedAccess pv.addr L.align)

/-- Theorem: Dereferencing `null` (`addr = 0, alloc = none`) at unit layout
`⟨0, 1⟩` is valid for both loads and stores (`rc = 0` in Miri). -/
theorem null_unit_load_and_store_valid
    (mem : AllocId → Option (AllocEntry × ZstVal)) (isWrite : Bool) :
    checkIndirectLoadStore mem { alloc := none, addr := 0 } { size := 0, align := 1 } isWrite =
      .ok () :=
  rfl

/-- Theorem: Dereferencing `NonNull::<Aligned64Zst>::dangling()` (`addr = 64,
alloc = none`) at layout `⟨0, 64⟩` is valid (`64 % 64 == 0` and `size == 0`
skips allocation lookup). -/
theorem dangling_aligned64_zst_load_and_store_valid
    (mem : AllocId → Option (AllocEntry × ZstVal)) (isWrite : Bool) :
    checkIndirectLoadStore mem { alloc := none, addr := 64 } { size := 0, align := 64 } isWrite =
      .ok () :=
  rfl

/-- Theorem: For ANY initialized `PtrVal` `pv` (arbitrary `alloc` and arbitrary
`addr`, including odd misaligned addresses), indirect access at ZST layout
`⟨0, 1⟩` (`align = 1`) NEVER faults. -/
theorem any_init_ptr_zst_align_one_valid
    (mem : AllocId → Option (AllocEntry × ZstVal)) (pv : PtrVal) (isWrite : Bool) :
    checkIndirectLoadStore mem pv { size := 0, align := 1 } isWrite = .ok () := by
  unfold checkIndirectLoadStore checkDerefAlloc
  simp [isAligned_one pv.addr]

/-- Places in Section 1: direct local `l` or raw-pointer deref `*p`. -/
inductive ZstPlace where
  | direct (l : LocalId)
  | deref (ptrLocal : LocalId)
  deriving DecidableEq, Repr

/-- Operands in Section 1. -/
inductive ZstOperand where
  | copy (p : ZstPlace)
  | move (p : ZstPlace)
  | constZst (ty : ZstMirTy)
  | constScalar (n : Nat)
  | constPtr (pv : PtrVal) (pointee : ZstMirTy)

/-- Statements in Section 1. -/
inductive ZstStmt where
  | assign (dst : ZstPlace) (op : ZstOperand)
  | placeMention (p : ZstPlace)
  | storageLive (l : LocalId)
  | storageDead (l : LocalId)
  | checkAlignAssert (ptrLocal : LocalId) (requiredAlign : Nat)
  | nop

/-- Static type of a `ZstPlace`. -/
noncomputable def placeTy (env : LocalId → ZstMirTy) : ZstPlace → Option ZstMirTy
  | .direct l => some (env l)
  | .deref p =>
    match env p with
    | .rawPtr inner => some inner
    | _ => none

/-- Static type of a `ZstOperand`. -/
noncomputable def operandTy (env : LocalId → ZstMirTy) : ZstOperand → Option ZstMirTy
  | .copy p | .move p => placeTy env p
  | .constZst ty => some ty
  | .constScalar _ => some .scalar
  | .constPtr _ pointee => some (.rawPtr pointee)

/-- Read an initialized `PtrVal` from `ptrLocal`, faulting with UB if `ptrLocal`
is `.dead` or uninitialized (`.live none`). -/
def readPtrLocal (st : ZstState) (ptrLocal : LocalId) : ExecOutcome PtrVal ZstUbKind :=
  match st.locals ptrLocal with
  | .dead => .ub (.deadLocalAccess ptrLocal)
  | .live none => .ub (.uninitOperandRead ptrLocal)
  | .live (some (.ptrVal pv)) => .ok pv
  | .live (some _) => .ub .illTypedProgram

/-- Evaluate a `ZstOperand` with configurable `deinitOnMove : Bool`. -/
noncomputable def evalZstOperand (env : LocalId → ZstMirTy) (deinitOnMove : Bool)
    (st : ZstState) (op : ZstOperand) : ExecOutcome (ZstVal × ZstState) ZstUbKind :=
  match op with
  | .constZst ty =>
    if ty.isKnownZst then .ok (.zstVal, st) else .ub .illTypedProgram
  | .constScalar n => .ok (.scalarVal n, st)
  | .constPtr pv _ => .ok (.ptrVal pv, st)
  | .copy (.direct l) =>
    match st.locals l with
    | .dead => .ub (.deadLocalAccess l)
    | .live none => .ub (.uninitOperandRead l)
    | .live (some v) => .ok (v, st)
  | .move (.direct l) =>
    match st.locals l with
    | .dead => .ub (.deadLocalAccess l)
    | .live none => .ub (.uninitOperandRead l)
    | .live (some v) =>
      let st' :=
        if deinitOnMove then
          { st with locals := updateFn st.locals l (liveUninitZstSlot (env l)) }
        else st
      .ok (v, st')
  | .copy (.deref p) | .move (.deref p) =>
    match env p with
    | .rawPtr innerTy =>
      match readPtrLocal st p with
      | .ub err => .ub err
      | .ok pv =>
        match checkIndirectLoadStore st.memVars pv innerTy.layout false with
        | .ub err => .ub err
        | .ok () =>
          if innerTy.isKnownZst then
            .ok (.zstVal, st)
          else
            match pv.alloc with
            | none => .ub (.danglingOrOobAccess pv innerTy.layout.size)
            | some aid =>
              match st.memVars aid with
              | some (_, v) => .ok (v, st)
              | none => .ub (.danglingOrOobAccess pv innerTy.layout.size)
    | _ => .ub .illTypedProgram

/-- Execute a `ZstStmt` in lockstep with `rustc_const_eval::interpret` and
`Trusted.MirSemantics.evalStatement` (checking static assignment type agreement
`operandTy env op == placeTy env dst` upfront). -/
noncomputable def execZstStmt (env : LocalId → ZstMirTy) (deinitOnMove : Bool)
    (st : ZstState) (stmt : ZstStmt) : ExecOutcome ZstState ZstUbKind :=
  match stmt with
  | .nop => .ok st
  | .storageLive l =>
    .ok { st with locals := updateFn st.locals l (liveUninitZstSlot (env l)) }
  | .storageDead l =>
    .ok { st with locals := updateFn st.locals l .dead }
  | .placeMention (.direct _) => .ok st
  | .placeMention (.deref p) =>
    match env p with
    | .rawPtr _ =>
      match readPtrLocal st p with
      | .ub err => .ub err
      | .ok _ => .ok st
    | _ => .ub .illTypedProgram
  | .checkAlignAssert p reqAlign =>
    match readPtrLocal st p with
    | .ub err => .ub err
    | .ok pv =>
      if isAligned pv.addr reqAlign then .ok st
      else .ub (.failedAlignmentAssert pv.addr reqAlign)
  | .assign (.direct dst) op =>
    if !(operandTy env op == some (env dst)) then
      .ub .illTypedProgram
    else
      match evalZstOperand env deinitOnMove st op with
      | .ub err => .ub err
      | .ok (v, st1) =>
        match st1.locals dst with
        | .dead => .ub (.deadLocalAccess dst)
        | .live _ =>
          .ok { st1 with locals := updateFn st1.locals dst (.live (some v)) }
  | .assign (.deref p) op =>
    match env p with
    | .rawPtr innerTy =>
      if !(operandTy env op == some innerTy) then
        .ub .illTypedProgram
      else
        match evalZstOperand env deinitOnMove st op with
        | .ub err => .ub err
        | .ok (v, st1) =>
          match readPtrLocal st1 p with
          | .ub err => .ub err
          | .ok pv =>
            match checkIndirectLoadStore st1.memVars pv innerTy.layout true with
            | .ub err => .ub err
            | .ok () =>
              if innerTy.isKnownZst then
                .ok st1
              else
                match pv.alloc with
                | none => .ub (.danglingOrOobAccess pv innerTy.layout.size)
                | some aid =>
                  match st1.memVars aid with
                  | some (entry, _) =>
                    let mem' := fun a => if Nat.beq a aid then some (entry, v) else st1.memVars a
                    .ok { st1 with memVars := mem' }
                  | none => .ub (.danglingOrOobAccess pv innerTy.layout.size)
    | _ => .ub .illTypedProgram

/-- Upstream `RemoveZsts` operand rewrite (`remove_zsts.rs:108-116` at
`c7d5ba59d`): rewrites ANY `Copy`/`Move` operand of known ZST type (including
indirect `copy (*p)`) to `ConstValue::ZeroSized`. -/
noncomputable def removeZstsOperand (env : LocalId → ZstMirTy)
    (op : ZstOperand) : ZstOperand :=
  match op with
  | .constZst _ | .constScalar _ | .constPtr _ _ => op
  | .copy p | .move p =>
    match placeTy env p with
    | some ty => if ty.isKnownZst then .constZst ty else op
    | none => op

/-- Upstream `RemoveZsts` statement rewrite (`remove_zsts.rs:118-152` at
`c7d5ba59d`):
  - `StorageLive(l)` / `StorageDead(l)` on ZST local `l` -> `.nop`
  - Indirect ZST `Assign((*p, op))` and `PlaceMention(*p)` -> `.nop`
  - Direct `Assign(dst, op)` -> `Assign(dst, removeZstsOperand env op)` -/
noncomputable def removeZstsStmt (env : LocalId → ZstMirTy)
    (stmt : ZstStmt) : ZstStmt :=
  match stmt with
  | .storageLive l | .storageDead l =>
    if (env l).isKnownZst then .nop else stmt
  | .assign (.deref p) op =>
    match placeTy env (.deref p) with
    | some ty =>
      if ty.isKnownZst then .nop
      else .assign (.deref p) (removeZstsOperand env op)
    | none => .assign (.deref p) (removeZstsOperand env op)
  | .assign (.direct dst) op =>
    .assign (.direct dst) (removeZstsOperand env op)
  | .placeMention (.deref p) =>
    match placeTy env (.deref p) with
    | some ty => if ty.isKnownZst then .nop else stmt
    | none => stmt
  | .placeMention (.direct _) | .checkAlignAssert _ _ | .nop => stmt

/-- `removeZstsOperand` preserves static `operandTy`. -/
theorem removeZstsOperand_ty_eq (env : LocalId → ZstMirTy) (op : ZstOperand) :
    operandTy env (removeZstsOperand env op) = operandTy env op := by
  cases op with
  | constZst _ | constScalar _ | constPtr _ _ => rfl
  | copy p | move p =>
    dsimp [removeZstsOperand, operandTy]
    cases hp : placeTy env p with
    | none => dsimp [operandTy]; exact hp
    | some ty =>
      dsimp
      cases ty.isKnownZst with
      | false => dsimp [operandTy]; exact hp
      | true => dsimp [operandTy]

/-- Observational refinement relation modulo ZST local liveness. -/
def ZstObsRel (env : LocalId → ZstMirTy) (src tgt : ZstState) : Prop :=
  src.memVars = tgt.memVars ∧
  (∀ l, (env l).isKnownZst = false → src.locals l = tgt.locals l) ∧
  (∀ l, (env l).isKnownZst = true →
    (∀ v, src.locals l = .live (some v) → v = .zstVal) ∧
    tgt.locals l = .live (some .zstVal))

/-- Evaluating ANY ZST-typed operand under `ZstObsRel` yields `.zstVal` and
evaluates in `tgt` under `removeZstsOperand` without mutating `tgt`. -/
theorem evalZstOperand_zst_ty_inv
    (env : LocalId → ZstMirTy) (deinitOnMove : Bool)
    (src tgt : ZstState) (op : ZstOperand) (ty : ZstMirTy)
    (v : ZstVal) (src' : ZstState)
    (hrel : ZstObsRel env src tgt)
    (hopTy : operandTy env op = some ty)
    (hz : ty.isKnownZst = true)
    (hev : evalZstOperand env deinitOnMove src op = .ok (v, src')) :
    v = .zstVal ∧
    evalZstOperand env deinitOnMove tgt (removeZstsOperand env op) = .ok (.zstVal, tgt) ∧
    ZstObsRel env src' tgt := by
  rcases hrel with ⟨hmem, hnonZst, hzst⟩
  cases op with
  | constZst t =>
    dsimp [operandTy] at hopTy
    injection hopTy with hteq; subst hteq
    dsimp [evalZstOperand, removeZstsOperand] at hev ⊢
    rw [hz] at hev ⊢
    injection hev with hpair_; injection hpair_ with hv hs; subst hv hs
    exact ⟨rfl, rfl, ⟨hmem, hnonZst, hzst⟩⟩
  | constScalar _ =>
    dsimp [operandTy] at hopTy
    injection hopTy with hteq; subst hteq
    contradiction
  | constPtr _ _ =>
    dsimp [operandTy] at hopTy
    injection hopTy with hteq; subst hteq
    contradiction
  | copy p =>
    cases p with
    | direct l =>
      dsimp [operandTy, placeTy] at hopTy
      injection hopTy with hteq
      have hzl : (env l).isKnownZst = true := by rw [hteq]; exact hz
      dsimp [removeZstsOperand, placeTy]
      rw [hzl]
      dsimp [evalZstOperand] at hev ⊢
      rw [hzl]
      cases hsl : src.locals l with
      | dead => rw [hsl] at hev; contradiction
      | live opt =>
        cases opt with
        | none => rw [hsl] at hev; contradiction
        | some val =>
          rw [hsl] at hev
          injection hev with hpair_; injection hpair_ with hv hs; subst hv hs
          have hvz : val = .zstVal := (hzst l hzl).1 val hsl
          exact ⟨hvz, rfl, ⟨hmem, hnonZst, hzst⟩⟩
    | deref p =>
      dsimp [operandTy, placeTy] at hopTy
      dsimp [removeZstsOperand, placeTy]
      dsimp [evalZstOperand] at hev
      cases hep : env p with
      | zst _ => rw [hep] at hopTy; contradiction
      | scalar => rw [hep] at hopTy; contradiction
      | rawPtr innerTy =>
        rw [hep] at hopTy hev
        injection hopTy with hteq; subst hteq
        dsimp at hev ⊢
        rw [hz]
        dsimp [evalZstOperand]
        rw [hz]
        cases hrp : readPtrLocal src p with
        | ub _ => rw [hrp] at hev; contradiction
        | ok pv =>
          rw [hrp] at hev; dsimp at hev
          cases hchk : checkIndirectLoadStore src.memVars pv innerTy.layout false with
          | ub _ => rw [hchk] at hev; contradiction
          | ok u =>
            cases u
            rw [hchk] at hev; dsimp at hev
            rw [hz] at hev; dsimp at hev
            injection hev with hpair_; injection hpair_ with hv hs; subst hv hs
            exact ⟨rfl, rfl, ⟨hmem, hnonZst, hzst⟩⟩
  | move p =>
    cases p with
    | direct l =>
      dsimp [operandTy, placeTy] at hopTy
      injection hopTy with hteq
      have hzl : (env l).isKnownZst = true := by rw [hteq]; exact hz
      dsimp [removeZstsOperand, placeTy]
      rw [hzl]
      dsimp [evalZstOperand] at hev ⊢
      rw [hzl]
      cases hsl : src.locals l with
      | dead => rw [hsl] at hev; contradiction
      | live opt =>
        cases opt with
        | none => rw [hsl] at hev; contradiction
        | some val =>
          rw [hsl] at hev
          injection hev with hpair_; injection hpair_ with hv hs; subst hv hs
          have hvz : val = .zstVal := (hzst l hzl).1 val hsl
          cases deinitOnMove with
          | false => exact ⟨hvz, rfl, ⟨hmem, hnonZst, hzst⟩⟩
          | true =>
            dsimp
            refine ⟨hvz, rfl, ⟨hmem, ?_, ?_⟩⟩
            · intro k hk
              dsimp
              have hkl : k ≠ l := fun heq => by subst heq; rw [hzl] at hk; contradiction
              rw [updateFn_ne _ l k _ hkl]; exact hnonZst k hk
            · intro k hk
              dsimp
              cases hkl : Nat.beq k l with
              | true =>
                have heq : k = l := Nat.eq_of_beq_eq_true hkl
                subst heq
                refine ⟨?_, (hzst k hk).2⟩
                intro v' hv'
                rw [updateFn_self] at hv'
                unfold liveUninitZstSlot at hv'
                rw [hzl] at hv'
                injection hv' with h1; injection h1 with h2; exact h2.symm
              | false =>
                have hne : k ≠ l := (nat_beq_eq_false_iff k l).mp hkl
                rw [updateFn_ne _ l k _ hne]; exact hzst k hk
    | deref p =>
      dsimp [operandTy, placeTy] at hopTy
      dsimp [removeZstsOperand, placeTy]
      dsimp [evalZstOperand] at hev
      cases hep : env p with
      | zst _ => rw [hep] at hopTy; contradiction
      | scalar => rw [hep] at hopTy; contradiction
      | rawPtr innerTy =>
        rw [hep] at hopTy hev
        injection hopTy with hteq; subst hteq
        dsimp at hev ⊢
        rw [hz]
        dsimp [evalZstOperand]
        rw [hz]
        cases hrp : readPtrLocal src p with
        | ub _ => rw [hrp] at hev; contradiction
        | ok pv =>
          rw [hrp] at hev; dsimp at hev
          cases hchk : checkIndirectLoadStore src.memVars pv innerTy.layout false with
          | ub _ => rw [hchk] at hev; contradiction
          | ok u =>
            cases u
            rw [hchk] at hev; dsimp at hev
            rw [hz] at hev; dsimp at hev
            injection hev with hpair_; injection hpair_ with hv hs; subst hv hs
            exact ⟨rfl, rfl, ⟨hmem, hnonZst, hzst⟩⟩

/-- Evaluating a non-ZST-typed operand under `ZstObsRel` evaluates identically
in `tgt` under `removeZstsOperand`. -/
theorem evalZstOperand_nonZst_ty_inv
    (env : LocalId → ZstMirTy) (deinitOnMove : Bool)
    (src tgt : ZstState) (op : ZstOperand) (ty : ZstMirTy)
    (v : ZstVal) (src' : ZstState)
    (hrel : ZstObsRel env src tgt)
    (hopTy : operandTy env op = some ty)
    (hnz : ty.isKnownZst = false)
    (hev : evalZstOperand env deinitOnMove src op = .ok (v, src')) :
    ∃ tgt', evalZstOperand env deinitOnMove tgt (removeZstsOperand env op) = .ok (v, tgt') ∧
      ZstObsRel env src' tgt' := by
  rcases hrel with ⟨hmem, hnonZst, hzst⟩
  cases op with
  | constZst _ =>
    dsimp [evalZstOperand] at hev
    dsimp [operandTy] at hopTy
    injection hopTy with hteq; subst hteq
    rw [hnz] at hev; contradiction
  | constScalar _ =>
    injection hev with hpair_; injection hpair_ with hv hs; subst hv hs
    exact ⟨tgt, rfl, ⟨hmem, hnonZst, hzst⟩⟩
  | constPtr _ _ =>
    injection hev with hpair_; injection hpair_ with hv hs; subst hv hs
    exact ⟨tgt, rfl, ⟨hmem, hnonZst, hzst⟩⟩
  | copy p =>
    cases p with
    | direct l =>
      dsimp [operandTy, placeTy] at hopTy
      injection hopTy with hteq
      have hnl : (env l).isKnownZst = false := by rw [hteq]; exact hnz
      dsimp [removeZstsOperand, placeTy]
      rw [hnl]
      dsimp [evalZstOperand] at hev ⊢
      rw [← hnonZst l hnl]
      cases hsl : src.locals l with
      | dead => rw [hsl] at hev; contradiction
      | live opt =>
        cases opt with
        | none => rw [hsl] at hev; contradiction
        | some val =>
          rw [hsl] at hev
          injection hev with hpair_; injection hpair_ with hv hs; subst hv hs
          exact ⟨tgt, rfl, ⟨hmem, hnonZst, hzst⟩⟩
    | deref p =>
      dsimp [operandTy, placeTy] at hopTy
      dsimp [removeZstsOperand, placeTy]
      dsimp [evalZstOperand] at hev
      cases hep : env p with
      | zst _ => rw [hep] at hopTy; contradiction
      | scalar => rw [hep] at hopTy; contradiction
      | rawPtr innerTy =>
        rw [hep] at hopTy hev
        injection hopTy with hteq; subst hteq
        dsimp
        rw [hnz]
        dsimp [evalZstOperand]
        rw [hep]
        have hpNonZst : (env p).isKnownZst = false := by rw [hep]; rfl
        have hrpEq : readPtrLocal tgt p = readPtrLocal src p := by
          unfold readPtrLocal; rw [← hnonZst p hpNonZst]
        rw [hrpEq, ← hmem]
        cases hrp : readPtrLocal src p with
        | ub _ => rw [hrp] at hev; contradiction
        | ok pv =>
          rw [hrp] at hev; dsimp at hev ⊢
          cases hchk : checkIndirectLoadStore src.memVars pv innerTy.layout false with
          | ub _ => rw [hchk] at hev; contradiction
          | ok u =>
            cases u
            rw [hchk] at hev; dsimp at hev ⊢
            rw [hnz] at hev ⊢; dsimp at hev ⊢
            cases hpa : pv.alloc with
            | none => rw [hpa] at hev; contradiction
            | some aid =>
              rw [hpa] at hev; dsimp at hev ⊢
              cases hma : src.memVars aid with
              | none => rw [hma] at hev; contradiction
              | some ma =>
                rcases ma with ⟨_, _⟩
                rw [hma] at hev; dsimp at hev ⊢
                injection hev with hpair_; injection hpair_ with hv hs; subst hv hs
                exact ⟨tgt, rfl, ⟨hmem, hnonZst, hzst⟩⟩
  | move p =>
    cases p with
    | direct l =>
      dsimp [operandTy, placeTy] at hopTy
      injection hopTy with hteq
      have hnl : (env l).isKnownZst = false := by rw [hteq]; exact hnz
      dsimp [removeZstsOperand, placeTy]
      rw [hnl]
      dsimp [evalZstOperand] at hev ⊢
      rw [← hnonZst l hnl]
      cases hsl : src.locals l with
      | dead => rw [hsl] at hev; contradiction
      | live opt =>
        cases opt with
        | none => rw [hsl] at hev; contradiction
        | some val =>
          rw [hsl] at hev
          injection hev with hpair_; injection hpair_ with hv hs; subst hv hs
          cases deinitOnMove with
          | false => exact ⟨tgt, rfl, ⟨hmem, hnonZst, hzst⟩⟩
          | true =>
            dsimp
            refine ⟨_, rfl, ⟨hmem, ?_, ?_⟩⟩
            · intro k hk
              dsimp
              cases hkl : Nat.beq k l with
              | true =>
                have heq : k = l := Nat.eq_of_beq_eq_true hkl
                subst heq; rw [updateFn_self, updateFn_self]
              | false =>
                have hne : k ≠ l := (nat_beq_eq_false_iff k l).mp hkl
                rw [updateFn_ne _ l k _ hne, updateFn_ne _ l k _ hne]
                exact hnonZst k hk
            · intro k hk
              dsimp
              have hne : k ≠ l := fun heq => by subst heq; rw [hnl] at hk; contradiction
              rw [updateFn_ne _ l k _ hne, updateFn_ne _ l k _ hne]
              exact hzst k hk
    | deref p =>
      dsimp [operandTy, placeTy] at hopTy
      dsimp [removeZstsOperand, placeTy]
      dsimp [evalZstOperand] at hev
      cases hep : env p with
      | zst _ => rw [hep] at hopTy; contradiction
      | scalar => rw [hep] at hopTy; contradiction
      | rawPtr innerTy =>
        rw [hep] at hopTy hev
        injection hopTy with hteq; subst hteq
        dsimp
        rw [hnz]
        dsimp [evalZstOperand]
        rw [hep]
        have hpNonZst : (env p).isKnownZst = false := by rw [hep]; rfl
        have hrpEq : readPtrLocal tgt p = readPtrLocal src p := by
          unfold readPtrLocal; rw [← hnonZst p hpNonZst]
        rw [hrpEq, ← hmem]
        cases hrp : readPtrLocal src p with
        | ub _ => rw [hrp] at hev; contradiction
        | ok pv =>
          rw [hrp] at hev; dsimp at hev ⊢
          cases hchk : checkIndirectLoadStore src.memVars pv innerTy.layout false with
          | ub _ => rw [hchk] at hev; contradiction
          | ok u =>
            cases u
            rw [hchk] at hev; dsimp at hev ⊢
            rw [hnz] at hev ⊢; dsimp at hev ⊢
            cases hpa : pv.alloc with
            | none => rw [hpa] at hev; contradiction
            | some aid =>
              rw [hpa] at hev; dsimp at hev ⊢
              cases hma : src.memVars aid with
              | none => rw [hma] at hev; contradiction
              | some ma =>
                rcases ma with ⟨_, _⟩
                rw [hma] at hev; dsimp at hev ⊢
                injection hev with hpair_; injection hpair_ with hv hs; subst hv hs
                exact ⟨tgt, rfl, ⟨hmem, hnonZst, hzst⟩⟩

/-- Helper lemma: `readPtrLocal` is preserved from `src` to `tgt` under `ZstObsRel`. -/
theorem readPtrLocal_preserved_by_obsRel
    (env : LocalId → ZstMirTy) (src tgt : ZstState) (p : LocalId) (pv : PtrVal)
    (hrel : ZstObsRel env src tgt)
    (hrp : readPtrLocal src p = .ok pv) :
    readPtrLocal tgt p = .ok pv := by
  rcases hrel with ⟨_, hnonZst, hzst⟩
  have hpNonZst : (env p).isKnownZst = false := by
    cases hzp : (env p).isKnownZst with
    | false => rfl
    | true =>
      unfold readPtrLocal at hrp
      cases hsl : src.locals p with
      | dead => rw [hsl] at hrp; contradiction
      | live opt =>
        cases opt with
        | none => rw [hsl] at hrp; contradiction
        | some val =>
          have hvz := (hzst p hzp).1 val hsl
          subst hvz
          rw [hsl] at hrp; contradiction
  unfold readPtrLocal at hrp ⊢
  rw [← hnonZst p hpNonZst]
  exact hrp

/-- **Main Theorem 1a (`removeZstsStmt_forward_codegen_refinement`):**
Unconditional `removeZstsStmt` (matching `rustc`'s `RemoveZsts`) is a sound
forward UB-refining transformation across ALL layouts (`align == 1` and
`align > 1`): whenever `src` steps without UB (`execZstStmt = .ok src'`),
`removeZstsStmt` also steps without UB (`execZstStmt = .ok tgt'`) and preserves
exact memory and non-ZST local state (`ZstObsRel`). -/
theorem removeZstsStmt_forward_codegen_refinement
    (env : LocalId → ZstMirTy) (deinitOnMove : Bool)
    (src tgt : ZstState) (stmt : ZstStmt) (src' : ZstState)
    (hrel : ZstObsRel env src tgt)
    (hexec : execZstStmt env deinitOnMove src stmt = .ok src') :
    ∃ tgt', execZstStmt env deinitOnMove tgt (removeZstsStmt env stmt) = .ok tgt' ∧
      ZstObsRel env src' tgt' := by
  rcases hrel with ⟨hmem, hnonZst, hzst⟩
  cases stmt with
  | nop =>
    injection hexec with hs; subst hs
    exact ⟨tgt, rfl, ⟨hmem, hnonZst, hzst⟩⟩
  | storageLive l =>
    dsimp [execZstStmt] at hexec
    injection hexec with hs; subst hs
    dsimp [removeZstsStmt]
    cases hz : (env l).isKnownZst with
    | true =>
      refine ⟨tgt, rfl, ⟨hmem, ?_, ?_⟩⟩
      · intro k hk
        dsimp
        have hne : k ≠ l := fun heq => by subst heq; rw [hz] at hk; contradiction
        rw [updateFn_ne _ l k _ hne]; exact hnonZst k hk
      · intro k hk
        dsimp
        cases hkl : Nat.beq k l with
        | true =>
          have heq : k = l := Nat.eq_of_beq_eq_true hkl
          subst heq
          refine ⟨?_, (hzst k hk).2⟩
          intro v hv
          rw [updateFn_self] at hv
          unfold liveUninitZstSlot at hv
          rw [hz] at hv
          injection hv with h1; injection h1 with h2; exact h2.symm
        | false =>
          have hne : k ≠ l := (nat_beq_eq_false_iff k l).mp hkl
          rw [updateFn_ne _ l k _ hne]; exact hzst k hk
    | false =>
      refine ⟨_, rfl, ⟨hmem, ?_, ?_⟩⟩
      · intro k hk
        dsimp
        cases hkl : Nat.beq k l with
        | true =>
          have heq : k = l := Nat.eq_of_beq_eq_true hkl
          subst heq; rw [updateFn_self, updateFn_self]
        | false =>
          have hne : k ≠ l := (nat_beq_eq_false_iff k l).mp hkl
          rw [updateFn_ne _ l k _ hne, updateFn_ne _ l k _ hne]; exact hnonZst k hk
      · intro k hk
        dsimp
        have hne : k ≠ l := fun heq => by subst heq; rw [hz] at hk; contradiction
        rw [updateFn_ne _ l k _ hne, updateFn_ne _ l k _ hne]; exact hzst k hk
  | storageDead l =>
    dsimp [execZstStmt] at hexec
    injection hexec with hs; subst hs
    dsimp [removeZstsStmt]
    cases hz : (env l).isKnownZst with
    | true =>
      refine ⟨tgt, rfl, ⟨hmem, ?_, ?_⟩⟩
      · intro k hk
        dsimp
        have hne : k ≠ l := fun heq => by subst heq; rw [hz] at hk; contradiction
        rw [updateFn_ne _ l k _ hne]; exact hnonZst k hk
      · intro k hk
        dsimp
        cases hkl : Nat.beq k l with
        | true =>
          have heq : k = l := Nat.eq_of_beq_eq_true hkl
          subst heq
          refine ⟨?_, (hzst k hk).2⟩
          intro v hv; rw [updateFn_self] at hv; contradiction
        | false =>
          have hne : k ≠ l := (nat_beq_eq_false_iff k l).mp hkl
          rw [updateFn_ne _ l k _ hne]; exact hzst k hk
    | false =>
      refine ⟨_, rfl, ⟨hmem, ?_, ?_⟩⟩
      · intro k hk
        dsimp
        cases hkl : Nat.beq k l with
        | true =>
          have heq : k = l := Nat.eq_of_beq_eq_true hkl
          subst heq; rw [updateFn_self, updateFn_self]
        | false =>
          have hne : k ≠ l := (nat_beq_eq_false_iff k l).mp hkl
          rw [updateFn_ne _ l k _ hne, updateFn_ne _ l k _ hne]; exact hnonZst k hk
      · intro k hk
        dsimp
        have hne : k ≠ l := fun heq => by subst heq; rw [hz] at hk; contradiction
        rw [updateFn_ne _ l k _ hne, updateFn_ne _ l k _ hne]; exact hzst k hk
  | placeMention p =>
    cases p with
    | direct _ =>
      dsimp [execZstStmt] at hexec
      injection hexec with hs; subst hs
      exact ⟨tgt, rfl, ⟨hmem, hnonZst, hzst⟩⟩
    | deref p =>
      dsimp [execZstStmt] at hexec
      dsimp [removeZstsStmt, placeTy]
      cases hep : env p with
      | zst _ => rw [hep] at hexec; contradiction
      | scalar => rw [hep] at hexec; contradiction
      | rawPtr innerTy =>
        rw [hep] at hexec
        dsimp
        cases hrp : readPtrLocal src p with
        | ub _ => rw [hrp] at hexec; contradiction
        | ok pv =>
          rw [hrp] at hexec
          injection hexec with hs; subst hs
          cases hz : innerTy.isKnownZst with
          | true => exact ⟨tgt, rfl, ⟨hmem, hnonZst, hzst⟩⟩
          | false =>
            dsimp [execZstStmt]
            rw [hep, readPtrLocal_preserved_by_obsRel env src tgt p pv ⟨hmem, hnonZst, hzst⟩ hrp]
            exact ⟨tgt, rfl, ⟨hmem, hnonZst, hzst⟩⟩
  | checkAlignAssert p reqAlign =>
    dsimp [removeZstsStmt]
    dsimp [execZstStmt] at hexec ⊢
    cases hrp : readPtrLocal src p with
    | ub _ => rw [hrp] at hexec; contradiction
    | ok pv =>
      rw [hrp] at hexec
      rw [readPtrLocal_preserved_by_obsRel env src tgt p pv ⟨hmem, hnonZst, hzst⟩ hrp]
      dsimp at hexec ⊢
      cases hal : isAligned pv.addr reqAlign with
      | false => rw [hal] at hexec; contradiction
      | true =>
        rw [hal] at hexec; dsimp at hexec ⊢
        injection hexec with hs; subst hs
        exact ⟨tgt, rfl, ⟨hmem, hnonZst, hzst⟩⟩
  | assign dst op =>
    cases dst with
    | direct d =>
      dsimp [removeZstsStmt]
      dsimp [execZstStmt] at hexec ⊢
      rw [removeZstsOperand_ty_eq env op]
      cases htyCheck : (operandTy env op == some (env d)) with
      | false => rw [htyCheck] at hexec; contradiction
      | true =>
        rw [htyCheck] at hexec; dsimp at hexec ⊢
        have hopTy : operandTy env op = some (env d) := eq_of_beq htyCheck
        cases hev : evalZstOperand env deinitOnMove src op with
        | ub _ => rw [hev] at hexec; contradiction
        | ok pair =>
          rcases pair with ⟨v, src1⟩
          rw [hev] at hexec; dsimp at hexec
          cases hzd : (env d).isKnownZst with
          | true =>
            rcases evalZstOperand_zst_ty_inv env deinitOnMove src tgt op (env d) v src1
                ⟨hmem, hnonZst, hzst⟩ hopTy hzd hev with ⟨hvz, hevTgt, hrel1⟩
            subst hvz
            rw [hevTgt]
            rcases hrel1 with ⟨hmem1, hnonZst1, hzst1⟩
            cases hsd : src1.locals d with
            | dead => rw [hsd] at hexec; contradiction
            | live _ =>
              rw [hsd] at hexec
              injection hexec with hs; subst hs
              dsimp
              rw [(hzst1 d hzd).2]
              refine ⟨_, rfl, ⟨hmem1, ?_, ?_⟩⟩
              · intro k hk
                dsimp
                have hne : k ≠ d := fun heq => by subst heq; rw [hzd] at hk; contradiction
                rw [updateFn_ne _ d k _ hne, updateFn_ne _ d k _ hne]; exact hnonZst1 k hk
              · intro k hk
                dsimp
                cases hkd : Nat.beq k d with
                | true =>
                  have heq : k = d := Nat.eq_of_beq_eq_true hkd
                  subst heq; rw [updateFn_self, updateFn_self]
                  exact ⟨fun _ hv' => by injection hv' with h1; injection h1 with h2; exact h2.symm, rfl⟩
                | false =>
                  have hne : k ≠ d := (nat_beq_eq_false_iff k d).mp hkd
                  rw [updateFn_ne _ d k _ hne, updateFn_ne _ d k _ hne]; exact hzst1 k hk
          | false =>
            rcases evalZstOperand_nonZst_ty_inv env deinitOnMove src tgt op (env d) v src1
                ⟨hmem, hnonZst, hzst⟩ hopTy hzd hev with ⟨tgt1, hevTgt, hrel1⟩
            rw [hevTgt]
            rcases hrel1 with ⟨hmem1, hnonZst1, hzst1⟩
            cases hsd : src1.locals d with
            | dead => rw [hsd] at hexec; contradiction
            | live _ =>
              rw [hsd] at hexec
              injection hexec with hs; subst hs
              dsimp
              rw [← hnonZst1 d hzd, hsd]
              refine ⟨_, rfl, ⟨hmem1, ?_, ?_⟩⟩
              · intro k hk
                dsimp
                cases hkd : Nat.beq k d with
                | true =>
                  have heq : k = d := Nat.eq_of_beq_eq_true hkd
                  subst heq; rw [updateFn_self, updateFn_self]
                | false =>
                  have hne : k ≠ d := (nat_beq_eq_false_iff k d).mp hkd
                  rw [updateFn_ne _ d k _ hne, updateFn_ne _ d k _ hne]; exact hnonZst1 k hk
              · intro k hk
                dsimp
                have hne : k ≠ d := fun heq => by subst heq; rw [hzd] at hk; contradiction
                rw [updateFn_ne _ d k _ hne, updateFn_ne _ d k _ hne]; exact hzst1 k hk
    | deref p =>
      dsimp [removeZstsStmt, placeTy]
      dsimp [execZstStmt] at hexec
      cases hep : env p with
      | zst _ => rw [hep] at hexec; contradiction
      | scalar => rw [hep] at hexec; contradiction
      | rawPtr innerTy =>
        rw [hep] at hexec; dsimp at hexec ⊢
        cases htyCheck : (operandTy env op == some innerTy) with
        | false => rw [htyCheck] at hexec; contradiction
        | true =>
          rw [htyCheck] at hexec; dsimp at hexec
          have hopTy : operandTy env op = some innerTy := eq_of_beq htyCheck
          cases hev : evalZstOperand env deinitOnMove src op with
          | ub _ => rw [hev] at hexec; contradiction
          | ok pair =>
            rcases pair with ⟨v, src1⟩
            cases hz : innerTy.isKnownZst with
            | true =>
              rcases evalZstOperand_zst_ty_inv env deinitOnMove src tgt op innerTy v src1
                  ⟨hmem, hnonZst, hzst⟩ hopTy hz hev with ⟨_, _, hrel1⟩
              rw [hev] at hexec; dsimp at hexec
              cases hrp : readPtrLocal src1 p with
              | ub _ => rw [hrp] at hexec; contradiction
              | ok pv =>
                rw [hrp] at hexec; dsimp at hexec
                cases hchk : checkIndirectLoadStore src1.memVars pv innerTy.layout true with
                | ub _ => rw [hchk] at hexec; contradiction
                | ok u =>
                  cases u
                  rw [hchk] at hexec; dsimp at hexec; rw [hz] at hexec; dsimp at hexec
                  injection hexec with hs; subst hs
                  exact ⟨tgt, rfl, hrel1⟩
            | false =>
              rcases evalZstOperand_nonZst_ty_inv env deinitOnMove src tgt op innerTy v src1
                  ⟨hmem, hnonZst, hzst⟩ hopTy hz hev with ⟨tgt1, hevTgt, hrel1⟩
              dsimp [execZstStmt]
              rw [hep]; dsimp; rw [removeZstsOperand_ty_eq env op, htyCheck]
              dsimp
              rw [hevTgt]; dsimp
              rw [hev] at hexec; dsimp at hexec
              cases hrp : readPtrLocal src1 p with
              | ub _ => rw [hrp] at hexec; contradiction
              | ok pv =>
                rw [hrp] at hexec; dsimp at hexec
                rw [readPtrLocal_preserved_by_obsRel env src1 tgt1 p pv hrel1 hrp]; dsimp
                rcases hrel1 with ⟨hmem1, hnonZst1, hzst1⟩
                rw [← hmem1]
                cases hchk : checkIndirectLoadStore src1.memVars pv innerTy.layout true with
                | ub _ => rw [hchk] at hexec; contradiction
                | ok u =>
                  cases u
                  rw [hchk] at hexec; dsimp at hexec ⊢
                  rw [hz] at hexec ⊢; dsimp at hexec ⊢
                  cases hpa : pv.alloc with
                  | none => rw [hpa] at hexec; contradiction
                  | some aid =>
                    rw [hpa] at hexec; dsimp at hexec ⊢
                    cases hma : src1.memVars aid with
                    | none => rw [hma] at hexec; contradiction
                    | some ma =>
                      rcases ma with ⟨_, _⟩
                      rw [hma] at hexec; dsimp at hexec ⊢
                      injection hexec with hs; subst hs
                      exact ⟨_, rfl, ⟨rfl, hnonZst1, hzst1⟩⟩

/-- **Main Theorem 1b (`removeZsts_indirect_align_one_bidirectional_iff`):**
At alignment `1` (`innerTy = .zst 1`, e.g., `()`, `[u8; 0]`, `PhantomData<u8>`),
whenever the pointer local `p` holds an initialized `PtrVal` `pv` (including
`null`, `dangling`, or arbitrary odd integer addresses) and destination `dst` is
live, indirect ZST reads and writes NEVER fault, so `removeZstsStmt` satisfies
exact bidirectional outcome equality (`align == 1` erases ZERO UB on initialized
pointers). -/
theorem removeZsts_indirect_align_one_bidirectional_iff
    (env : LocalId → ZstMirTy) (deinitOnMove : Bool)
    (st : ZstState) (p dst : LocalId) (pv : PtrVal)
    (hep : env p = .rawPtr (.zst 1))
    (hed : env dst = .zst 1)
    (hpInit : st.locals p = .live (some (.ptrVal pv))) :
    execZstStmt env deinitOnMove st (.assign (.deref p) (.constZst (.zst 1))) =
      execZstStmt env deinitOnMove st
        (removeZstsStmt env (.assign (.deref p) (.constZst (.zst 1)))) ∧
    execZstStmt env deinitOnMove st (.assign (.direct dst) (.copy (.deref p))) =
      execZstStmt env deinitOnMove st
        (removeZstsStmt env (.assign (.direct dst) (.copy (.deref p)))) := by
  constructor
  · dsimp [removeZstsStmt, placeTy]
    rw [hep]
    dsimp [ZstMirTy.isKnownZst, ZstMirTy.layout, Layout.isZst]
    dsimp [execZstStmt, operandTy]
    rw [hep]
    dsimp [evalZstOperand, ZstMirTy.isKnownZst, ZstMirTy.layout, Layout.isZst, readPtrLocal]
    rw [hpInit]
    dsimp
    rw [any_init_ptr_zst_align_one_valid st.memVars pv true]
  · dsimp [removeZstsStmt, removeZstsOperand, placeTy]
    rw [hep]
    dsimp [ZstMirTy.isKnownZst, ZstMirTy.layout, Layout.isZst]
    dsimp [execZstStmt, operandTy, placeTy]
    simp only [hep, hed]
    dsimp [evalZstOperand, ZstMirTy.isKnownZst, ZstMirTy.layout, Layout.isZst, readPtrLocal]
    rw [hep, hpInit]
    dsimp
    rw [any_init_ptr_zst_align_one_valid st.memVars pv false]

/-- Certified / UB-preserving variant of `RemoveZsts` (`removeZstsCertifiedStmt`):
  - When `preserveUb = true` (Miri mode), leaves indirect ZST reads/writes and
    `StorageLive`/`StorageDead` intact so pointer initialization and
    `addr % align == 0` checks execute faithfully.
  - When `preserveUb = false`, folds an indirect ZST operation ONLY when
    `ty.layout.align == 1` AND `ptrConfirmedInit p = true`. -/
noncomputable def removeZstsCertifiedOperand (env : LocalId → ZstMirTy)
    (preserveUb : Bool) (ptrConfirmedInit : LocalId → Bool)
    (op : ZstOperand) : ZstOperand :=
  if preserveUb then op
  else
    match op with
    | .copy (.deref p) | .move (.deref p) =>
      match placeTy env (.deref p) with
      | some ty =>
        if ty.isKnownZst && Nat.beq ty.layout.align 1 && ptrConfirmedInit p then
          .constZst ty
        else op
      | none => op
    | _ => op

noncomputable def removeZstsCertifiedStmt (env : LocalId → ZstMirTy)
    (preserveUb : Bool) (ptrConfirmedInit : LocalId → Bool)
    (stmt : ZstStmt) : ZstStmt :=
  if preserveUb then stmt
  else
    match stmt with
    | .assign (.deref p) op =>
      let op' := removeZstsCertifiedOperand env false ptrConfirmedInit op
      match placeTy env (.deref p), op' with
      | some ty, .constZst cty =>
        if (cty == ty) && ty.isKnownZst && Nat.beq ty.layout.align 1 && ptrConfirmedInit p then
          .nop
        else .assign (.deref p) op'
      | _, _ => .assign (.deref p) op'
    | .assign (.direct dst) op =>
      .assign (.direct dst) (removeZstsCertifiedOperand env false ptrConfirmedInit op)
    | .placeMention (.deref p) =>
      match placeTy env (.deref p) with
      | some ty =>
        if ty.isKnownZst && ptrConfirmedInit p then .nop else stmt
      | none => stmt
    | _ => stmt

/-- Soundness of the `ptrConfirmedInit` static analysis witness. -/
def PtrInitSound (st : ZstState) (ptrConfirmedInit : LocalId → Bool) : Prop :=
  ∀ p, ptrConfirmedInit p = true → ∃ pv, st.locals p = .live (some (.ptrVal pv))

theorem removeZstsCertifiedOperand_exact_eq
    (env : LocalId → ZstMirTy) (deinitOnMove : Bool)
    (preserveUb : Bool) (ptrConfirmedInit : LocalId → Bool)
    (st : ZstState) (op : ZstOperand)
    (hinit : PtrInitSound st ptrConfirmedInit) :
    evalZstOperand env deinitOnMove st
      (removeZstsCertifiedOperand env preserveUb ptrConfirmedInit op) =
    evalZstOperand env deinitOnMove st op ∧
    operandTy env (removeZstsCertifiedOperand env preserveUb ptrConfirmedInit op) =
      operandTy env op := by
  cases preserveUb with
  | true => exact ⟨rfl, rfl⟩
  | false =>
    cases op with
    | constZst _ | constScalar _ | constPtr _ _ => exact ⟨rfl, rfl⟩
    | copy q =>
      cases q with
      | direct _ => exact ⟨rfl, rfl⟩
      | deref p =>
        dsimp [removeZstsCertifiedOperand, placeTy]
        cases hep : env p with
        | zst _ | scalar => exact ⟨rfl, rfl⟩
        | rawPtr innerTy =>
          dsimp
          cases hcond : (innerTy.isKnownZst && Nat.beq innerTy.layout.align 1 && ptrConfirmedInit p) with
          | false => exact ⟨rfl, rfl⟩
          | true =>
            have h12 : (innerTy.isKnownZst && Nat.beq innerTy.layout.align 1) = true ∧
                ptrConfirmedInit p = true := Bool.and_eq_true_iff.mp hcond
            have h1 : innerTy.isKnownZst = true ∧ Nat.beq innerTy.layout.align 1 = true :=
              Bool.and_eq_true_iff.mp h12.1
            rcases hinit p h12.2 with ⟨pv, hpSlot⟩
            have hsz0 : Nat.beq innerTy.layout.size 0 = true := h1.1
            have hal1 : innerTy.layout.align = 1 := Nat.eq_of_beq_eq_true h1.2
            constructor
            · dsimp [evalZstOperand]
              rw [h1.1, hep]
              dsimp [readPtrLocal]
              rw [hpSlot]
              dsimp [checkIndirectLoadStore, checkDerefAlloc]
              rw [hsz0]
              dsimp
              rw [hal1, isAligned_one pv.addr, h1.1]; rfl
            · dsimp [operandTy, placeTy]; rw [hep]
    | move q =>
      cases q with
      | direct _ => exact ⟨rfl, rfl⟩
      | deref p =>
        dsimp [removeZstsCertifiedOperand, placeTy]
        cases hep : env p with
        | zst _ | scalar => exact ⟨rfl, rfl⟩
        | rawPtr innerTy =>
          dsimp
          cases hcond : (innerTy.isKnownZst && Nat.beq innerTy.layout.align 1 && ptrConfirmedInit p) with
          | false => exact ⟨rfl, rfl⟩
          | true =>
            have h12 : (innerTy.isKnownZst && Nat.beq innerTy.layout.align 1) = true ∧
                ptrConfirmedInit p = true := Bool.and_eq_true_iff.mp hcond
            have h1 : innerTy.isKnownZst = true ∧ Nat.beq innerTy.layout.align 1 = true :=
              Bool.and_eq_true_iff.mp h12.1
            rcases hinit p h12.2 with ⟨pv, hpSlot⟩
            have hsz0 : Nat.beq innerTy.layout.size 0 = true := h1.1
            have hal1 : innerTy.layout.align = 1 := Nat.eq_of_beq_eq_true h1.2
            constructor
            · dsimp [evalZstOperand]
              rw [h1.1, hep]
              dsimp [readPtrLocal]
              rw [hpSlot]
              dsimp [checkIndirectLoadStore, checkDerefAlloc]
              rw [hsz0]
              dsimp
              rw [hal1, isAligned_one pv.addr, h1.1]; rfl
            · dsimp [operandTy, placeTy]; rw [hep]

/-- **Main Theorem 1c (`removeZstsCertifiedStmt_bidirectional_equivalence`):**
Whenever `preserveUb = true` (Miri mode) OR `PtrInitSound` holds (certified
codegen mode), `removeZstsCertifiedStmt` preserves **exact** operational
execution AND **exact** UB faults across ALL alignments (`align == 1` and
`align > 1`, initialized and uninitialized pointers). -/
theorem removeZstsCertifiedStmt_bidirectional_equivalence
    (env : LocalId → ZstMirTy) (deinitOnMove : Bool)
    (preserveUb : Bool) (ptrConfirmedInit : LocalId → Bool)
    (st : ZstState) (stmt : ZstStmt)
    (hinit : PtrInitSound st ptrConfirmedInit) :
    execZstStmt env deinitOnMove st
      (removeZstsCertifiedStmt env preserveUb ptrConfirmedInit stmt) =
    execZstStmt env deinitOnMove st stmt := by
  cases preserveUb with
  | true => rfl
  | false =>
    cases stmt with
    | nop | storageLive _ | storageDead _ | checkAlignAssert _ _ => rfl
    | placeMention q =>
      cases q with
      | direct _ => rfl
      | deref p =>
        dsimp [removeZstsCertifiedStmt, placeTy]
        cases hep : env p with
        | zst _ | scalar => rfl
        | rawPtr innerTy =>
          dsimp
          cases hcond : (innerTy.isKnownZst && ptrConfirmedInit p) with
          | false => rfl
          | true =>
            have hpOk : ptrConfirmedInit p = true := (Bool.and_eq_true_iff.mp hcond).2
            rcases hinit p hpOk with ⟨pv, hpSlot⟩
            dsimp [execZstStmt, readPtrLocal]
            rw [hep, hpSlot]
    | assign dst op =>
      have ⟨hopEv, hopTy⟩ :=
        removeZstsCertifiedOperand_exact_eq env deinitOnMove false ptrConfirmedInit st op hinit
      cases dst with
      | direct _ =>
        dsimp [removeZstsCertifiedStmt, execZstStmt]
        rw [hopTy, hopEv]
      | deref p =>
        dsimp [removeZstsCertifiedStmt, placeTy]
        cases hep : env p with
        | zst _ | scalar =>
          dsimp [execZstStmt]; rw [hep]
        | rawPtr innerTy =>
          dsimp
          cases hop' : removeZstsCertifiedOperand env false ptrConfirmedInit op with
          | copy _ | move _ | constScalar _ | constPtr _ _ =>
            dsimp [execZstStmt]
            rw [hep, ← hop', hopTy, hopEv]
          | constZst cty =>
            dsimp
            cases hcond : ((cty == innerTy) && innerTy.isKnownZst &&
                Nat.beq innerTy.layout.align 1 && ptrConfirmedInit p) with
            | false =>
              dsimp [execZstStmt]
              rw [hep, ← hop', hopTy, hopEv]
            | true =>
              have h123 : ((cty == innerTy) && innerTy.isKnownZst &&
                  Nat.beq innerTy.layout.align 1) = true ∧ ptrConfirmedInit p = true :=
                Bool.and_eq_true_iff.mp hcond
              have h12 : ((cty == innerTy) && innerTy.isKnownZst) = true ∧
                  Nat.beq innerTy.layout.align 1 = true :=
                Bool.and_eq_true_iff.mp h123.1
              have h1 : (cty == innerTy) = true ∧ innerTy.isKnownZst = true :=
                Bool.and_eq_true_iff.mp h12.1
              have hctyEq : cty = innerTy := eq_of_beq h1.1
              subst hctyEq
              rcases hinit p h123.2 with ⟨pv, hpSlot⟩
              have hsz0 : Nat.beq cty.layout.size 0 = true := h1.2
              have hal1 : cty.layout.align = 1 := Nat.eq_of_beq_eq_true h12.2
              have hopTySome : operandTy env op = some cty := by
                rw [← hopTy, hop']; rfl
              have hopEvZst : evalZstOperand env deinitOnMove st op = .ok (.zstVal, st) := by
                rw [← hopEv, hop']
                dsimp [evalZstOperand]
                rw [h1.2]; rfl
              dsimp [execZstStmt]
              rw [hep, hopTySome]
              simp [hopEvZst, readPtrLocal, hpSlot, checkIndirectLoadStore,
                checkDerefAlloc, hsz0, hal1, isAligned_one pv.addr, h1.2]

/-! ### 1.3 Sharpness Counterexample 1: `RemoveZsts` Erases Misaligned `Aligned64Zst` UB -/

def ce1Env : LocalId → ZstMirTy :=
  fun l =>
    if Nat.beq l 1 then .rawPtr (.zst 64)
    else .zst 64

def ce1MisalignedPtr : PtrVal := { alloc := some 0, addr := 1 }

def ce1InitState : ZstState :=
  { locals := fun l =>
      if Nat.beq l 1 then .live (some (.ptrVal ce1MisalignedPtr))
      else .live (some .zstVal)
  , memVars := fun a =>
      if Nat.beq a 0 then some ({ live := true, writable := true, size := 128 }, .zstVal)
      else none }

def ce1WriteStmt : ZstStmt := .assign (.deref 1) (.constZst (.zst 64))
def ce1ReadStmt  : ZstStmt := .assign (.direct 2) (.copy (.deref 1))

/-- **Counterexample 1 (`ce1_remove_zsts_erases_misaligned_align64_zst_ub`):**
On `#[repr(align(64))] struct Aligned64Zst` (`Layout = ⟨0, 64⟩`) with pointer
`misaligned` at address `1` (`1 % 64 = 1 ≠ 0`):
  1. Pre-`RemoveZsts` execution of `*misaligned = Aligned64Zst` (`ce1WriteStmt`)
     AND `let v = *misaligned` (`ce1ReadStmt`) both fault with
     `.ub (.misalignedAccess 1 64)`.
  2. Post-`RemoveZsts` execution of BOTH statements succeeds with `.ok` (`0` UB),
     while `removeZstsCertifiedStmt` (both with `preserveUb = true` and even with
     `preserveUb = false`) preserves `.ub (.misalignedAccess 1 64)`. -/
theorem ce1_remove_zsts_erases_misaligned_align64_zst_ub :
    execZstStmt ce1Env false ce1InitState ce1WriteStmt =
      .ub (.misalignedAccess 1 64) ∧
    execZstStmt ce1Env false ce1InitState ce1ReadStmt =
      .ub (.misalignedAccess 1 64) ∧
    execZstStmt ce1Env false ce1InitState (removeZstsStmt ce1Env ce1WriteStmt) =
      .ok ce1InitState ∧
    (∃ st', execZstStmt ce1Env false ce1InitState (removeZstsStmt ce1Env ce1ReadStmt) =
      .ok st') ∧
    execZstStmt ce1Env false ce1InitState
      (removeZstsCertifiedStmt ce1Env false (fun _ => true) ce1WriteStmt) =
      .ub (.misalignedAccess 1 64) ∧
    execZstStmt ce1Env false ce1InitState
      (removeZstsCertifiedStmt ce1Env false (fun _ => true) ce1ReadStmt) =
      .ub (.misalignedAccess 1 64) :=
  ⟨rfl, rfl, rfl, ⟨_, rfl⟩, rfl, rfl⟩

/-! ============================================================================
    Section 2. `ScalarReplacementOfAggregates` (`sroaFlatten`) Exact Bisimulation
    ============================================================================ -/

/-- Two-field selector (`FieldIdx` 0 or 1). -/
inductive Field2 where
  | f0
  | f1
  deriving DecidableEq, Repr

/-- Local type categories relevant to SROA eligibility (`sroa.rs:61-76`). -/
inductive SroaLocalKind where
  | scalar
  | structPair
  | unionOrEnum
  | maybeDangling
  deriving DecidableEq, Repr

/-- Static local-declaration and escape-analysis summary (`sroa.rs:56-88`). -/
structure SroaBodyEnv where
  argCount : Nat
  localKind : LocalId → SroaLocalKind
  addressTaken : LocalId → Bool

/-- Mirrors `escaping_locals` (`sroa.rs:56-88`): a local `l` is eligible for
SROA flattening iff `l > argCount` (neither `_0` return place nor ABI argument),
`!addressTaken l`, and `localKind l == .structPair`. -/
def isSroaEligible (env : SroaBodyEnv) (l : LocalId) : Bool :=
  Nat.blt env.argCount l && !env.addressTaken l && (env.localKind l == .structPair)

/-- Runtime slot state in the SROA machine. -/
inductive SroaSlot where
  | dead
  | liveScalar (val : Option Nat)
  | livePair (f0 : Option Nat) (f1 : Option Nat)
  deriving DecidableEq, Repr

/-- Fault kinds in the SROA machine. -/
inductive SroaUb where
  | deadSlot (l : LocalId)
  | uninitFieldOrScalar (l : LocalId)
  | typeMismatch
  deriving DecidableEq, Repr

/-- Operands producing a scalar `Nat` in the SROA MIR fragment. -/
inductive SroaScalarOp where
  | constNat (n : Nat)
  | copyScalar (src : LocalId)
  | moveScalar (src : LocalId)
  | copyField (agg : LocalId) (fld : Field2)
  | moveField (agg : LocalId) (fld : Field2)
  deriving DecidableEq, Repr

/-- Statements in the SROA MIR fragment, covering all rewrite arms of
`ReplacementVisitor::visit_statement` (`sroa.rs:302-422`). -/
inductive SroaStmt where
  | storageLiveScalar (l : LocalId)
  | storageLivePair (l : LocalId)
  | storageDead (l : LocalId)
  | assignScalar (dst : LocalId) (op : SroaScalarOp)
  | assignField (agg : LocalId) (fld : Field2) (op : SroaScalarOp)
  | assignAggregate (dst : LocalId) (op0 : SroaScalarOp) (op1 : SroaScalarOp)
  | assignPairCopyMove (dst : LocalId) (isMove : Bool) (src : LocalId)
  | nop
  deriving DecidableEq, Repr

abbrev SroaState := LocalId → SroaSlot

/-- Evaluate a `SroaScalarOp` under `deinitOnMove : Bool`. -/
def evalSroaScalarOp (deinitOnMove : Bool) (st : SroaState)
    (op : SroaScalarOp) : ExecOutcome (Nat × SroaState) SroaUb :=
  match op with
  | .constNat n => .ok (n, st)
  | .copyScalar s =>
    match st s with
    | .dead => .ub (.deadSlot s)
    | .liveScalar none => .ub (.uninitFieldOrScalar s)
    | .liveScalar (some n) => .ok (n, st)
    | .livePair _ _ => .ub .typeMismatch
  | .moveScalar s =>
    match st s with
    | .dead => .ub (.deadSlot s)
    | .liveScalar none => .ub (.uninitFieldOrScalar s)
    | .liveScalar (some n) =>
      let st' := if deinitOnMove then updateFn st s (.liveScalar none) else st
      .ok (n, st')
    | .livePair _ _ => .ub .typeMismatch
  | .copyField a fld =>
    match st a with
    | .dead => .ub (.deadSlot a)
    | .liveScalar _ => .ub .typeMismatch
    | .livePair o0 o1 =>
      match fld with
      | .f0 =>
        match o0 with
        | none => .ub (.uninitFieldOrScalar a)
        | some n => .ok (n, st)
      | .f1 =>
        match o1 with
        | none => .ub (.uninitFieldOrScalar a)
        | some n => .ok (n, st)
  | .moveField a fld =>
    match st a with
    | .dead => .ub (.deadSlot a)
    | .liveScalar _ => .ub .typeMismatch
    | .livePair o0 o1 =>
      match fld with
      | .f0 =>
        match o0 with
        | none => .ub (.uninitFieldOrScalar a)
        | some n =>
          let st' := if deinitOnMove then updateFn st a (.livePair none o1) else st
          .ok (n, st')
      | .f1 =>
        match o1 with
        | none => .ub (.uninitFieldOrScalar a)
        | some n =>
          let st' := if deinitOnMove then updateFn st a (.livePair o0 none) else st
          .ok (n, st')

/-- Execute a single `SroaStmt`. -/
def execSroaStmt (deinitOnMove : Bool) (st : SroaState)
    (stmt : SroaStmt) : ExecOutcome SroaState SroaUb :=
  match stmt with
  | .nop => .ok st
  | .storageLiveScalar l => .ok (updateFn st l (.liveScalar none))
  | .storageLivePair l => .ok (updateFn st l (.livePair none none))
  | .storageDead l => .ok (updateFn st l .dead)
  | .assignScalar dst op =>
    match evalSroaScalarOp deinitOnMove st op with
    | .ub err => .ub err
    | .ok (n, st1) =>
      match st1 dst with
      | .dead => .ub (.deadSlot dst)
      | .liveScalar _ => .ok (updateFn st1 dst (.liveScalar (some n)))
      | .livePair _ _ => .ub .typeMismatch
  | .assignField agg fld op =>
    match evalSroaScalarOp deinitOnMove st op with
    | .ub err => .ub err
    | .ok (n, st1) =>
      match st1 agg with
      | .dead => .ub (.deadSlot agg)
      | .liveScalar _ => .ub .typeMismatch
      | .livePair o0 o1 =>
        match fld with
        | .f0 => .ok (updateFn st1 agg (.livePair (some n) o1))
        | .f1 => .ok (updateFn st1 agg (.livePair o0 (some n)))
  | .assignAggregate dst op0 op1 =>
    match evalSroaScalarOp deinitOnMove st op0 with
    | .ub err => .ub err
    | .ok (n0, st1) =>
      match evalSroaScalarOp deinitOnMove st1 op1 with
      | .ub err => .ub err
      | .ok (n1, st2) =>
        match st2 dst with
        | .dead => .ub (.deadSlot dst)
        | .liveScalar _ => .ub .typeMismatch
        | .livePair _ _ => .ok (updateFn st2 dst (.livePair (some n0) (some n1)))
  | .assignPairCopyMove dst isMove src =>
    let op0 : SroaScalarOp := if isMove then .moveField src .f0 else .copyField src .f0
    let op1 : SroaScalarOp := if isMove then .moveField src .f1 else .copyField src .f1
    match evalSroaScalarOp deinitOnMove st op0 with
    | .ub err => .ub err
    | .ok (n0, st1) =>
      match st1 dst with
      | .dead => .ub (.deadSlot dst)
      | .liveScalar _ => .ub .typeMismatch
      | .livePair _ cur1 =>
        let stMid := updateFn st1 dst (.livePair (some n0) cur1)
        match evalSroaScalarOp deinitOnMove stMid op1 with
        | .ub err => .ub err
        | .ok (n1, st2) =>
          match st2 dst with
          | .dead => .ub (.deadSlot dst)
          | .liveScalar _ => .ub .typeMismatch
          | .livePair cur0' _ =>
            .ok (updateFn st2 dst (.livePair cur0' (some n1)))

/-- Execute a list of `SroaStmt`s sequentially. -/
noncomputable def execSroaProg (deinitOnMove : Bool) (st : SroaState) :
    List SroaStmt → ExecOutcome SroaState SroaUb
  | [] => .ok st
  | s :: rest =>
    match execSroaStmt deinitOnMove st s with
    | .ub err => .ub err
    | .ok st' => execSroaProg deinitOnMove st' rest

theorem execSroaProg_append (deinitOnMove : Bool) (st : SroaState)
    (p1 p2 : List SroaStmt) :
    execSroaProg deinitOnMove st (p1 ++ p2) =
      match execSroaProg deinitOnMove st p1 with
      | .ub err => .ub err
      | .ok st1 => execSroaProg deinitOnMove st1 p2 := by
  induction p1 generalizing st with
  | nil => rfl
  | cons s rest ih =>
    dsimp [execSroaProg]
    cases execSroaStmt deinitOnMove st s with
    | ub _ => rfl
    | ok st' => exact ih st'

theorem execSroaProg_singleton (deinitOnMove : Bool) (st : SroaState) (s : SroaStmt) :
    execSroaProg deinitOnMove st [s] = execSroaStmt deinitOnMove st s := by
  dsimp [execSroaProg]
  cases execSroaStmt deinitOnMove st s <;> rfl

/-- Map fragment fault local IDs `(l0, l1)` back to original aggregate local `l`. -/
def canonicalizeSroaUb (l l0 l1 : LocalId) : SroaUb → SroaUb
  | .deadSlot x =>
    if Nat.beq x l0 || Nat.beq x l1 then .deadSlot l else .deadSlot x
  | .uninitFieldOrScalar x =>
    if Nat.beq x l0 || Nat.beq x l1 then .uninitFieldOrScalar l else .uninitFieldOrScalar x
  | .typeMismatch => .typeMismatch

/-- Rewrite `SroaScalarOp` replacing field projections on `target` with scalar
accesses on fresh locals `l0` (`.f0`) and `l1` (`.f1`), matching
`ReplacementMap::replace_place` (`sroa.rs:147-154`). -/
def sroaFlattenOp (target l0 l1 : LocalId) (op : SroaScalarOp) : SroaScalarOp :=
  match op with
  | .copyField a .f0 => if Nat.beq a target then .copyScalar l0 else op
  | .copyField a .f1 => if Nat.beq a target then .copyScalar l1 else op
  | .moveField a .f0 => if Nat.beq a target then .moveScalar l0 else op
  | .moveField a .f1 => if Nat.beq a target then .moveScalar l1 else op
  | _ => op

/-- Flatten a single `SroaStmt` for eligible aggregate `target` into `(l0, l1)`. -/
def sroaFlattenStmt (target l0 l1 : LocalId) (stmt : SroaStmt) : List SroaStmt :=
  match stmt with
  | .storageLivePair a =>
    if Nat.beq a target then [.storageLiveScalar l0, .storageLiveScalar l1]
    else [stmt]
  | .storageLiveScalar _ => [stmt]
  | .storageDead a =>
    if Nat.beq a target then [.storageDead l0, .storageDead l1]
    else [stmt]
  | .assignScalar dst op =>
    [.assignScalar dst (sroaFlattenOp target l0 l1 op)]
  | .assignField a fld op =>
    let op' := sroaFlattenOp target l0 l1 op
    if Nat.beq a target then
      match fld with
      | .f0 => [.assignScalar l0 op']
      | .f1 => [.assignScalar l1 op']
    else
      [.assignField a fld op']
  | .assignAggregate dst op0 op1 =>
    let op0' := sroaFlattenOp target l0 l1 op0
    let op1' := sroaFlattenOp target l0 l1 op1
    if Nat.beq dst target then
      [.assignScalar l0 op0', .assignScalar l1 op1']
    else
      [.assignAggregate dst op0' op1']
  | .assignPairCopyMove dst isMove src =>
    let r0 : SroaScalarOp :=
      sroaFlattenOp target l0 l1 (if isMove then .moveField src .f0 else .copyField src .f0)
    let r1 : SroaScalarOp :=
      sroaFlattenOp target l0 l1 (if isMove then .moveField src .f1 else .copyField src .f1)
    if Nat.beq dst target then
      [.assignScalar l0 r0, .assignScalar l1 r1]
    else
      [.assignPairCopyMove dst isMove src]
  | .nop => [.nop]

noncomputable def sroaFlattenProg (target l0 l1 : LocalId) :
    List SroaStmt → List SroaStmt
  | [] => []
  | s :: rest => sroaFlattenStmt target l0 l1 s ++ sroaFlattenProg target l0 l1 rest

def OpUsesNeitherFresh (l0 l1 : LocalId) (target : LocalId) : SroaScalarOp → Bool
  | .constNat _ => true
  | .copyScalar s | .moveScalar s =>
    !Nat.beq s target && !Nat.beq s l0 && !Nat.beq s l1
  | .copyField a _ | .moveField a _ =>
    !Nat.beq a l0 && !Nat.beq a l1

def OpDoesNotReadTarget (target : LocalId) : SroaScalarOp → Bool
  | .constNat _ | .copyScalar _ | .moveScalar _ => true
  | .copyField a _ | .moveField a _ => !Nat.beq a target

def StmtSroaAdmitted (target l0 l1 : LocalId) : SroaStmt → Bool
  | .nop => true
  | .storageLiveScalar l =>
    !Nat.beq l target && !Nat.beq l l0 && !Nat.beq l l1
  | .storageLivePair l | .storageDead l =>
    !Nat.beq l l0 && !Nat.beq l l1
  | .assignScalar dst op =>
    !Nat.beq dst target && !Nat.beq dst l0 && !Nat.beq dst l1 &&
    OpUsesNeitherFresh l0 l1 target op
  | .assignField agg _ op =>
    !Nat.beq agg l0 && !Nat.beq agg l1 &&
    OpUsesNeitherFresh l0 l1 target op
  | .assignAggregate dst op0 op1 =>
    !Nat.beq dst l0 && !Nat.beq dst l1 &&
    OpUsesNeitherFresh l0 l1 target op0 &&
    OpUsesNeitherFresh l0 l1 target op1 &&
    (!Nat.beq dst target || (OpDoesNotReadTarget target op0 && OpDoesNotReadTarget target op1))
  | .assignPairCopyMove dst _ src =>
    !Nat.beq dst l0 && !Nat.beq dst l1 &&
    !Nat.beq src l0 && !Nat.beq src l1 &&
    !Nat.beq src target

/-- Exact state bisimulation coupling `src : SroaState` (with aggregate `target`)
and `tgt : SroaState` (with flattened scalar fragments `l0`, `l1`). -/
def SroaBisimRel (target l0 l1 : LocalId) (src tgt : SroaState) : Prop :=
  target ≠ l0 ∧ target ≠ l1 ∧ l0 ≠ l1 ∧
  (∀ k, k ≠ target → k ≠ l0 → k ≠ l1 → src k = tgt k) ∧
  ((src target = .dead ∧ tgt l0 = .dead ∧ tgt l1 = .dead) ∨
   (∃ o0 o1, src target = .livePair o0 o1 ∧
     tgt l0 = .liveScalar o0 ∧ tgt l1 = .liveScalar o1))

/-- Operand bisimulation lemma for `sroaFlattenOp`. -/
theorem sroaFlattenOp_bisim
    (deinitOnMove : Bool) (target l0 l1 : LocalId)
    (src tgt : SroaState) (op : SroaScalarOp)
    (hrel : SroaBisimRel target l0 l1 src tgt)
    (hadm : OpUsesNeitherFresh l0 l1 target op = true) :
    (∀ n src', evalSroaScalarOp deinitOnMove src op = .ok (n, src') →
      ∃ tgt', evalSroaScalarOp deinitOnMove tgt (sroaFlattenOp target l0 l1 op) = .ok (n, tgt') ∧
        SroaBisimRel target l0 l1 src' tgt') ∧
    (∀ err, evalSroaScalarOp deinitOnMove src op = .ub err →
      ∃ err', evalSroaScalarOp deinitOnMove tgt (sroaFlattenOp target l0 l1 op) = .ub err' ∧
        canonicalizeSroaUb target l0 l1 err' = err) := by
  rcases hrel with ⟨ht0, ht1, h01, hframe, hpair⟩
  cases op with
  | constNat _ =>
    refine ⟨?_, ?_⟩
    · intro n' src' hev
      injection hev with hpair_; injection hpair_ with hn hs; subst hn hs
      exact ⟨tgt, rfl, ⟨ht0, ht1, h01, hframe, hpair⟩⟩
    · intro _ hev; contradiction
  | copyScalar s =>
    dsimp [OpUsesNeitherFresh] at hadm
    have ⟨h12, hs1b⟩ := Bool.and_eq_true_iff.mp hadm
    have ⟨hstb, hs0b⟩ := Bool.and_eq_true_iff.mp h12
    have hst : s ≠ target := not_beq_true_to_ne hstb
    have hs0 : s ≠ l0 := not_beq_true_to_ne hs0b
    have hs1 : s ≠ l1 := not_beq_true_to_ne hs1b
    have hslot : tgt s = src s := (hframe s hst hs0 hs1).symm
    dsimp [sroaFlattenOp, evalSroaScalarOp]
    rw [hslot]
    refine ⟨?_, ?_⟩
    · intro n src' hev
      cases hss : src s with
      | dead | livePair _ _ => rw [hss] at hev; contradiction
      | liveScalar opt =>
        cases opt with
        | none => rw [hss] at hev; contradiction
        | some _ =>
          rw [hss] at hev
          injection hev with hpair_; injection hpair_ with hn hs; subst hn hs
          exact ⟨tgt, rfl, ⟨ht0, ht1, h01, hframe, hpair⟩⟩
    · intro err hev
      cases hss : src s with
      | dead =>
        rw [hss] at hev; injection hev with he; subst he
        refine ⟨.deadSlot s, rfl, ?_⟩
        dsimp [canonicalizeSroaUb]
        rw [(nat_beq_eq_false_iff s l0).mpr hs0, (nat_beq_eq_false_iff s l1).mpr hs1]; rfl
      | livePair _ _ =>
        rw [hss] at hev; injection hev with he; subst he
        exact ⟨.typeMismatch, rfl, rfl⟩
      | liveScalar opt =>
        cases opt with
        | some _ => rw [hss] at hev; contradiction
        | none =>
          rw [hss] at hev; injection hev with he; subst he
          refine ⟨.uninitFieldOrScalar s, rfl, ?_⟩
          dsimp [canonicalizeSroaUb]
          rw [(nat_beq_eq_false_iff s l0).mpr hs0, (nat_beq_eq_false_iff s l1).mpr hs1]; rfl
  | moveScalar s =>
    dsimp [OpUsesNeitherFresh] at hadm
    have ⟨h12, hs1b⟩ := Bool.and_eq_true_iff.mp hadm
    have ⟨hstb, hs0b⟩ := Bool.and_eq_true_iff.mp h12
    have hst : s ≠ target := not_beq_true_to_ne hstb
    have hs0 : s ≠ l0 := not_beq_true_to_ne hs0b
    have hs1 : s ≠ l1 := not_beq_true_to_ne hs1b
    have hslot : tgt s = src s := (hframe s hst hs0 hs1).symm
    dsimp [sroaFlattenOp, evalSroaScalarOp]
    rw [hslot]
    refine ⟨?_, ?_⟩
    · intro n src' hev
      cases hss : src s with
      | dead | livePair _ _ => rw [hss] at hev; contradiction
      | liveScalar opt =>
        cases opt with
        | none => rw [hss] at hev; contradiction
        | some _ =>
          rw [hss] at hev
          injection hev with hpair_; injection hpair_ with hn hs; subst hn hs
          cases deinitOnMove with
          | false => exact ⟨tgt, rfl, ⟨ht0, ht1, h01, hframe, hpair⟩⟩
          | true =>
            dsimp
            refine ⟨_, rfl, ⟨ht0, ht1, h01, ?_, ?_⟩⟩
            · intro k hkt hk0 hk1
              cases hks : Nat.beq k s with
              | true =>
                have heq : k = s := Nat.eq_of_beq_eq_true hks
                subst heq; rw [updateFn_self, updateFn_self]
              | false =>
                have hne : k ≠ s := (nat_beq_eq_false_iff k s).mp hks
                rw [updateFn_ne _ s k _ hne, updateFn_ne _ s k _ hne]
                exact hframe k hkt hk0 hk1
            · rw [updateFn_ne _ s target _ (Ne.symm hst),
                  updateFn_ne _ s l0 _ (Ne.symm hs0),
                  updateFn_ne _ s l1 _ (Ne.symm hs1)]
              exact hpair
    · intro err hev
      cases hss : src s with
      | dead =>
        rw [hss] at hev; injection hev with he; subst he
        refine ⟨.deadSlot s, rfl, ?_⟩
        dsimp [canonicalizeSroaUb]
        rw [(nat_beq_eq_false_iff s l0).mpr hs0, (nat_beq_eq_false_iff s l1).mpr hs1]; rfl
      | livePair _ _ =>
        rw [hss] at hev; injection hev with he; subst he
        exact ⟨.typeMismatch, rfl, rfl⟩
      | liveScalar opt =>
        cases opt with
        | some _ => rw [hss] at hev; contradiction
        | none =>
          rw [hss] at hev; injection hev with he; subst he
          refine ⟨.uninitFieldOrScalar s, rfl, ?_⟩
          dsimp [canonicalizeSroaUb]
          rw [(nat_beq_eq_false_iff s l0).mpr hs0, (nat_beq_eq_false_iff s l1).mpr hs1]; rfl
  | copyField a fld =>
    dsimp [OpUsesNeitherFresh] at hadm
    have ⟨ha0b, ha1b⟩ := Bool.and_eq_true_iff.mp hadm
    have ha0 : a ≠ l0 := not_beq_true_to_ne ha0b
    have ha1 : a ≠ l1 := not_beq_true_to_ne ha1b
    cases hat : Nat.beq a target with
    | true =>
      have heq : a = target := Nat.eq_of_beq_eq_true hat
      subst heq
      cases fld with
      | f0 =>
        dsimp [sroaFlattenOp]
        rw [Nat.beq_refl a]
        dsimp [evalSroaScalarOp]
        rcases hpair with ⟨hsd, ht0d, _⟩ | ⟨o0, o1, hsp, htl0, htl1⟩
        · rw [hsd, ht0d]
          refine ⟨fun _ _ h => by contradiction, fun err h => ?_⟩
          injection h with he; subst he
          refine ⟨.deadSlot l0, rfl, ?_⟩
          dsimp [canonicalizeSroaUb]; rw [Nat.beq_refl l0]; rfl
        · rw [hsp, htl0]
          cases o0 with
          | none =>
            refine ⟨fun _ _ h => by contradiction, fun err h => ?_⟩
            injection h with he; subst he
            refine ⟨.uninitFieldOrScalar l0, rfl, ?_⟩
            dsimp [canonicalizeSroaUb]; rw [Nat.beq_refl l0]; rfl
          | some n =>
            refine ⟨fun n' src' h => ?_, fun _ h => by contradiction⟩
            injection h with hpair_; injection hpair_ with hn hs; subst hn hs
            exact ⟨tgt, rfl, ⟨ht0, ht1, h01, hframe, Or.inr ⟨some n, o1, hsp, htl0, htl1⟩⟩⟩
      | f1 =>
        dsimp [sroaFlattenOp]
        rw [Nat.beq_refl a]
        dsimp [evalSroaScalarOp]
        rcases hpair with ⟨hsd, _, ht1d⟩ | ⟨o0, o1, hsp, htl0, htl1⟩
        · rw [hsd, ht1d]
          refine ⟨fun _ _ h => by contradiction, fun err h => ?_⟩
          injection h with he; subst he
          refine ⟨.deadSlot l1, rfl, ?_⟩
          dsimp [canonicalizeSroaUb]
          rw [(nat_beq_eq_false_iff l1 l0).mpr (Ne.symm h01), Nat.beq_refl l1]; rfl
        · rw [hsp, htl1]
          cases o1 with
          | none =>
            refine ⟨fun _ _ h => by contradiction, fun err h => ?_⟩
            injection h with he; subst he
            refine ⟨.uninitFieldOrScalar l1, rfl, ?_⟩
            dsimp [canonicalizeSroaUb]
            rw [(nat_beq_eq_false_iff l1 l0).mpr (Ne.symm h01), Nat.beq_refl l1]; rfl
          | some n =>
            refine ⟨fun n' src' h => ?_, fun _ h => by contradiction⟩
            injection h with hpair_; injection hpair_ with hn hs; subst hn hs
            exact ⟨tgt, rfl, ⟨ht0, ht1, h01, hframe, Or.inr ⟨o0, some n, hsp, htl0, htl1⟩⟩⟩
    | false =>
      have hne : a ≠ target := (nat_beq_eq_false_iff a target).mp hat
      have hslot : tgt a = src a := (hframe a hne ha0 ha1).symm
      cases fld <;> {
        dsimp [sroaFlattenOp]
        rw [hat]
        dsimp [evalSroaScalarOp]
        rw [hslot]
        refine ⟨?_, ?_⟩
        · intro n src' hev
          cases hsa : src a with
          | dead | liveScalar _ => rw [hsa] at hev; contradiction
          | livePair o0 o1 =>
            rw [hsa] at hev
            first
            | (cases o0 with
               | none => contradiction
               | some _ => injection hev with hpair_; injection hpair_ with hn hs; subst hn hs; exact ⟨tgt, rfl, ⟨ht0, ht1, h01, hframe, hpair⟩⟩)
            | (cases o1 with
               | none => contradiction
               | some _ => injection hev with hpair_; injection hpair_ with hn hs; subst hn hs; exact ⟨tgt, rfl, ⟨ht0, ht1, h01, hframe, hpair⟩⟩)
        · intro err hev
          cases hsa : src a with
          | dead =>
            rw [hsa] at hev; injection hev with he; subst he
            refine ⟨.deadSlot a, rfl, ?_⟩
            dsimp [canonicalizeSroaUb]
            rw [(nat_beq_eq_false_iff a l0).mpr ha0, (nat_beq_eq_false_iff a l1).mpr ha1]; rfl
          | liveScalar _ =>
            rw [hsa] at hev; injection hev with he; subst he
            exact ⟨.typeMismatch, rfl, rfl⟩
          | livePair o0 o1 =>
            rw [hsa] at hev
            first
            | (cases o0 with
               | some _ => contradiction
               | none =>
                 injection hev with he; subst he
                 refine ⟨.uninitFieldOrScalar a, rfl, ?_⟩
                 dsimp [canonicalizeSroaUb]
                 rw [(nat_beq_eq_false_iff a l0).mpr ha0, (nat_beq_eq_false_iff a l1).mpr ha1]; rfl)
            | (cases o1 with
               | some _ => contradiction
               | none =>
                 injection hev with he; subst he
                 refine ⟨.uninitFieldOrScalar a, rfl, ?_⟩
                 dsimp [canonicalizeSroaUb]
                 rw [(nat_beq_eq_false_iff a l0).mpr ha0, (nat_beq_eq_false_iff a l1).mpr ha1]; rfl)
      }
  | moveField a fld =>
    dsimp [OpUsesNeitherFresh] at hadm
    have ⟨ha0b, ha1b⟩ := Bool.and_eq_true_iff.mp hadm
    have ha0 : a ≠ l0 := not_beq_true_to_ne ha0b
    have ha1 : a ≠ l1 := not_beq_true_to_ne ha1b
    cases hat : Nat.beq a target with
    | true =>
      have heq : a = target := Nat.eq_of_beq_eq_true hat
      subst heq
      cases fld with
      | f0 =>
        dsimp [sroaFlattenOp]
        rw [Nat.beq_refl a]
        dsimp [evalSroaScalarOp]
        rcases hpair with ⟨hsd, ht0d, _⟩ | ⟨o0, o1, hsp, htl0, htl1⟩
        · rw [hsd, ht0d]
          refine ⟨fun _ _ h => by contradiction, fun err h => ?_⟩
          injection h with he; subst he
          refine ⟨.deadSlot l0, rfl, ?_⟩
          dsimp [canonicalizeSroaUb]; rw [Nat.beq_refl l0]; rfl
        · rw [hsp, htl0]
          cases o0 with
          | none =>
            refine ⟨fun _ _ h => by contradiction, fun err h => ?_⟩
            injection h with he; subst he
            refine ⟨.uninitFieldOrScalar l0, rfl, ?_⟩
            dsimp [canonicalizeSroaUb]; rw [Nat.beq_refl l0]; rfl
          | some n =>
            refine ⟨fun n' src' h => ?_, fun _ h => by contradiction⟩
            injection h with hpair_; injection hpair_ with hn hs; subst hn hs
            cases deinitOnMove with
            | false =>
              exact ⟨tgt, rfl, ⟨ht0, ht1, h01, hframe, Or.inr ⟨some n, o1, hsp, htl0, htl1⟩⟩⟩
            | true =>
              dsimp
              refine ⟨_, rfl, ⟨ht0, ht1, h01, ?_, Or.inr ⟨none, o1, ?_, ?_, ?_⟩⟩⟩
              · intro k hkt hk0 hk1
                rw [updateFn_ne _ a k _ hkt, updateFn_ne _ l0 k _ hk0]
                exact hframe k hkt hk0 hk1
              · exact updateFn_self src a (.livePair none o1)
              · exact updateFn_self tgt l0 (.liveScalar none)
              · rw [updateFn_ne _ l0 l1 _ (Ne.symm h01)]; exact htl1
      | f1 =>
        dsimp [sroaFlattenOp]
        rw [Nat.beq_refl a]
        dsimp [evalSroaScalarOp]
        rcases hpair with ⟨hsd, _, ht1d⟩ | ⟨o0, o1, hsp, htl0, htl1⟩
        · rw [hsd, ht1d]
          refine ⟨fun _ _ h => by contradiction, fun err h => ?_⟩
          injection h with he; subst he
          refine ⟨.deadSlot l1, rfl, ?_⟩
          dsimp [canonicalizeSroaUb]
          rw [(nat_beq_eq_false_iff l1 l0).mpr (Ne.symm h01), Nat.beq_refl l1]; rfl
        · rw [hsp, htl1]
          cases o1 with
          | none =>
            refine ⟨fun _ _ h => by contradiction, fun err h => ?_⟩
            injection h with he; subst he
            refine ⟨.uninitFieldOrScalar l1, rfl, ?_⟩
            dsimp [canonicalizeSroaUb]
            rw [(nat_beq_eq_false_iff l1 l0).mpr (Ne.symm h01), Nat.beq_refl l1]; rfl
          | some n =>
            refine ⟨fun n' src' h => ?_, fun _ h => by contradiction⟩
            injection h with hpair_; injection hpair_ with hn hs; subst hn hs
            cases deinitOnMove with
            | false =>
              exact ⟨tgt, rfl, ⟨ht0, ht1, h01, hframe, Or.inr ⟨o0, some n, hsp, htl0, htl1⟩⟩⟩
            | true =>
              dsimp
              refine ⟨_, rfl, ⟨ht0, ht1, h01, ?_, Or.inr ⟨o0, none, ?_, ?_, ?_⟩⟩⟩
              · intro k hkt hk0 hk1
                rw [updateFn_ne _ a k _ hkt, updateFn_ne _ l1 k _ hk1]
                exact hframe k hkt hk0 hk1
              · exact updateFn_self src a (.livePair o0 none)
              · rw [updateFn_ne _ l1 l0 _ h01]; exact htl0
              · exact updateFn_self tgt l1 (.liveScalar none)
    | false =>
      have hne : a ≠ target := (nat_beq_eq_false_iff a target).mp hat
      have hslot : tgt a = src a := (hframe a hne ha0 ha1).symm
      cases fld with
      | f0 =>
        dsimp [sroaFlattenOp]; rw [hat]; dsimp [evalSroaScalarOp]; rw [hslot]
        refine ⟨?_, ?_⟩
        · intro n src' hev
          cases hsa : src a with
          | dead | liveScalar _ => rw [hsa] at hev; contradiction
          | livePair o0 o1 =>
            rw [hsa] at hev; dsimp at hev
            cases ho0 : o0 with
            | none => rw [ho0] at hev; contradiction
            | some _ =>
              rw [ho0] at hev
              injection hev with hpair_; injection hpair_ with hn hs; subst hn hs
              cases deinitOnMove with
              | false => exact ⟨tgt, rfl, ⟨ht0, ht1, h01, hframe, hpair⟩⟩
              | true =>
                dsimp
                refine ⟨_, rfl, ⟨ht0, ht1, h01, ?_, ?_⟩⟩
                · intro k hkt hk0 hk1
                  cases hka : Nat.beq k a with
                  | true => have heq := Nat.eq_of_beq_eq_true hka; subst heq; rw [updateFn_self, updateFn_self]
                  | false =>
                    have hnea := (nat_beq_eq_false_iff k a).mp hka
                    rw [updateFn_ne _ a k _ hnea, updateFn_ne _ a k _ hnea]; exact hframe k hkt hk0 hk1
                · rw [updateFn_ne _ a target _ (Ne.symm hne),
                      updateFn_ne _ a l0 _ (Ne.symm ha0),
                      updateFn_ne _ a l1 _ (Ne.symm ha1)]
                  exact hpair
        · intro err hev
          cases hsa : src a with
          | dead =>
            rw [hsa] at hev; injection hev with he; subst he
            refine ⟨.deadSlot a, rfl, ?_⟩
            dsimp [canonicalizeSroaUb]
            rw [(nat_beq_eq_false_iff a l0).mpr ha0, (nat_beq_eq_false_iff a l1).mpr ha1]; rfl
          | liveScalar _ =>
            rw [hsa] at hev; injection hev with he; subst he
            exact ⟨.typeMismatch, rfl, rfl⟩
          | livePair o0 _ =>
            rw [hsa] at hev; dsimp at hev
            cases ho0 : o0 with
            | some _ => rw [ho0] at hev; contradiction
            | none =>
              rw [ho0] at hev; injection hev with he; subst he
              refine ⟨.uninitFieldOrScalar a, rfl, ?_⟩
              dsimp [canonicalizeSroaUb]
              rw [(nat_beq_eq_false_iff a l0).mpr ha0, (nat_beq_eq_false_iff a l1).mpr ha1]; rfl
      | f1 =>
        dsimp [sroaFlattenOp]; rw [hat]; dsimp [evalSroaScalarOp]; rw [hslot]
        refine ⟨?_, ?_⟩
        · intro n src' hev
          cases hsa : src a with
          | dead | liveScalar _ => rw [hsa] at hev; contradiction
          | livePair o0 o1 =>
            rw [hsa] at hev; dsimp at hev
            cases ho1 : o1 with
            | none => rw [ho1] at hev; contradiction
            | some _ =>
              rw [ho1] at hev
              injection hev with hpair_; injection hpair_ with hn hs; subst hn hs
              cases deinitOnMove with
              | false => exact ⟨tgt, rfl, ⟨ht0, ht1, h01, hframe, hpair⟩⟩
              | true =>
                dsimp
                refine ⟨_, rfl, ⟨ht0, ht1, h01, ?_, ?_⟩⟩
                · intro k hkt hk0 hk1
                  cases hka : Nat.beq k a with
                  | true => have heq := Nat.eq_of_beq_eq_true hka; subst heq; rw [updateFn_self, updateFn_self]
                  | false =>
                    have hnea := (nat_beq_eq_false_iff k a).mp hka
                    rw [updateFn_ne _ a k _ hnea, updateFn_ne _ a k _ hnea]; exact hframe k hkt hk0 hk1
                · rw [updateFn_ne _ a target _ (Ne.symm hne),
                      updateFn_ne _ a l0 _ (Ne.symm ha0),
                      updateFn_ne _ a l1 _ (Ne.symm ha1)]
                  exact hpair
        · intro err hev
          cases hsa : src a with
          | dead =>
            rw [hsa] at hev; injection hev with he; subst he
            refine ⟨.deadSlot a, rfl, ?_⟩
            dsimp [canonicalizeSroaUb]
            rw [(nat_beq_eq_false_iff a l0).mpr ha0, (nat_beq_eq_false_iff a l1).mpr ha1]; rfl
          | liveScalar _ =>
            rw [hsa] at hev; injection hev with he; subst he
            exact ⟨.typeMismatch, rfl, rfl⟩
          | livePair _ o1 =>
            rw [hsa] at hev; dsimp at hev
            cases ho1 : o1 with
            | some _ => rw [ho1] at hev; contradiction
            | none =>
              rw [ho1] at hev; injection hev with he; subst he
              refine ⟨.uninitFieldOrScalar a, rfl, ?_⟩
              dsimp [canonicalizeSroaUb]
              rw [(nat_beq_eq_false_iff a l0).mpr ha0, (nat_beq_eq_false_iff a l1).mpr ha1]; rfl

/-- Framing lemma for `l0` when `op` neither reads `target` nor uses `(l0, l1)`. -/
theorem evalSroaScalarOp_frame_l0
    (deinitOnMove : Bool) (target l0 l1 : LocalId)
    (st : SroaState) (v0 : SroaSlot) (op : SroaScalarOp)
    (hf : OpUsesNeitherFresh l0 l1 target op = true)
    (hnr : OpDoesNotReadTarget target op = true) :
    sroaFlattenOp target l0 l1 op = op ∧
    (∀ n st', evalSroaScalarOp deinitOnMove st op = .ok (n, st') →
      evalSroaScalarOp deinitOnMove (updateFn st l0 v0) op = .ok (n, updateFn st' l0 v0)) ∧
    (∀ err, evalSroaScalarOp deinitOnMove st op = .ub err →
      evalSroaScalarOp deinitOnMove (updateFn st l0 v0) op = .ub err) := by
  cases op with
  | constNat _ =>
    exact ⟨rfl, fun _ _ h => by injection h with hpair_; injection hpair_ with hn hs; subst hn hs; rfl, fun _ h => by contradiction⟩
  | copyScalar s =>
    dsimp [OpUsesNeitherFresh] at hf
    have ⟨h12, _⟩ := Bool.and_eq_true_iff.mp hf
    have ⟨_, hs0b⟩ := Bool.and_eq_true_iff.mp h12
    have hs0 : s ≠ l0 := not_beq_true_to_ne hs0b
    refine ⟨rfl, ?_, ?_⟩
    · intro _ _ h
      dsimp [evalSroaScalarOp] at h ⊢
      rw [updateFn_ne _ l0 s _ hs0]
      cases hss : st s with
      | dead | livePair _ _ => rw [hss] at h; contradiction
      | liveScalar o =>
        cases o with
        | none => rw [hss] at h; contradiction
        | some _ => rw [hss] at h; injection h with hpair_; injection hpair_ with hn hs; subst hn hs; rfl
    · intro _ h
      dsimp [evalSroaScalarOp] at h ⊢
      rw [updateFn_ne _ l0 s _ hs0]
      cases hss : st s with
      | dead | livePair _ _ => rw [hss] at h; exact h
      | liveScalar o =>
        rw [hss] at h
        cases o with
        | none => exact h
        | some _ => contradiction
  | moveScalar s =>
    dsimp [OpUsesNeitherFresh] at hf
    have ⟨h12, _⟩ := Bool.and_eq_true_iff.mp hf
    have ⟨_, hs0b⟩ := Bool.and_eq_true_iff.mp h12
    have hs0 : s ≠ l0 := not_beq_true_to_ne hs0b
    refine ⟨rfl, ?_, ?_⟩
    · intro _ _ h
      dsimp [evalSroaScalarOp] at h ⊢
      rw [updateFn_ne _ l0 s _ hs0]
      cases hss : st s with
      | dead | livePair _ _ => rw [hss] at h; contradiction
      | liveScalar o =>
        cases o with
        | none => rw [hss] at h; contradiction
        | some _ =>
          rw [hss] at h; injection h with hpair_; injection hpair_ with hn hs; subst hn hs
          cases deinitOnMove with
          | false => rfl
          | true =>
            dsimp
            have hcomm : updateFn (updateFn st l0 v0) s (.liveScalar none) =
                updateFn (updateFn st s (.liveScalar none)) l0 v0 := by
              funext x
              cases hxs : Nat.beq x s with
              | true =>
                have heq : x = s := Nat.eq_of_beq_eq_true hxs
                subst heq
                rw [updateFn_self, updateFn_ne _ l0 x _ hs0, updateFn_self]
              | false =>
                have hne : x ≠ s := (nat_beq_eq_false_iff x s).mp hxs
                rw [updateFn_ne _ s x _ hne]
                cases hx0 : Nat.beq x l0 with
                | true =>
                  have heq0 : x = l0 := Nat.eq_of_beq_eq_true hx0
                  subst heq0; rw [updateFn_self, updateFn_self]
                | false =>
                  have hne0 : x ≠ l0 := (nat_beq_eq_false_iff x l0).mp hx0
                  rw [updateFn_ne _ l0 x _ hne0, updateFn_ne _ l0 x _ hne0, updateFn_ne _ s x _ hne]
            rw [hcomm]
    · intro _ h
      dsimp [evalSroaScalarOp] at h ⊢
      rw [updateFn_ne _ l0 s _ hs0]
      cases hss : st s with
      | dead | livePair _ _ => rw [hss] at h; exact h
      | liveScalar o =>
        rw [hss] at h
        cases o with
        | none => exact h
        | some _ => contradiction
  | copyField a fld =>
    dsimp [OpUsesNeitherFresh] at hf
    dsimp [OpDoesNotReadTarget] at hnr
    have ⟨ha0b, _⟩ := Bool.and_eq_true_iff.mp hf
    have ha0 : a ≠ l0 := not_beq_true_to_ne ha0b
    have hatf : Nat.beq a target = false := (nat_beq_eq_false_iff a target).mpr (not_beq_true_to_ne hnr)
    cases fld <;> {
      refine ⟨by dsimp [sroaFlattenOp]; rw [hatf]; rfl, ?_, ?_⟩
      · intro _ _ h
        dsimp [evalSroaScalarOp] at h ⊢
        rw [updateFn_ne _ l0 a _ ha0]
        cases hsa : st a with
        | dead | liveScalar _ => rw [hsa] at h; contradiction
        | livePair o0 o1 =>
          rw [hsa] at h
          first
          | (cases o0 with | none => contradiction | some _ => injection h with hpair_; injection hpair_ with hn hs; subst hn hs; rfl)
          | (cases o1 with | none => contradiction | some _ => injection h with hpair_; injection hpair_ with hn hs; subst hn hs; rfl)
      · intro _ h
        dsimp [evalSroaScalarOp] at h ⊢
        rw [updateFn_ne _ l0 a _ ha0]
        cases hsa : st a with
        | dead | liveScalar _ => rw [hsa] at h; exact h
        | livePair o0 o1 =>
          rw [hsa] at h; dsimp at h ⊢
          first
          | (cases ho0 : o0 with | none => rw [ho0] at h; exact h | some _ => rw [ho0] at h; contradiction)
          | (cases ho1 : o1 with | none => rw [ho1] at h; exact h | some _ => rw [ho1] at h; contradiction)
    }
  | moveField a fld =>
    dsimp [OpUsesNeitherFresh] at hf
    dsimp [OpDoesNotReadTarget] at hnr
    have ⟨ha0b, _⟩ := Bool.and_eq_true_iff.mp hf
    have ha0 : a ≠ l0 := not_beq_true_to_ne ha0b
    have hatf : Nat.beq a target = false := (nat_beq_eq_false_iff a target).mpr (not_beq_true_to_ne hnr)
    cases fld <;> {
      refine ⟨by dsimp [sroaFlattenOp]; rw [hatf]; rfl, ?_, ?_⟩
      · intro _ _ h
        dsimp [evalSroaScalarOp] at h ⊢
        rw [updateFn_ne _ l0 a _ ha0]
        cases hsa : st a with
        | dead | liveScalar _ => rw [hsa] at h; contradiction
        | livePair o0 o1 =>
          rw [hsa] at h
          first
          | (cases o0 with
             | none => contradiction
             | some _ =>
               injection h with hpair_; injection hpair_ with hn hs; subst hn hs
               cases deinitOnMove with
               | false => rfl
               | true =>
                 dsimp
                 have hcomm : updateFn (updateFn st l0 v0) a (.livePair none o1) =
                     updateFn (updateFn st a (.livePair none o1)) l0 v0 := by
                   funext x
                   cases hxa : Nat.beq x a with
                   | true =>
                     have heq : x = a := Nat.eq_of_beq_eq_true hxa
                     subst heq; rw [updateFn_self, updateFn_ne _ l0 x _ ha0, updateFn_self]
                   | false =>
                     have hne : x ≠ a := (nat_beq_eq_false_iff x a).mp hxa
                     rw [updateFn_ne _ a x _ hne]
                     cases hx0 : Nat.beq x l0 with
                     | true =>
                       have heq0 : x = l0 := Nat.eq_of_beq_eq_true hx0
                       subst heq0; rw [updateFn_self, updateFn_self]
                     | false =>
                       have hne0 : x ≠ l0 := (nat_beq_eq_false_iff x l0).mp hx0
                       rw [updateFn_ne _ l0 x _ hne0, updateFn_ne _ l0 x _ hne0, updateFn_ne _ a x _ hne]
                 rw [hcomm])
          | (cases o1 with
             | none => contradiction
             | some _ =>
               injection h with hpair_; injection hpair_ with hn hs; subst hn hs
               cases deinitOnMove with
               | false => rfl
               | true =>
                 dsimp
                 have hcomm : updateFn (updateFn st l0 v0) a (.livePair o0 none) =
                     updateFn (updateFn st a (.livePair o0 none)) l0 v0 := by
                   funext x
                   cases hxa : Nat.beq x a with
                   | true =>
                     have heq : x = a := Nat.eq_of_beq_eq_true hxa
                     subst heq; rw [updateFn_self, updateFn_ne _ l0 x _ ha0, updateFn_self]
                   | false =>
                     have hne : x ≠ a := (nat_beq_eq_false_iff x a).mp hxa
                     rw [updateFn_ne _ a x _ hne]
                     cases hx0 : Nat.beq x l0 with
                     | true =>
                       have heq0 : x = l0 := Nat.eq_of_beq_eq_true hx0
                       subst heq0; rw [updateFn_self, updateFn_self]
                     | false =>
                       have hne0 : x ≠ l0 := (nat_beq_eq_false_iff x l0).mp hx0
                       rw [updateFn_ne _ l0 x _ hne0, updateFn_ne _ l0 x _ hne0, updateFn_ne _ a x _ hne]
                 rw [hcomm])
      · intro _ h
        dsimp [evalSroaScalarOp] at h ⊢
        rw [updateFn_ne _ l0 a _ ha0]
        cases hsa : st a with
        | dead | liveScalar _ => rw [hsa] at h; exact h
        | livePair o0 o1 =>
          rw [hsa] at h; dsimp at h ⊢
          first
          | (cases ho0 : o0 with | none => rw [ho0] at h; exact h | some _ => rw [ho0] at h; contradiction)
          | (cases ho1 : o1 with | none => rw [ho1] at h; exact h | some _ => rw [ho1] at h; contradiction)
    }

/-- Helper: `evalSroaScalarOp` preserves `st dst` when `op` does not touch `dst`. -/
theorem evalSroaScalarOp_preserves_target_slot
    (deinitOnMove : Bool) (dst l0 l1 : LocalId)
    (st st' : SroaState) (op : SroaScalarOp) (n : Nat)
    (hf : OpUsesNeitherFresh l0 l1 dst op = true)
    (hnr : OpDoesNotReadTarget dst op = true)
    (hev : evalSroaScalarOp deinitOnMove st op = .ok (n, st')) :
    st' dst = st dst := by
  cases op with
  | constNat _ => injection hev with hpair_; injection hpair_ with _ hs; subst hs; rfl
  | copyScalar s =>
    dsimp [evalSroaScalarOp] at hev
    cases hs1 : st s with
    | dead | livePair _ _ => rw [hs1] at hev; contradiction
    | liveScalar o =>
      cases o with
      | none => rw [hs1] at hev; contradiction
      | some _ => rw [hs1] at hev; injection hev with hpair_; injection hpair_ with _ hs; subst hs; rfl
  | moveScalar s =>
    dsimp [OpUsesNeitherFresh] at hf
    have ⟨h12, _⟩ := Bool.and_eq_true_iff.mp hf
    have ⟨hstb, _⟩ := Bool.and_eq_true_iff.mp h12
    have hne : dst ≠ s := Ne.symm (not_beq_true_to_ne hstb)
    dsimp [evalSroaScalarOp] at hev
    cases hs1 : st s with
    | dead | livePair _ _ => rw [hs1] at hev; contradiction
    | liveScalar o =>
      cases o with
      | none => rw [hs1] at hev; contradiction
      | some _ =>
        rw [hs1] at hev; injection hev with hpair_; injection hpair_ with _ hs; subst hs
        cases deinitOnMove with
        | false => rfl
        | true => exact updateFn_ne st s dst _ hne
  | copyField a f =>
    dsimp [evalSroaScalarOp] at hev
    cases ha1s : st a with
    | dead | liveScalar _ => rw [ha1s] at hev; contradiction
    | livePair x0 x1 =>
      rw [ha1s] at hev
      cases f <;> (first
        | (cases x0 with | none => contradiction | some _ => injection hev with hpair_; injection hpair_ with _ hs; subst hs; rfl)
        | (cases x1 with | none => contradiction | some _ => injection hev with hpair_; injection hpair_ with _ hs; subst hs; rfl))
  | moveField a f =>
    dsimp [OpDoesNotReadTarget] at hnr
    have hne : dst ≠ a := Ne.symm (not_beq_true_to_ne hnr)
    dsimp [evalSroaScalarOp] at hev
    cases ha1s : st a with
    | dead | liveScalar _ => rw [ha1s] at hev; contradiction
    | livePair x0 x1 =>
      rw [ha1s] at hev
      cases f <;> (first
        | (cases x0 with
           | none => contradiction
           | some _ =>
             injection hev with hpair_; injection hpair_ with _ hs; subst hs
             cases deinitOnMove with | false => rfl | true => exact updateFn_ne st a dst _ hne)
        | (cases x1 with
           | none => contradiction
           | some _ =>
             injection hev with hpair_; injection hpair_ with _ hs; subst hs
             cases deinitOnMove with | false => rfl | true => exact updateFn_ne st a dst _ hne))

/-- **Main Theorem 2a (`sroaFlattenStmt_exact_bisimulation`):**
For every SROA-admitted statement `stmt`, `sroaFlattenStmt` preserves exact
bidirectional operational behavior (both `.ok` state coupling and `.ub`
equivalence) for both `deinitOnMove = false` and `deinitOnMove = true`. -/
theorem sroaFlattenStmt_exact_bisimulation
    (deinitOnMove : Bool) (target l0 l1 : LocalId)
    (src tgt : SroaState) (stmt : SroaStmt)
    (hrel : SroaBisimRel target l0 l1 src tgt)
    (hadm : StmtSroaAdmitted target l0 l1 stmt = true) :
    (∀ src', execSroaStmt deinitOnMove src stmt = .ok src' →
      ∃ tgt', execSroaProg deinitOnMove tgt (sroaFlattenStmt target l0 l1 stmt) = .ok tgt' ∧
        SroaBisimRel target l0 l1 src' tgt') ∧
    ((∃ err, execSroaStmt deinitOnMove src stmt = .ub err) ↔
     (∃ err', execSroaProg deinitOnMove tgt (sroaFlattenStmt target l0 l1 stmt) = .ub err')) := by
  rcases hrel with ⟨ht0, ht1, h01, hframe, hpair⟩
  have hrel0 : SroaBisimRel target l0 l1 src tgt := ⟨ht0, ht1, h01, hframe, hpair⟩
  cases stmt with
  | nop =>
    refine ⟨fun _ h => ?_, ⟨fun ⟨_, h⟩ => by contradiction, fun ⟨_, h⟩ => by contradiction⟩⟩
    injection h with hs; subst hs
    exact ⟨tgt, rfl, hrel0⟩
  | storageLiveScalar l =>
    dsimp [StmtSroaAdmitted] at hadm
    have ⟨h12, hl1b⟩ := Bool.and_eq_true_iff.mp hadm
    have ⟨hltb, hl0b⟩ := Bool.and_eq_true_iff.mp h12
    have hlt : l ≠ target := not_beq_true_to_ne hltb
    have hl0 : l ≠ l0 := not_beq_true_to_ne hl0b
    have hl1 : l ≠ l1 := not_beq_true_to_ne hl1b
    refine ⟨fun _ h => ?_, ⟨fun ⟨_, h⟩ => by contradiction, fun ⟨_, h⟩ => by contradiction⟩⟩
    injection h with hs; subst hs
    refine ⟨_, rfl, ⟨ht0, ht1, h01, ?_, ?_⟩⟩
    · intro k hkt hk0 hk1
      cases hkl : Nat.beq k l with
      | true => have heq := Nat.eq_of_beq_eq_true hkl; subst heq; rw [updateFn_self, updateFn_self]
      | false =>
        have hne := (nat_beq_eq_false_iff k l).mp hkl
        rw [updateFn_ne _ l k _ hne, updateFn_ne _ l k _ hne]; exact hframe k hkt hk0 hk1
    · rw [updateFn_ne _ l target _ (Ne.symm hlt),
          updateFn_ne _ l l0 _ (Ne.symm hl0),
          updateFn_ne _ l l1 _ (Ne.symm hl1)]
      exact hpair
  | storageLivePair a =>
    dsimp [StmtSroaAdmitted] at hadm
    have ⟨ha0b, ha1b⟩ := Bool.and_eq_true_iff.mp hadm
    have ha0 : a ≠ l0 := not_beq_true_to_ne ha0b
    have ha1 : a ≠ l1 := not_beq_true_to_ne ha1b
    cases hat : Nat.beq a target with
    | true =>
      have heq : a = target := Nat.eq_of_beq_eq_true hat
      subst heq
      dsimp [sroaFlattenStmt]; rw [Nat.beq_refl a]
      dsimp [execSroaProg, execSroaStmt]
      refine ⟨fun _ h => ?_, ⟨fun ⟨_, h⟩ => by contradiction, fun ⟨_, h⟩ => by contradiction⟩⟩
      injection h with hs; subst hs
      refine ⟨_, rfl, ⟨ht0, ht1, h01, ?_, Or.inr ⟨none, none, ?_, ?_, ?_⟩⟩⟩
      · intro k hkt hk0 hk1
        rw [updateFn_ne _ a k _ hkt, updateFn_ne _ l1 k _ hk1, updateFn_ne _ l0 k _ hk0]
        exact hframe k hkt hk0 hk1
      · exact updateFn_self src a (.livePair none none)
      · rw [updateFn_ne _ l1 l0 _ h01, updateFn_self]
      · exact updateFn_self _ l1 (SroaSlot.liveScalar none)
    | false =>
      have hne : a ≠ target := (nat_beq_eq_false_iff a target).mp hat
      dsimp [sroaFlattenStmt]; rw [hat]
      dsimp [execSroaProg, execSroaStmt]
      refine ⟨fun _ h => ?_, ⟨fun ⟨_, h⟩ => by contradiction, fun ⟨_, h⟩ => by contradiction⟩⟩
      injection h with hs; subst hs
      refine ⟨_, rfl, ⟨ht0, ht1, h01, ?_, ?_⟩⟩
      · intro k hkt hk0 hk1
        cases hka : Nat.beq k a with
        | true => have heq := Nat.eq_of_beq_eq_true hka; subst heq; rw [updateFn_self, updateFn_self]
        | false =>
          have hnea := (nat_beq_eq_false_iff k a).mp hka
          rw [updateFn_ne _ a k _ hnea, updateFn_ne _ a k _ hnea]; exact hframe k hkt hk0 hk1
      · rw [updateFn_ne _ a target _ (Ne.symm hne),
            updateFn_ne _ a l0 _ (Ne.symm ha0),
            updateFn_ne _ a l1 _ (Ne.symm ha1)]
        exact hpair
  | storageDead a =>
    dsimp [StmtSroaAdmitted] at hadm
    have ⟨ha0b, ha1b⟩ := Bool.and_eq_true_iff.mp hadm
    have ha0 : a ≠ l0 := not_beq_true_to_ne ha0b
    have ha1 : a ≠ l1 := not_beq_true_to_ne ha1b
    cases hat : Nat.beq a target with
    | true =>
      have heq : a = target := Nat.eq_of_beq_eq_true hat
      subst heq
      dsimp [sroaFlattenStmt]; rw [Nat.beq_refl a]
      dsimp [execSroaProg, execSroaStmt]
      refine ⟨fun _ h => ?_, ⟨fun ⟨_, h⟩ => by contradiction, fun ⟨_, h⟩ => by contradiction⟩⟩
      injection h with hs; subst hs
      refine ⟨_, rfl, ⟨ht0, ht1, h01, ?_, Or.inl ⟨?_, ?_, ?_⟩⟩⟩
      · intro k hkt hk0 hk1
        rw [updateFn_ne _ a k _ hkt, updateFn_ne _ l1 k _ hk1, updateFn_ne _ l0 k _ hk0]
        exact hframe k hkt hk0 hk1
      · exact updateFn_self src a .dead
      · rw [updateFn_ne _ l1 l0 _ h01, updateFn_self]
      · exact updateFn_self _ l1 SroaSlot.dead
    | false =>
      have hne : a ≠ target := (nat_beq_eq_false_iff a target).mp hat
      dsimp [sroaFlattenStmt]; rw [hat]
      dsimp [execSroaProg, execSroaStmt]
      refine ⟨fun _ h => ?_, ⟨fun ⟨_, h⟩ => by contradiction, fun ⟨_, h⟩ => by contradiction⟩⟩
      injection h with hs; subst hs
      refine ⟨_, rfl, ⟨ht0, ht1, h01, ?_, ?_⟩⟩
      · intro k hkt hk0 hk1
        cases hka : Nat.beq k a with
        | true => have heq := Nat.eq_of_beq_eq_true hka; subst heq; rw [updateFn_self, updateFn_self]
        | false =>
          have hnea := (nat_beq_eq_false_iff k a).mp hka
          rw [updateFn_ne _ a k _ hnea, updateFn_ne _ a k _ hnea]; exact hframe k hkt hk0 hk1
      · rw [updateFn_ne _ a target _ (Ne.symm hne),
            updateFn_ne _ a l0 _ (Ne.symm ha0),
            updateFn_ne _ a l1 _ (Ne.symm ha1)]
        exact hpair
  | assignScalar dst op =>
    dsimp [StmtSroaAdmitted] at hadm
    have ⟨hd123, hopAdm⟩ := Bool.and_eq_true_iff.mp hadm
    have ⟨hd12, hd1b⟩ := Bool.and_eq_true_iff.mp hd123
    have ⟨hdtb, hd0b⟩ := Bool.and_eq_true_iff.mp hd12
    have hdt : dst ≠ target := not_beq_true_to_ne hdtb
    have hd0 : dst ≠ l0 := not_beq_true_to_ne hd0b
    have hd1 : dst ≠ l1 := not_beq_true_to_ne hd1b
    have ⟨hopOk, hopUb⟩ := sroaFlattenOp_bisim deinitOnMove target l0 l1 src tgt op hrel0 hopAdm
    dsimp [sroaFlattenStmt, execSroaProg, execSroaStmt]
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · intro _ h
      cases hev : evalSroaScalarOp deinitOnMove src op with
      | ub _ => rw [hev] at h; contradiction
      | ok pair =>
        rcases pair with ⟨n, src1⟩
        rw [hev] at h; dsimp at h
        rcases hopOk n src1 hev with ⟨tgt1, hevTgt, hrel1⟩
        rw [hevTgt]; dsimp
        rcases hrel1 with ⟨_, _, _, hframe1, hpair1⟩
        rw [← hframe1 dst hdt hd0 hd1]
        cases hsd : src1 dst with
        | dead | livePair _ _ => rw [hsd] at h; contradiction
        | liveScalar _ =>
          rw [hsd] at h; injection h with hs; subst hs
          refine ⟨_, rfl, ⟨ht0, ht1, h01, ?_, ?_⟩⟩
          · intro k hkt hk0 hk1
            cases hkd : Nat.beq k dst with
            | true => have heq := Nat.eq_of_beq_eq_true hkd; subst heq; rw [updateFn_self, updateFn_self]
            | false =>
              have hne := (nat_beq_eq_false_iff k dst).mp hkd
              rw [updateFn_ne _ dst k _ hne, updateFn_ne _ dst k _ hne]; exact hframe1 k hkt hk0 hk1
          · rw [updateFn_ne _ dst target _ (Ne.symm hdt),
                updateFn_ne _ dst l0 _ (Ne.symm hd0),
                updateFn_ne _ dst l1 _ (Ne.symm hd1)]
            exact hpair1
    · rintro ⟨_, h⟩
      cases hev : evalSroaScalarOp deinitOnMove src op with
      | ub e =>
        rcases hopUb e hev with ⟨e', hevTgt, _⟩
        rw [hevTgt]; exact ⟨e', rfl⟩
      | ok pair =>
        rcases pair with ⟨n, src1⟩
        rw [hev] at h; dsimp at h
        rcases hopOk n src1 hev with ⟨tgt1, hevTgt, hrel1⟩
        rw [hevTgt]; dsimp
        rcases hrel1 with ⟨_, _, _, hframe1, _⟩
        rw [← hframe1 dst hdt hd0 hd1]
        cases hsd : src1 dst with
        | dead => exact ⟨.deadSlot dst, rfl⟩
        | livePair _ _ => exact ⟨.typeMismatch, rfl⟩
        | liveScalar _ => rw [hsd] at h; contradiction
    · rintro ⟨_, h⟩
      cases hev : evalSroaScalarOp deinitOnMove src op with
      | ub e => exact ⟨e, rfl⟩
      | ok pair =>
        rcases pair with ⟨n, src1⟩
        rcases hopOk n src1 hev with ⟨tgt1, hevTgt, hrel1⟩
        rw [hevTgt] at h; dsimp at h
        rcases hrel1 with ⟨_, _, _, hframe1, _⟩
        rw [← hframe1 dst hdt hd0 hd1] at h
        dsimp
        cases hsd : src1 dst with
        | dead => exact ⟨.deadSlot dst, rfl⟩
        | livePair _ _ => exact ⟨.typeMismatch, rfl⟩
        | liveScalar _ => rw [hsd] at h; contradiction
  | assignField agg fld op =>
    dsimp [StmtSroaAdmitted] at hadm
    have ⟨ha01, hopAdm⟩ := Bool.and_eq_true_iff.mp hadm
    have ⟨ha0b, ha1b⟩ := Bool.and_eq_true_iff.mp ha01
    have ha0 : agg ≠ l0 := not_beq_true_to_ne ha0b
    have ha1 : agg ≠ l1 := not_beq_true_to_ne ha1b
    have ⟨hopOk, hopUb⟩ := sroaFlattenOp_bisim deinitOnMove target l0 l1 src tgt op hrel0 hopAdm
    cases hat : Nat.beq agg target with
    | true =>
      have heq : agg = target := Nat.eq_of_beq_eq_true hat
      subst heq
      cases fld with
      | f0 =>
        dsimp [sroaFlattenStmt]; rw [Nat.beq_refl agg]
        dsimp [execSroaProg, execSroaStmt]
        refine ⟨?_, ⟨?_, ?_⟩⟩
        · intro _ h
          cases hev : evalSroaScalarOp deinitOnMove src op with
          | ub _ => rw [hev] at h; contradiction
          | ok pair =>
            rcases pair with ⟨n, src1⟩
            rw [hev] at h; dsimp at h
            rcases hopOk n src1 hev with ⟨tgt1, hevTgt, hrel1⟩
            rw [hevTgt]; dsimp
            rcases hrel1 with ⟨_, _, _, hframe1, hpair1⟩
            rcases hpair1 with ⟨hsd, _, _⟩ | ⟨_, o1, hsp, htl0, htl1⟩
            · rw [hsd] at h; contradiction
            · rw [hsp] at h; injection h with hs; subst hs
              rw [htl0]
              refine ⟨_, rfl, ⟨ht0, ht1, h01, ?_, Or.inr ⟨some n, o1, ?_, ?_, ?_⟩⟩⟩
              · intro k hkt hk0 hk1
                rw [updateFn_ne _ agg k _ hkt, updateFn_ne _ l0 k _ hk0]
                exact hframe1 k hkt hk0 hk1
              · exact updateFn_self src1 agg (.livePair (some n) o1)
              · exact updateFn_self tgt1 l0 (.liveScalar (some n))
              · rw [updateFn_ne _ l0 l1 _ (Ne.symm h01)]; exact htl1
        · rintro ⟨_, h⟩
          cases hev : evalSroaScalarOp deinitOnMove src op with
          | ub e =>
            rcases hopUb e hev with ⟨e', hevTgt, _⟩
            rw [hevTgt]; exact ⟨e', rfl⟩
          | ok pair =>
            rcases pair with ⟨n, src1⟩
            rw [hev] at h; dsimp at h
            rcases hopOk n src1 hev with ⟨tgt1, hevTgt, hrel1⟩
            rw [hevTgt]; dsimp
            rcases hrel1 with ⟨_, _, _, _, hpair1⟩
            rcases hpair1 with ⟨_, ht0d, _⟩ | ⟨_, _, hsp, _, _⟩
            · rw [ht0d]; exact ⟨.deadSlot l0, rfl⟩
            · rw [hsp] at h; contradiction
        · rintro ⟨_, h⟩
          cases hev : evalSroaScalarOp deinitOnMove src op with
          | ub e => exact ⟨e, rfl⟩
          | ok pair =>
            rcases pair with ⟨n, src1⟩
            rcases hopOk n src1 hev with ⟨tgt1, hevTgt, hrel1⟩
            rw [hevTgt] at h; dsimp at h
            dsimp
            rcases hrel1 with ⟨_, _, _, _, hpair1⟩
            rcases hpair1 with ⟨hsd, _, _⟩ | ⟨_, _, _, htl0, _⟩
            · rw [hsd]; exact ⟨.deadSlot agg, rfl⟩
            · rw [htl0] at h; contradiction
      | f1 =>
        dsimp [sroaFlattenStmt]; rw [Nat.beq_refl agg]
        dsimp [execSroaProg, execSroaStmt]
        refine ⟨?_, ⟨?_, ?_⟩⟩
        · intro _ h
          cases hev : evalSroaScalarOp deinitOnMove src op with
          | ub _ => rw [hev] at h; contradiction
          | ok pair =>
            rcases pair with ⟨n, src1⟩
            rw [hev] at h; dsimp at h
            rcases hopOk n src1 hev with ⟨tgt1, hevTgt, hrel1⟩
            rw [hevTgt]; dsimp
            rcases hrel1 with ⟨_, _, _, hframe1, hpair1⟩
            rcases hpair1 with ⟨hsd, _, _⟩ | ⟨o0, _, hsp, htl0, htl1⟩
            · rw [hsd] at h; contradiction
            · rw [hsp] at h; injection h with hs; subst hs
              rw [htl1]
              refine ⟨_, rfl, ⟨ht0, ht1, h01, ?_, Or.inr ⟨o0, some n, ?_, ?_, ?_⟩⟩⟩
              · intro k hkt hk0 hk1
                rw [updateFn_ne _ agg k _ hkt, updateFn_ne _ l1 k _ hk1]
                exact hframe1 k hkt hk0 hk1
              · exact updateFn_self src1 agg (.livePair o0 (some n))
              · rw [updateFn_ne _ l1 l0 _ h01]; exact htl0
              · exact updateFn_self tgt1 l1 (.liveScalar (some n))
        · rintro ⟨_, h⟩
          cases hev : evalSroaScalarOp deinitOnMove src op with
          | ub e =>
            rcases hopUb e hev with ⟨e', hevTgt, _⟩
            rw [hevTgt]; exact ⟨e', rfl⟩
          | ok pair =>
            rcases pair with ⟨n, src1⟩
            rw [hev] at h; dsimp at h
            rcases hopOk n src1 hev with ⟨tgt1, hevTgt, hrel1⟩
            rw [hevTgt]; dsimp
            rcases hrel1 with ⟨_, _, _, _, hpair1⟩
            rcases hpair1 with ⟨_, _, ht1d⟩ | ⟨_, _, hsp, _, _⟩
            · rw [ht1d]; exact ⟨.deadSlot l1, rfl⟩
            · rw [hsp] at h; contradiction
        · rintro ⟨_, h⟩
          cases hev : evalSroaScalarOp deinitOnMove src op with
          | ub e => exact ⟨e, rfl⟩
          | ok pair =>
            rcases pair with ⟨n, src1⟩
            rcases hopOk n src1 hev with ⟨tgt1, hevTgt, hrel1⟩
            rw [hevTgt] at h; dsimp at h
            dsimp
            rcases hrel1 with ⟨_, _, _, _, hpair1⟩
            rcases hpair1 with ⟨hsd, _, _⟩ | ⟨_, _, _, _, htl1⟩
            · rw [hsd]; exact ⟨.deadSlot agg, rfl⟩
            · rw [htl1] at h; contradiction
    | false =>
      have hne : agg ≠ target := (nat_beq_eq_false_iff agg target).mp hat
      dsimp [sroaFlattenStmt]; rw [hat]
      dsimp [execSroaProg, execSroaStmt]
      refine ⟨?_, ⟨?_, ?_⟩⟩
      · intro _ h
        cases hev : evalSroaScalarOp deinitOnMove src op with
        | ub _ => rw [hev] at h; contradiction
        | ok pair =>
          rcases pair with ⟨n, src1⟩
          rw [hev] at h; dsimp at h
          rcases hopOk n src1 hev with ⟨tgt1, hevTgt, hrel1⟩
          rw [hevTgt]; dsimp
          rcases hrel1 with ⟨_, _, _, hframe1, hpair1⟩
          rw [← hframe1 agg hne ha0 ha1]
          cases hsa : src1 agg with
          | dead | liveScalar _ => rw [hsa] at h; contradiction
          | livePair _ _ =>
            rw [hsa] at h
            cases fld <;> {
              injection h with hs; subst hs
              refine ⟨_, rfl, ⟨ht0, ht1, h01, ?_, ?_⟩⟩
              · intro k hkt hk0 hk1
                cases hka : Nat.beq k agg with
                | true => have heq := Nat.eq_of_beq_eq_true hka; subst heq; rw [updateFn_self, updateFn_self]
                | false =>
                  have hnea := (nat_beq_eq_false_iff k agg).mp hka
                  rw [updateFn_ne _ agg k _ hnea, updateFn_ne _ agg k _ hnea]; exact hframe1 k hkt hk0 hk1
              · rw [updateFn_ne _ agg target _ (Ne.symm hne),
                    updateFn_ne _ agg l0 _ (Ne.symm ha0),
                    updateFn_ne _ agg l1 _ (Ne.symm ha1)]
                exact hpair1
            }
      · rintro ⟨_, h⟩
        cases hev : evalSroaScalarOp deinitOnMove src op with
        | ub e =>
          rcases hopUb e hev with ⟨e', hevTgt, _⟩
          rw [hevTgt]; exact ⟨e', rfl⟩
        | ok pair =>
          rcases pair with ⟨n, src1⟩
          rw [hev] at h; dsimp at h
          rcases hopOk n src1 hev with ⟨tgt1, hevTgt, hrel1⟩
          rw [hevTgt]; dsimp
          rcases hrel1 with ⟨_, _, _, hframe1, _⟩
          rw [← hframe1 agg hne ha0 ha1]
          cases hsa : src1 agg with
          | dead => exact ⟨.deadSlot agg, rfl⟩
          | liveScalar _ => exact ⟨.typeMismatch, rfl⟩
          | livePair _ _ => rw [hsa] at h; cases fld <;> contradiction
      · rintro ⟨_, h⟩
        cases hev : evalSroaScalarOp deinitOnMove src op with
        | ub e => exact ⟨e, rfl⟩
        | ok pair =>
          rcases pair with ⟨n, src1⟩
          rcases hopOk n src1 hev with ⟨tgt1, hevTgt, hrel1⟩
          rw [hevTgt] at h; dsimp at h
          rcases hrel1 with ⟨_, _, _, hframe1, _⟩
          rw [← hframe1 agg hne ha0 ha1] at h
          dsimp
          cases hsa : src1 agg with
          | dead => exact ⟨.deadSlot agg, rfl⟩
          | liveScalar _ => exact ⟨.typeMismatch, rfl⟩
          | livePair _ _ => rw [hsa] at h; cases fld <;> contradiction
  | assignAggregate dst op0 op1 =>
    dsimp [StmtSroaAdmitted] at hadm
    have ⟨hleft, hselfGuard⟩ := Bool.and_eq_true_iff.mp hadm
    have ⟨hleft2, hop1Adm⟩ := Bool.and_eq_true_iff.mp hleft
    have ⟨hd01, hop0Adm⟩ := Bool.and_eq_true_iff.mp hleft2
    have ⟨hd0b, hd1b⟩ := Bool.and_eq_true_iff.mp hd01
    have hd0 : dst ≠ l0 := not_beq_true_to_ne hd0b
    have hd1 : dst ≠ l1 := not_beq_true_to_ne hd1b
    have ⟨hop0Ok, hop0Ub⟩ := sroaFlattenOp_bisim deinitOnMove target l0 l1 src tgt op0 hrel0 hop0Adm
    cases hdt : Nat.beq dst target with
    | true =>
      have heq : dst = target := Nat.eq_of_beq_eq_true hdt
      subst heq
      rw [Nat.beq_refl dst] at hselfGuard
      have ⟨_, hop1NoRead⟩ := Bool.and_eq_true_iff.mp hselfGuard
      dsimp [sroaFlattenStmt]; rw [Nat.beq_refl dst]
      dsimp [execSroaProg, execSroaStmt]
      refine ⟨?_, ⟨?_, ?_⟩⟩
      · intro _ h
        cases hev0 : evalSroaScalarOp deinitOnMove src op0 with
        | ub _ => rw [hev0] at h; contradiction
        | ok p0 =>
          rcases p0 with ⟨n0, src1⟩
          rw [hev0] at h; dsimp at h
          rcases hop0Ok n0 src1 hev0 with ⟨tgt1, hev0Tgt, hrel1⟩
          rw [hev0Tgt]; dsimp
          have ⟨hop1Ok, _⟩ := sroaFlattenOp_bisim deinitOnMove dst l0 l1 src1 tgt1 op1 hrel1 hop1Adm
          cases hev1 : evalSroaScalarOp deinitOnMove src1 op1 with
          | ub _ => rw [hev1] at h; contradiction
          | ok p1 =>
            rcases p1 with ⟨n1, src2⟩
            rw [hev1] at h; dsimp at h
            rcases hop1Ok n1 src2 hev1 with ⟨tgt2, hev1Tgt, hrel2⟩
            rcases hrel1 with ⟨_, _, _, _, hpair1⟩
            rcases hrel2 with ⟨_, _, _, hframe2, hpair2⟩
            rcases hpair2 with ⟨hsd2, _, _⟩ | ⟨_, _, hsp2, _, htl2_1⟩
            · rw [hsd2] at h; contradiction
            · rcases hpair1 with ⟨hsd1, _, _⟩ | ⟨_, _, _, htl1_0, _⟩
              · have hdeadPres :=
                  evalSroaScalarOp_preserves_target_slot deinitOnMove dst l0 l1 src1 src2 op1 n1 hop1Adm hop1NoRead hev1
                rw [hdeadPres, hsd1] at hsp2; contradiction
              · rw [htl1_0]; dsimp
                have ⟨hflatId, hframeEvOk, _⟩ :=
                  evalSroaScalarOp_frame_l0 deinitOnMove dst l0 l1 tgt1 (.liveScalar (some n0)) op1 hop1Adm hop1NoRead
                rw [hflatId] at hev1Tgt ⊢
                rw [hframeEvOk n1 tgt2 hev1Tgt]; dsimp
                rw [updateFn_ne _ l0 l1 _ (Ne.symm h01), htl2_1]; dsimp
                rw [hsp2] at h; injection h with hs; subst hs
                refine ⟨_, rfl, ⟨ht0, ht1, h01, ?_, Or.inr ⟨some n0, some n1, ?_, ?_, ?_⟩⟩⟩
                · intro k hkt hk0 hk1
                  rw [updateFn_ne _ dst k _ hkt, updateFn_ne _ l1 k _ hk1, updateFn_ne _ l0 k _ hk0]
                  exact hframe2 k hkt hk0 hk1
                · exact updateFn_self src2 dst (.livePair (some n0) (some n1))
                · rw [updateFn_ne _ l1 l0 _ h01, updateFn_self]
                · exact updateFn_self _ l1 (SroaSlot.liveScalar (some n1))
      · rintro ⟨_, h⟩
        cases hev0 : evalSroaScalarOp deinitOnMove src op0 with
        | ub e =>
          rcases hop0Ub e hev0 with ⟨e', hev0Tgt, _⟩
          rw [hev0Tgt]; exact ⟨e', rfl⟩
        | ok p0 =>
          rcases p0 with ⟨n0, src1⟩
          rw [hev0] at h; dsimp at h
          rcases hop0Ok n0 src1 hev0 with ⟨tgt1, hev0Tgt, hrel1⟩
          rw [hev0Tgt]; dsimp
          have ⟨hop1Ok, hop1Ub⟩ := sroaFlattenOp_bisim deinitOnMove dst l0 l1 src1 tgt1 op1 hrel1 hop1Adm
          have ⟨hflatId, hframeEvOk, hframeEvUb⟩ :=
            evalSroaScalarOp_frame_l0 deinitOnMove dst l0 l1 tgt1 (.liveScalar (some n0)) op1 hop1Adm hop1NoRead
          rcases hrel1 with ⟨_, _, _, _, hpair1⟩
          rcases hpair1 with ⟨_, htl1_d, _⟩ | ⟨_, _, _, htl1_0, _⟩
          · rw [htl1_d]; exact ⟨.deadSlot l0, rfl⟩
          · rw [htl1_0]; dsimp
            cases hev1 : evalSroaScalarOp deinitOnMove src1 op1 with
            | ub e1 =>
              rcases hop1Ub e1 hev1 with ⟨e1', hev1Tgt, _⟩
              rw [hflatId] at hev1Tgt ⊢
              rw [hframeEvUb e1' hev1Tgt]; exact ⟨e1', rfl⟩
            | ok p1 =>
              rcases p1 with ⟨n1, src2⟩
              rw [hev1] at h; dsimp at h
              rcases hop1Ok n1 src2 hev1 with ⟨tgt2, hev1Tgt, hrel2⟩
              rw [hflatId] at hev1Tgt ⊢
              rw [hframeEvOk n1 tgt2 hev1Tgt]; dsimp
              rcases hrel2 with ⟨_, _, _, _, hpair2⟩
              rcases hpair2 with ⟨_, _, htl2_d⟩ | ⟨_, _, hsp2, _, _⟩
              · rw [updateFn_ne _ l0 l1 _ (Ne.symm h01), htl2_d]; exact ⟨.deadSlot l1, rfl⟩
              · rw [hsp2] at h; contradiction
      · rintro ⟨_, h⟩
        cases hev0 : evalSroaScalarOp deinitOnMove src op0 with
        | ub e => exact ⟨e, rfl⟩
        | ok p0 =>
          rcases p0 with ⟨n0, src1⟩
          rcases hop0Ok n0 src1 hev0 with ⟨tgt1, hev0Tgt, hrel1⟩
          rw [hev0Tgt] at h; dsimp at h
          dsimp
          have ⟨hop1Ok, _⟩ := sroaFlattenOp_bisim deinitOnMove dst l0 l1 src1 tgt1 op1 hrel1 hop1Adm
          have ⟨hflatId, hframeEvOk, _⟩ :=
            evalSroaScalarOp_frame_l0 deinitOnMove dst l0 l1 tgt1 (.liveScalar (some n0)) op1 hop1Adm hop1NoRead
          cases hev1 : evalSroaScalarOp deinitOnMove src1 op1 with
          | ub e1 => exact ⟨e1, rfl⟩
          | ok p1 =>
            rcases p1 with ⟨n1, src2⟩
            dsimp
            rcases hop1Ok n1 src2 hev1 with ⟨tgt2, hev1Tgt, hrel2⟩
            rcases hrel1 with ⟨_, _, _, _, hpair1⟩
            rcases hrel2 with ⟨_, _, _, _, hpair2⟩
            rcases hpair2 with ⟨hsd2, _, _⟩ | ⟨_, _, hsp2, _, htl2_1⟩
            · rw [hsd2]; exact ⟨.deadSlot dst, rfl⟩
            · rcases hpair1 with ⟨hsd1, _, _⟩ | ⟨_, _, _, htl1_0, _⟩
              · have hdeadPres :=
                  evalSroaScalarOp_preserves_target_slot deinitOnMove dst l0 l1 src1 src2 op1 n1 hop1Adm hop1NoRead hev1
                rw [hdeadPres, hsd1] at hsp2; contradiction
              · rw [htl1_0] at h; dsimp at h
                rw [hflatId] at hev1Tgt h
                rw [hframeEvOk n1 tgt2 hev1Tgt] at h; dsimp at h
                rw [updateFn_ne _ l0 l1 _ (Ne.symm h01), htl2_1] at h; contradiction
    | false =>
      have hne : dst ≠ target := (nat_beq_eq_false_iff dst target).mp hdt
      dsimp [sroaFlattenStmt]; rw [hdt]
      dsimp [execSroaProg, execSroaStmt]
      refine ⟨?_, ⟨?_, ?_⟩⟩
      · intro _ h
        cases hev0 : evalSroaScalarOp deinitOnMove src op0 with
        | ub _ => rw [hev0] at h; contradiction
        | ok p0 =>
          rcases p0 with ⟨n0, src1⟩
          rw [hev0] at h; dsimp at h
          rcases hop0Ok n0 src1 hev0 with ⟨tgt1, hev0Tgt, hrel1⟩
          rw [hev0Tgt]; dsimp
          have ⟨hop1Ok, _⟩ := sroaFlattenOp_bisim deinitOnMove target l0 l1 src1 tgt1 op1 hrel1 hop1Adm
          cases hev1 : evalSroaScalarOp deinitOnMove src1 op1 with
          | ub _ => rw [hev1] at h; contradiction
          | ok p1 =>
            rcases p1 with ⟨n1, src2⟩
            rw [hev1] at h; dsimp at h
            rcases hop1Ok n1 src2 hev1 with ⟨tgt2, hev1Tgt, hrel2⟩
            rw [hev1Tgt]; dsimp
            rcases hrel2 with ⟨_, _, _, hframe2, hpair2⟩
            rw [← hframe2 dst hne hd0 hd1]
            cases hsd : src2 dst with
            | dead | liveScalar _ => rw [hsd] at h; contradiction
            | livePair _ _ =>
              rw [hsd] at h; injection h with hs; subst hs
              refine ⟨_, rfl, ⟨ht0, ht1, h01, ?_, ?_⟩⟩
              · intro k hkt hk0 hk1
                cases hkd : Nat.beq k dst with
                | true => have heq := Nat.eq_of_beq_eq_true hkd; subst heq; rw [updateFn_self, updateFn_self]
                | false =>
                  have hnea := (nat_beq_eq_false_iff k dst).mp hkd
                  rw [updateFn_ne _ dst k _ hnea, updateFn_ne _ dst k _ hnea]; exact hframe2 k hkt hk0 hk1
              · rw [updateFn_ne _ dst target _ (Ne.symm hne),
                    updateFn_ne _ dst l0 _ (Ne.symm hd0),
                    updateFn_ne _ dst l1 _ (Ne.symm hd1)]
                exact hpair2
      · rintro ⟨_, h⟩
        cases hev0 : evalSroaScalarOp deinitOnMove src op0 with
        | ub e =>
          rcases hop0Ub e hev0 with ⟨e', hev0Tgt, _⟩
          rw [hev0Tgt]; exact ⟨e', rfl⟩
        | ok p0 =>
          rcases p0 with ⟨n0, src1⟩
          rw [hev0] at h; dsimp at h
          rcases hop0Ok n0 src1 hev0 with ⟨tgt1, hev0Tgt, hrel1⟩
          rw [hev0Tgt]; dsimp
          have ⟨hop1Ok, hop1Ub⟩ := sroaFlattenOp_bisim deinitOnMove target l0 l1 src1 tgt1 op1 hrel1 hop1Adm
          cases hev1 : evalSroaScalarOp deinitOnMove src1 op1 with
          | ub e1 =>
            rcases hop1Ub e1 hev1 with ⟨e1', hev1Tgt, _⟩
            rw [hev1Tgt]; exact ⟨e1', rfl⟩
          | ok p1 =>
            rcases p1 with ⟨n1, src2⟩
            rw [hev1] at h; dsimp at h
            rcases hop1Ok n1 src2 hev1 with ⟨tgt2, hev1Tgt, hrel2⟩
            rw [hev1Tgt]; dsimp
            rcases hrel2 with ⟨_, _, _, hframe2, _⟩
            rw [← hframe2 dst hne hd0 hd1]
            cases hsd : src2 dst with
            | dead => exact ⟨.deadSlot dst, rfl⟩
            | liveScalar _ => exact ⟨.typeMismatch, rfl⟩
            | livePair _ _ => rw [hsd] at h; contradiction
      · rintro ⟨_, h⟩
        cases hev0 : evalSroaScalarOp deinitOnMove src op0 with
        | ub e => exact ⟨e, rfl⟩
        | ok p0 =>
          rcases p0 with ⟨n0, src1⟩
          rcases hop0Ok n0 src1 hev0 with ⟨tgt1, hev0Tgt, hrel1⟩
          rw [hev0Tgt] at h; dsimp at h
          dsimp
          have ⟨hop1Ok, _⟩ := sroaFlattenOp_bisim deinitOnMove target l0 l1 src1 tgt1 op1 hrel1 hop1Adm
          cases hev1 : evalSroaScalarOp deinitOnMove src1 op1 with
          | ub e1 => exact ⟨e1, rfl⟩
          | ok p1 =>
            rcases p1 with ⟨n1, src2⟩
            rcases hop1Ok n1 src2 hev1 with ⟨tgt2, hev1Tgt, hrel2⟩
            rw [hev1Tgt] at h; dsimp at h
            rcases hrel2 with ⟨_, _, _, hframe2, _⟩
            rw [← hframe2 dst hne hd0 hd1] at h
            dsimp
            cases hsd : src2 dst with
            | dead => exact ⟨.deadSlot dst, rfl⟩
            | liveScalar _ => exact ⟨.typeMismatch, rfl⟩
            | livePair _ _ => rw [hsd] at h; contradiction
  | assignPairCopyMove dst isMove srcLoc =>
    dsimp [StmtSroaAdmitted] at hadm
    have ⟨hleft, hsrcNotTargetB⟩ := Bool.and_eq_true_iff.mp hadm
    have ⟨hd01_s0, hs1b⟩ := Bool.and_eq_true_iff.mp hleft
    have ⟨hd01_inner, hs0_inner⟩ := Bool.and_eq_true_iff.mp hd01_s0
    have ⟨hd0b, hd1b⟩ := Bool.and_eq_true_iff.mp hd01_inner
    have hd0 : dst ≠ l0 := not_beq_true_to_ne hd0b
    have hd1 : dst ≠ l1 := not_beq_true_to_ne hd1b
    have hsrcNeTarget : srcLoc ≠ target := not_beq_true_to_ne hsrcNotTargetB
    have hsrcBeqFalse : Nat.beq srcLoc target = false :=
      (nat_beq_eq_false_iff srcLoc target).mpr hsrcNeTarget
    let r0 : SroaScalarOp := if isMove then .moveField srcLoc .f0 else .copyField srcLoc .f0
    let r1 : SroaScalarOp := if isMove then .moveField srcLoc .f1 else .copyField srcLoc .f1
    have hr0Adm : OpUsesNeitherFresh l0 l1 target r0 = true := by
      cases isMove <;> { dsimp [r0, OpUsesNeitherFresh]; rw [hs0_inner, hs1b]; rfl }
    have hr1Adm : OpUsesNeitherFresh l0 l1 target r1 = true := by
      cases isMove <;> { dsimp [r1, OpUsesNeitherFresh]; rw [hs0_inner, hs1b]; rfl }
    have hr0Flat : sroaFlattenOp target l0 l1 r0 = r0 := by
      cases isMove <;> { dsimp [r0, sroaFlattenOp]; rw [hsrcBeqFalse]; rfl }
    have hr1Flat : sroaFlattenOp target l0 l1 r1 = r1 := by
      cases isMove <;> { dsimp [r1, sroaFlattenOp]; rw [hsrcBeqFalse]; rfl }
    have ⟨hr0Ok, hr0Ub⟩ := sroaFlattenOp_bisim deinitOnMove target l0 l1 src tgt r0 hrel0 hr0Adm
    rw [hr0Flat] at hr0Ok hr0Ub
    cases hdt : Nat.beq dst target with
    | true =>
      have heq : dst = target := Nat.eq_of_beq_eq_true hdt
      subst heq
      dsimp [sroaFlattenStmt]
      rw [Nat.beq_refl dst, hr0Flat, hr1Flat]
      dsimp [execSroaProg, execSroaStmt]
      refine ⟨?_, ⟨?_, ?_⟩⟩
      · intro src' h
        change (match evalSroaScalarOp deinitOnMove src r0 with
          | ExecOutcome.ub err => ExecOutcome.ub err
          | ExecOutcome.ok (n0, st1) => _) = ExecOutcome.ok src' at h
        cases hev0 : evalSroaScalarOp deinitOnMove src r0 with
        | ub _ => rw [hev0] at h; contradiction
        | ok p0 =>
          rcases p0 with ⟨n0, src1⟩
          rw [hev0] at h; dsimp at h
          rcases hr0Ok n0 src1 hev0 with ⟨tgt1, hev0Tgt, hrel1⟩
          rw [hev0Tgt]; dsimp
          rcases hrel1 with ⟨_, _, _, hframe1, hpair1⟩
          rcases hpair1 with ⟨hsd1, _, _⟩ | ⟨_, o1, hsp1, htl1_0, htl1_1⟩
          · rw [hsd1] at h; contradiction
          · rw [hsp1] at h; dsimp at h
            rw [htl1_0]; dsimp
            have hrelMid : SroaBisimRel dst l0 l1
                (updateFn src1 dst (.livePair (some n0) o1))
                (updateFn tgt1 l0 (.liveScalar (some n0))) := by
              refine ⟨ht0, ht1, h01, ?_, Or.inr ⟨some n0, o1, ?_, ?_, ?_⟩⟩
              · intro k hkt hk0 hk1
                rw [updateFn_ne _ dst k _ hkt, updateFn_ne _ l0 k _ hk0]
                exact hframe1 k hkt hk0 hk1
              · exact updateFn_self src1 dst (.livePair (some n0) o1)
              · exact updateFn_self tgt1 l0 (.liveScalar (some n0))
              · rw [updateFn_ne _ l0 l1 _ (Ne.symm h01)]; exact htl1_1
            have ⟨hr1Ok, _⟩ := sroaFlattenOp_bisim deinitOnMove dst l0 l1 _ _ r1 hrelMid hr1Adm
            rw [hr1Flat] at hr1Ok
            cases hev1 : evalSroaScalarOp deinitOnMove (updateFn src1 dst (.livePair (some n0) o1)) r1 with
            | ub _ => rw [hev1] at h; contradiction
            | ok p1 =>
              rcases p1 with ⟨n1, src2⟩
              rw [hev1] at h; dsimp at h
              rcases hr1Ok n1 src2 hev1 with ⟨tgt2, hev1Tgt, hrel2⟩
              rw [hev1Tgt]; dsimp
              rcases hrel2 with ⟨_, _, _, hframe2, hpair2⟩
              rcases hpair2 with ⟨hsd2, _, _⟩ | ⟨cur0', _, hsp2, htl2_0, htl2_1⟩
              · rw [hsd2] at h; contradiction
              · rw [hsp2] at h; injection h with hs; subst hs
                rw [htl2_1]; dsimp
                refine ⟨_, rfl, ⟨ht0, ht1, h01, ?_, Or.inr ⟨cur0', some n1, ?_, ?_, ?_⟩⟩⟩
                · intro k hkt hk0 hk1
                  rw [updateFn_ne _ dst k _ hkt, updateFn_ne _ l1 k _ hk1]
                  exact hframe2 k hkt hk0 hk1
                · exact updateFn_self src2 dst (.livePair cur0' (some n1))
                · rw [updateFn_ne _ l1 l0 _ h01]; exact htl2_0
                · exact updateFn_self tgt2 l1 (.liveScalar (some n1))
      · rintro ⟨err, h⟩
        change (match evalSroaScalarOp deinitOnMove src r0 with
          | ExecOutcome.ub err => ExecOutcome.ub err
          | ExecOutcome.ok (n0, st1) => _) = ExecOutcome.ub err at h
        cases hev0 : evalSroaScalarOp deinitOnMove src r0 with
        | ub e0 =>
          rcases hr0Ub e0 hev0 with ⟨e0', hev0Tgt, _⟩
          rw [hev0Tgt]; exact ⟨e0', rfl⟩
        | ok p0 =>
          rcases p0 with ⟨n0, src1⟩
          rw [hev0] at h; dsimp at h
          rcases hr0Ok n0 src1 hev0 with ⟨tgt1, hev0Tgt, hrel1⟩
          rw [hev0Tgt]; dsimp
          rcases hrel1 with ⟨_, _, _, hframe1, hpair1⟩
          rcases hpair1 with ⟨_, htl1_d, _⟩ | ⟨_, o1, hsp1, htl1_0, htl1_1⟩
          · rw [htl1_d]; exact ⟨.deadSlot l0, rfl⟩
          · rw [hsp1] at h; dsimp at h
            rw [htl1_0]; dsimp
            have hrelMid : SroaBisimRel dst l0 l1
                (updateFn src1 dst (.livePair (some n0) o1))
                (updateFn tgt1 l0 (.liveScalar (some n0))) := by
              refine ⟨ht0, ht1, h01, ?_, Or.inr ⟨some n0, o1, ?_, ?_, ?_⟩⟩
              · intro k hkt hk0 hk1
                rw [updateFn_ne _ dst k _ hkt, updateFn_ne _ l0 k _ hk0]
                exact hframe1 k hkt hk0 hk1
              · exact updateFn_self src1 dst (.livePair (some n0) o1)
              · exact updateFn_self tgt1 l0 (.liveScalar (some n0))
              · rw [updateFn_ne _ l0 l1 _ (Ne.symm h01)]; exact htl1_1
            have ⟨hr1Ok, hr1Ub⟩ := sroaFlattenOp_bisim deinitOnMove dst l0 l1 _ _ r1 hrelMid hr1Adm
            rw [hr1Flat] at hr1Ok hr1Ub
            cases hev1 : evalSroaScalarOp deinitOnMove (updateFn src1 dst (.livePair (some n0) o1)) r1 with
            | ub e1 =>
              rcases hr1Ub e1 hev1 with ⟨e1', hev1Tgt, _⟩
              rw [hev1Tgt]; exact ⟨e1', rfl⟩
            | ok p1 =>
              rcases p1 with ⟨n1, src2⟩
              rw [hev1] at h; dsimp at h
              rcases hr1Ok n1 src2 hev1 with ⟨tgt2, hev1Tgt, hrel2⟩
              rw [hev1Tgt]; dsimp
              rcases hrel2 with ⟨_, _, _, _, hpair2⟩
              rcases hpair2 with ⟨_, _, htl2_d⟩ | ⟨_, _, hsp2, _, _⟩
              · rw [htl2_d]; exact ⟨.deadSlot l1, rfl⟩
              · rw [hsp2] at h; contradiction
      · rintro ⟨_, h⟩
        cases hev0 : evalSroaScalarOp deinitOnMove src r0 with
        | ub e0 =>
          exact ⟨e0, rfl⟩
        | ok p0 =>
          rcases p0 with ⟨n0, src1⟩
          rcases hr0Ok n0 src1 hev0 with ⟨tgt1, hev0Tgt, hrel1⟩
          rw [hev0Tgt] at h; dsimp at h
          rcases hrel1 with ⟨_, _, _, hframe1, hpair1⟩
          rcases hpair1 with ⟨hsd1, _, _⟩ | ⟨_, o1, hsp1, htl1_0, htl1_1⟩
          · refine ⟨.deadSlot dst, ?_⟩
            dsimp; rw [hsd1]
          · rw [htl1_0] at h; dsimp at h
            have hrelMid : SroaBisimRel dst l0 l1
                (updateFn src1 dst (.livePair (some n0) o1))
                (updateFn tgt1 l0 (.liveScalar (some n0))) := by
              refine ⟨ht0, ht1, h01, ?_, Or.inr ⟨some n0, o1, ?_, ?_, ?_⟩⟩
              · intro k hkt hk0 hk1
                rw [updateFn_ne _ dst k _ hkt, updateFn_ne _ l0 k _ hk0]
                exact hframe1 k hkt hk0 hk1
              · exact updateFn_self src1 dst (.livePair (some n0) o1)
              · exact updateFn_self tgt1 l0 (.liveScalar (some n0))
              · rw [updateFn_ne _ l0 l1 _ (Ne.symm h01)]; exact htl1_1
            have ⟨hr1Ok, _⟩ := sroaFlattenOp_bisim deinitOnMove dst l0 l1 _ _ r1 hrelMid hr1Adm
            rw [hr1Flat] at hr1Ok
            cases hev1 : evalSroaScalarOp deinitOnMove (updateFn src1 dst (.livePair (some n0) o1)) r1 with
            | ub e1 =>
              refine ⟨e1, ?_⟩
              dsimp; rw [hsp1]; dsimp; rw [hev1]
            | ok p1 =>
              rcases p1 with ⟨n1, src2⟩
              rcases hr1Ok n1 src2 hev1 with ⟨tgt2, hev1Tgt, hrel2⟩
              rw [hev1Tgt] at h; dsimp at h
              rcases hrel2 with ⟨_, _, _, _, hpair2⟩
              rcases hpair2 with ⟨hsd2, _, _⟩ | ⟨_, _, _, _, htl2_1⟩
              · refine ⟨.deadSlot dst, ?_⟩
                dsimp; rw [hsp1]; dsimp; rw [hev1]; dsimp; rw [hsd2]
              · rw [htl2_1] at h; contradiction
    | false =>
      have hne : dst ≠ target := (nat_beq_eq_false_iff dst target).mp hdt
      dsimp [sroaFlattenStmt]; rw [hdt]; dsimp
      rw [execSroaProg_singleton]
      dsimp [execSroaStmt]
      refine ⟨?_, ⟨?_, ?_⟩⟩
      · intro src' h
        change (match evalSroaScalarOp deinitOnMove src r0 with
          | ExecOutcome.ub err => ExecOutcome.ub err
          | ExecOutcome.ok (n0, st1) => _) = ExecOutcome.ok src' at h
        cases hev0 : evalSroaScalarOp deinitOnMove src r0 with
        | ub _ => rw [hev0] at h; contradiction
        | ok p0 =>
          rcases p0 with ⟨n0, src1⟩
          rw [hev0] at h; dsimp at h
          rcases hr0Ok n0 src1 hev0 with ⟨tgt1, hev0Tgt, hrel1⟩
          rcases hrel1 with ⟨_, _, _, hframe1, hpair1⟩
          cases hsd1 : src1 dst with
          | dead | liveScalar _ => rw [hsd1] at h; contradiction
          | livePair _ cur1 =>
            rw [hsd1] at h; dsimp at h
            have hrelMid : SroaBisimRel target l0 l1
                (updateFn src1 dst (.livePair (some n0) cur1))
                (updateFn tgt1 dst (.livePair (some n0) cur1)) := by
              refine ⟨ht0, ht1, h01, ?_, ?_⟩
              · intro k hkt hk0 hk1
                cases hkd : Nat.beq k dst with
                | true => have heq := Nat.eq_of_beq_eq_true hkd; subst heq; rw [updateFn_self, updateFn_self]
                | false =>
                  have hnea := (nat_beq_eq_false_iff k dst).mp hkd
                  rw [updateFn_ne _ dst k _ hnea, updateFn_ne _ dst k _ hnea]; exact hframe1 k hkt hk0 hk1
              · rw [updateFn_ne _ dst target _ (Ne.symm hne),
                    updateFn_ne _ dst l0 _ (Ne.symm hd0),
                    updateFn_ne _ dst l1 _ (Ne.symm hd1)]
                exact hpair1
            have ⟨hr1Ok, _⟩ := sroaFlattenOp_bisim deinitOnMove target l0 l1 _ _ r1 hrelMid hr1Adm
            rw [hr1Flat] at hr1Ok
            cases hev1 : evalSroaScalarOp deinitOnMove (updateFn src1 dst (.livePair (some n0) cur1)) r1 with
            | ub _ => rw [hev1] at h; contradiction
            | ok p1 =>
              rcases p1 with ⟨n1, src2⟩
              rw [hev1] at h; dsimp at h
              rcases hr1Ok n1 src2 hev1 with ⟨tgt2, hev1Tgt, hrel2⟩
              rcases hrel2 with ⟨_, _, _, hframe2, hpair2⟩
              cases hsd2 : src2 dst with
              | dead | liveScalar _ => rw [hsd2] at h; contradiction
              | livePair cur0' _ =>
                rw [hsd2] at h; injection h with hs; subst hs
                refine ⟨updateFn tgt2 dst (.livePair cur0' (some n1)), ?_, ⟨ht0, ht1, h01, ?_, ?_⟩⟩
                · change (match evalSroaScalarOp deinitOnMove tgt r0 with
                    | ExecOutcome.ub err => ExecOutcome.ub err
                    | ExecOutcome.ok (n0, st1) => _) = _
                  rw [hev0Tgt]; dsimp
                  rw [← hframe1 dst hne hd0 hd1, hsd1]; dsimp
                  have fold_r1 : (if isMove = true then SroaScalarOp.moveField srcLoc Field2.f1 else SroaScalarOp.copyField srcLoc Field2.f1) = r1 := rfl
                  rw [fold_r1, hev1Tgt]; dsimp
                  rw [← hframe2 dst hne hd0 hd1, hsd2]
                · intro k hkt hk0 hk1
                  cases hkd : Nat.beq k dst with
                  | true => have heq := Nat.eq_of_beq_eq_true hkd; subst heq; rw [updateFn_self, updateFn_self]
                  | false =>
                    have hnea := (nat_beq_eq_false_iff k dst).mp hkd
                    rw [updateFn_ne _ dst k _ hnea, updateFn_ne _ dst k _ hnea]; exact hframe2 k hkt hk0 hk1
                · rw [updateFn_ne _ dst target _ (Ne.symm hne),
                      updateFn_ne _ dst l0 _ (Ne.symm hd0),
                      updateFn_ne _ dst l1 _ (Ne.symm hd1)]
                  exact hpair2
      · rintro ⟨err, h⟩
        change (match evalSroaScalarOp deinitOnMove src r0 with
          | ExecOutcome.ub err => ExecOutcome.ub err
          | ExecOutcome.ok (n0, st1) => _) = ExecOutcome.ub err at h
        change ∃ err', (match evalSroaScalarOp deinitOnMove tgt r0 with
          | ExecOutcome.ub err => ExecOutcome.ub err
          | ExecOutcome.ok (n0, st1) => _) = ExecOutcome.ub err'
        cases hev0 : evalSroaScalarOp deinitOnMove src r0 with
        | ub e0 =>
          rcases hr0Ub e0 hev0 with ⟨e0', hev0Tgt, _⟩
          rw [hev0Tgt]; exact ⟨e0', rfl⟩
        | ok p0 =>
          rcases p0 with ⟨n0, src1⟩
          rw [hev0] at h; dsimp at h
          rcases hr0Ok n0 src1 hev0 with ⟨tgt1, hev0Tgt, hrel1⟩
          rw [hev0Tgt]; dsimp
          rcases hrel1 with ⟨_, _, _, hframe1, hpair1⟩
          rw [← hframe1 dst hne hd0 hd1]
          cases hsd1 : src1 dst with
          | dead => exact ⟨.deadSlot dst, rfl⟩
          | liveScalar _ => exact ⟨.typeMismatch, rfl⟩
          | livePair _ cur1 =>
            rw [hsd1] at h; dsimp at h ⊢
            have fold_r1 : (if isMove = true then SroaScalarOp.moveField srcLoc Field2.f1 else SroaScalarOp.copyField srcLoc Field2.f1) = r1 := rfl
            rw [fold_r1] at h ⊢
            have hrelMid : SroaBisimRel target l0 l1
                (updateFn src1 dst (.livePair (some n0) cur1))
                (updateFn tgt1 dst (.livePair (some n0) cur1)) := by
              refine ⟨ht0, ht1, h01, ?_, ?_⟩
              · intro k hkt hk0 hk1
                cases hkd : Nat.beq k dst with
                | true => have heq := Nat.eq_of_beq_eq_true hkd; subst heq; rw [updateFn_self, updateFn_self]
                | false =>
                  have hnea := (nat_beq_eq_false_iff k dst).mp hkd
                  rw [updateFn_ne _ dst k _ hnea, updateFn_ne _ dst k _ hnea]; exact hframe1 k hkt hk0 hk1
              · rw [updateFn_ne _ dst target _ (Ne.symm hne),
                    updateFn_ne _ dst l0 _ (Ne.symm hd0),
                    updateFn_ne _ dst l1 _ (Ne.symm hd1)]
                exact hpair1
            have ⟨hr1Ok, hr1Ub⟩ := sroaFlattenOp_bisim deinitOnMove target l0 l1 _ _ r1 hrelMid hr1Adm
            rw [hr1Flat] at hr1Ok hr1Ub
            cases hev1 : evalSroaScalarOp deinitOnMove (updateFn src1 dst (.livePair (some n0) cur1)) r1 with
            | ub e1 =>
              rcases hr1Ub e1 hev1 with ⟨e1', hev1Tgt, _⟩
              rw [hev1Tgt]; exact ⟨e1', rfl⟩
            | ok p1 =>
              rcases p1 with ⟨n1, src2⟩
              rw [hev1] at h; dsimp at h
              rcases hr1Ok n1 src2 hev1 with ⟨tgt2, hev1Tgt, hrel2⟩
              rw [hev1Tgt]; dsimp
              rcases hrel2 with ⟨_, _, _, hframe2, _⟩
              rw [← hframe2 dst hne hd0 hd1]
              cases hsd2 : src2 dst with
              | dead => exact ⟨.deadSlot dst, rfl⟩
              | liveScalar _ => exact ⟨.typeMismatch, rfl⟩
              | livePair _ _ => rw [hsd2] at h; contradiction
      · rintro ⟨err', h⟩
        change (match evalSroaScalarOp deinitOnMove tgt r0 with
          | ExecOutcome.ub err => ExecOutcome.ub err
          | ExecOutcome.ok (n0, st1) => _) = ExecOutcome.ub err' at h
        change ∃ err, (match evalSroaScalarOp deinitOnMove src r0 with
          | ExecOutcome.ub err => ExecOutcome.ub err
          | ExecOutcome.ok (n0, st1) => _) = ExecOutcome.ub err
        cases hev0 : evalSroaScalarOp deinitOnMove src r0 with
        | ub e0 => exact ⟨e0, rfl⟩
        | ok p0 =>
          rcases p0 with ⟨n0, src1⟩
          rcases hr0Ok n0 src1 hev0 with ⟨tgt1, hev0Tgt, hrel1⟩
          rw [hev0Tgt] at h; dsimp at h
          dsimp
          rcases hrel1 with ⟨_, _, _, hframe1, hpair1⟩
          rw [← hframe1 dst hne hd0 hd1] at h
          cases hsd1 : src1 dst with
          | dead => exact ⟨.deadSlot dst, rfl⟩
          | liveScalar _ => exact ⟨.typeMismatch, rfl⟩
          | livePair _ cur1 =>
            rw [hsd1] at h; dsimp at h ⊢
            have fold_r1 : (if isMove = true then SroaScalarOp.moveField srcLoc Field2.f1 else SroaScalarOp.copyField srcLoc Field2.f1) = r1 := rfl
            rw [fold_r1] at h ⊢
            have hrelMid : SroaBisimRel target l0 l1
                (updateFn src1 dst (.livePair (some n0) cur1))
                (updateFn tgt1 dst (.livePair (some n0) cur1)) := by
              refine ⟨ht0, ht1, h01, ?_, ?_⟩
              · intro k hkt hk0 hk1
                cases hkd : Nat.beq k dst with
                | true => have heq := Nat.eq_of_beq_eq_true hkd; subst heq; rw [updateFn_self, updateFn_self]
                | false =>
                  have hnea := (nat_beq_eq_false_iff k dst).mp hkd
                  rw [updateFn_ne _ dst k _ hnea, updateFn_ne _ dst k _ hnea]; exact hframe1 k hkt hk0 hk1
              · rw [updateFn_ne _ dst target _ (Ne.symm hne),
                    updateFn_ne _ dst l0 _ (Ne.symm hd0),
                    updateFn_ne _ dst l1 _ (Ne.symm hd1)]
                exact hpair1
            have ⟨hr1Ok, _⟩ := sroaFlattenOp_bisim deinitOnMove target l0 l1 _ _ r1 hrelMid hr1Adm
            rw [hr1Flat] at hr1Ok
            cases hev1 : evalSroaScalarOp deinitOnMove (updateFn src1 dst (.livePair (some n0) cur1)) r1 with
            | ub e1 => exact ⟨e1, rfl⟩
            | ok p1 =>
              rcases p1 with ⟨n1, src2⟩
              rcases hr1Ok n1 src2 hev1 with ⟨tgt2, hev1Tgt, hrel2⟩
              rw [hev1Tgt] at h; dsimp at h
              rcases hrel2 with ⟨_, _, _, hframe2, _⟩
              rw [← hframe2 dst hne hd0 hd1] at h
              dsimp
              cases hsd2 : src2 dst with
              | dead => exact ⟨.deadSlot dst, rfl⟩
              | liveScalar _ => exact ⟨.typeMismatch, rfl⟩
              | livePair _ _ => rw [hsd2] at h; contradiction

/-- **Main Theorem 2b (`sroaFlattenProg_exact_bisimulation`):**
Inductive composition of `sroaFlattenStmt_exact_bisimulation` across arbitrary
statement lists `prog`: `execSroaProg` before and after `sroaFlattenProg`
satisfies exact bidirectional state bisimulation AND exact bidirectional UB
equivalence. -/
theorem sroaFlattenProg_exact_bisimulation
    (deinitOnMove : Bool) (target l0 l1 : LocalId)
    (src tgt : SroaState) (prog : List SroaStmt)
    (hrel : SroaBisimRel target l0 l1 src tgt)
    (hadm : prog.all (StmtSroaAdmitted target l0 l1) = true) :
    (∀ src', execSroaProg deinitOnMove src prog = .ok src' →
      ∃ tgt', execSroaProg deinitOnMove tgt (sroaFlattenProg target l0 l1 prog) = .ok tgt' ∧
        SroaBisimRel target l0 l1 src' tgt') ∧
    ((∃ err, execSroaProg deinitOnMove src prog = .ub err) ↔
     (∃ err', execSroaProg deinitOnMove tgt (sroaFlattenProg target l0 l1 prog) = .ub err')) := by
  induction prog generalizing src tgt with
  | nil =>
    refine ⟨fun _ h => ?_, ⟨fun ⟨_, h⟩ => by contradiction, fun ⟨_, h⟩ => by contradiction⟩⟩
    injection h with hs; subst hs
    exact ⟨tgt, rfl, hrel⟩
  | cons s rest ih =>
    dsimp [List.all] at hadm
    have ⟨hsAdm, hrestAdm⟩ := Bool.and_eq_true_iff.mp hadm
    have ⟨hsOk, hsUbIff⟩ := sroaFlattenStmt_exact_bisimulation deinitOnMove target l0 l1 src tgt s hrel hsAdm
    dsimp [sroaFlattenProg, execSroaProg]
    rw [execSroaProg_append]
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · intro src' h
      cases hs : execSroaStmt deinitOnMove src s with
      | ub _ => rw [hs] at h; contradiction
      | ok src1 =>
        rw [hs] at h
        rcases hsOk src1 hs with ⟨tgt1, hsTgt, hrel1⟩
        rw [hsTgt]
        exact (ih src1 tgt1 hrel1 hrestAdm).1 src' h
    · rintro ⟨err, h⟩
      cases hs : execSroaStmt deinitOnMove src s with
      | ub e =>
        rcases hsUbIff.mp ⟨e, hs⟩ with ⟨e', hsTgt⟩
        rw [hsTgt]; exact ⟨e', rfl⟩
      | ok src1 =>
        rw [hs] at h
        rcases hsOk src1 hs with ⟨tgt1, hsTgt, hrel1⟩
        rw [hsTgt]
        exact (ih src1 tgt1 hrel1 hrestAdm).2.mp ⟨err, h⟩
    · rintro ⟨err', h⟩
      cases hs : execSroaStmt deinitOnMove src s with
      | ub e => exact ⟨e, rfl⟩
      | ok src1 =>
        rcases hsOk src1 hs with ⟨tgt1, hsTgt, hrel1⟩
        rw [hsTgt] at h
        exact (ih src1 tgt1 hrel1 hrestAdm).2.mpr ⟨err', h⟩

/-- Why `MaybeDangling<T>` MUST be excluded from SROA (`sroa.rs:66-68`):
Copying/moving a `MaybeDangling<&u64>` wrapper whose inner reference points to a
freed allocation (`allocLive = false`) is valid (`inMaybeDangling = true`),
whereas SROA-flattening `MaybeDangling<&u64>` into a plain `&u64` local enforces
live-allocation reference validity (`allocLive = true`) and introduces UB! -/
def checkAssignRefWrapper (inMaybeDangling : Bool) (nonNull aligned allocLive : Bool) : Bool :=
  if inMaybeDangling then true else nonNull && aligned && allocLive

theorem sroa_maybeDangling_exclusion_necessary :
    checkAssignRefWrapper true true true false = true ∧
    checkAssignRefWrapper false true true false = false :=
  ⟨rfl, rfl⟩

/-! ============================================================================
    Section 3. `ReferencePropagation` (`refProp`) Exact Bisimulation
               and Sharpness Counterexamples (`ce2`, `ce3`)
    ============================================================================ -/

abbrev BorrowId := Nat
abbrev GenId := Nat

/-- Values in the Section 3 `ReferencePropagation` operational model:
  - `scalar n`: plain integer value
  - `sharedRef target gen`: `&target` bound to stack-allocation generation `gen`
  - `mutRef target gen bid`: `&mut target` bound to stack-allocation generation
    `gen` and unique borrow capability `bid` (Stacked/Tree Borrows `Unique`/`Active`). -/
inductive RefVal where
  | scalar (n : Nat)
  | sharedRef (target : LocalId) (gen : GenId)
  | mutRef (target : LocalId) (gen : GenId) (bid : BorrowId)
  deriving DecidableEq, Repr

/-- Per-local runtime entry in Section 3. -/
structure RefLocalEntry where
  slot : LocalSlot RefVal
  gen : GenId
  activeMutBorrow : Option BorrowId
  deriving DecidableEq, Repr

/-- Machine state for Section 3. -/
structure RefMachineState where
  locals : LocalId → RefLocalEntry
  nextBorrowId : BorrowId

/-- Modeled UB kinds in Section 3. -/
inductive RefUb where
  | deadLocal (l : LocalId)
  | uninitLocal (l : LocalId)
  | danglingAfterStorageDead (target : LocalId)
  | mutBorrowAliasingViolation (target : LocalId) (bid : BorrowId)
  | typeError
  deriving DecidableEq, Repr

/-- Statements in Section 3. -/
inductive RefStmt where
  | storageLive (l : LocalId)
  | storageDead (l : LocalId)
  | assignConst (dst : LocalId) (n : Nat)
  | assignCopyLocal (dst : LocalId) (src : LocalId)
  | borrowShared (refLoc : LocalId) (target : LocalId)
  | borrowMut (refLoc : LocalId) (target : LocalId)
  | assignFromDeref (dst : LocalId) (refLoc : LocalId)
  | assignToDeref (refLoc : LocalId) (n : Nat)
  | placeMentionLocal (l : LocalId)
  | placeMentionDeref (refLoc : LocalId)
  | nop
  deriving DecidableEq, Repr

/-- Direct read of `src`: requires `src` live and initialized, AND invalidates
any active `&mut` borrow on `src` (parent access pops child `&mut`!). -/
def directReadLocal (st : RefMachineState) (src : LocalId) :
    ExecOutcome (RefVal × RefMachineState) RefUb :=
  let e := st.locals src
  match e.slot with
  | .dead => .ub (.deadLocal src)
  | .live none => .ub (.uninitLocal src)
  | .live (some v) =>
    let st' := { st with locals := updateFn st.locals src { e with activeMutBorrow := none } }
    .ok (v, st')

/-- Direct write of `v` to `dst`: requires `dst` live, AND invalidates any active
`&mut` borrow on `dst`. -/
def directWriteLocal (st : RefMachineState) (dst : LocalId) (v : RefVal) :
    ExecOutcome RefMachineState RefUb :=
  let e := st.locals dst
  match e.slot with
  | .dead => .ub (.deadLocal dst)
  | .live _ =>
    let e' : RefLocalEntry := { e with slot := .live (some v), activeMutBorrow := none }
    .ok { st with locals := updateFn st.locals dst e' }

/-- Dereference validation (`deref_pointer` in `place.rs:490-517` + `&mut`
uniqueness). -/
def resolveRefDeref (st : RefMachineState) (refLoc : LocalId) (requireMut : Bool) :
    ExecOutcome LocalId RefUb :=
  match (st.locals refLoc).slot with
  | .dead => .ub (.deadLocal refLoc)
  | .live none => .ub (.uninitLocal refLoc)
  | .live (some (.scalar _)) => .ub .typeError
  | .live (some (.sharedRef target gen)) =>
    if requireMut then .ub .typeError
    else
      let te := st.locals target
      match te.slot with
      | .dead => .ub (.danglingAfterStorageDead target)
      | .live _ =>
        if Nat.beq te.gen gen then .ok target
        else .ub (.danglingAfterStorageDead target)
  | .live (some (.mutRef target gen bid)) =>
    let te := st.locals target
    match te.slot with
    | .dead => .ub (.danglingAfterStorageDead target)
    | .live _ =>
      if !Nat.beq te.gen gen then
        .ub (.danglingAfterStorageDead target)
      else
        match te.activeMutBorrow with
        | none => .ub (.mutBorrowAliasingViolation target bid)
        | some curBid =>
          if Nat.beq curBid bid then .ok target
          else .ub (.mutBorrowAliasingViolation target bid)

/-- Execute a single `RefStmt`. -/
def execRefStmt (st : RefMachineState) (stmt : RefStmt) :
    ExecOutcome RefMachineState RefUb :=
  match stmt with
  | .nop => .ok st
  | .storageLive l =>
    let e := st.locals l
    let e' : RefLocalEntry := { slot := .live none, gen := e.gen + 1, activeMutBorrow := none }
    .ok { st with locals := updateFn st.locals l e' }
  | .storageDead l =>
    let e := st.locals l
    let e' : RefLocalEntry := { e with slot := .dead, activeMutBorrow := none }
    .ok { st with locals := updateFn st.locals l e' }
  | .assignConst dst n =>
    directWriteLocal st dst (.scalar n)
  | .assignCopyLocal dst src =>
    match directReadLocal st src with
    | .ub err => .ub err
    | .ok (v, st1) => directWriteLocal st1 dst v
  | .borrowShared refLoc target =>
    let te := st.locals target
    match te.slot with
    | .dead => .ub (.deadLocal target)
    | .live _ =>
      let st1 := { st with locals := updateFn st.locals target { te with activeMutBorrow := none } }
      directWriteLocal st1 refLoc (.sharedRef target te.gen)
  | .borrowMut refLoc target =>
    let te := st.locals target
    match te.slot with
    | .dead => .ub (.deadLocal target)
    | .live _ =>
      let bid := st.nextBorrowId
      let st1 : RefMachineState :=
        { locals := updateFn st.locals target { te with activeMutBorrow := some bid }
        , nextBorrowId := bid + 1 }
      directWriteLocal st1 refLoc (.mutRef target te.gen bid)
  | .assignFromDeref dst refLoc =>
    match resolveRefDeref st refLoc false with
    | .ub err => .ub err
    | .ok target =>
      match (st.locals target).slot with
      | .dead => .ub (.danglingAfterStorageDead target)
      | .live none => .ub (.uninitLocal target)
      | .live (some v) => directWriteLocal st dst v
  | .assignToDeref refLoc n =>
    match resolveRefDeref st refLoc true with
    | .ub err => .ub err
    | .ok target =>
      let te := st.locals target
      let te' : RefLocalEntry := { te with slot := .live (some (.scalar n)) }
      .ok { st with locals := updateFn st.locals target te' }
  | .placeMentionLocal _ => .ok st
  | .placeMentionDeref refLoc =>
    match resolveRefDeref st refLoc false with
    | .ub err => .ub err
    | .ok _ => .ok st

noncomputable def execRefProg (st : RefMachineState) :
    List RefStmt → ExecOutcome RefMachineState RefUb
  | [] => .ok st
  | s :: rest =>
    match execRefStmt st s with
    | .ub err => .ub err
    | .ok st' => execRefProg st' rest

/-- Shared-reference `ReferencePropagation` substitution (`ref_prop.rs:71-72, 432-453`):
replaces shared-reference dereferences `*refLoc` (`assignFromDeref`, `placeMentionDeref`)
with direct `target` without needing to delete `refLoc = &target`. -/
def refPropSharedStmt (refLoc target : LocalId) (stmt : RefStmt) : RefStmt :=
  match stmt with
  | .assignFromDeref dst r =>
    if Nat.beq r refLoc then .assignCopyLocal dst target else stmt
  | .placeMentionDeref r =>
    if Nat.beq r refLoc then .placeMentionLocal target else stmt
  | _ => stmt

/-- **Main Theorem 3a (`refProp_shared_exact_bisimulation`):**
When `refLoc` holds `.sharedRef target gen` at `target`'s current generation `gen`
(`singleStorageLive`), `target` is guaranteed live (`!maybeStorageDead`), and
`target` has no active `&mut` borrow (`activeMutBorrow = none`), `refPropSharedStmt`
preserves **exact** state and UB identity (`execRefStmt` before == after). -/
theorem refProp_shared_exact_bisimulation
    (st : RefMachineState) (refLoc target : LocalId) (gen : GenId)
    (optTarget : Option RefVal) (stmt : RefStmt)
    (href : (st.locals refLoc).slot = .live (some (.sharedRef target gen)))
    (hlive : (st.locals target).slot = .live optTarget)
    (hgen : (st.locals target).gen = gen)
    (hnoMut : (st.locals target).activeMutBorrow = none) :
    execRefStmt st (refPropSharedStmt refLoc target stmt) =
      execRefStmt st stmt := by
  have htEntry : st.locals target =
      { slot := .live optTarget, gen := gen, activeMutBorrow := none } := by
    cases hte : st.locals target
    rw [hte] at hlive hgen hnoMut
    dsimp at hlive hgen hnoMut
    subst hlive hgen hnoMut
    rfl
  have hnoopTargetUpdate :
      updateFn st.locals target { st.locals target with activeMutBorrow := none } =
        st.locals := by
    funext x
    cases hxt : Nat.beq x target with
    | true =>
      have heq := Nat.eq_of_beq_eq_true hxt
      subst heq
      rw [updateFn_self, htEntry]
    | false =>
      have hne := (nat_beq_eq_false_iff x target).mp hxt
      exact updateFn_ne st.locals target x _ hne
  cases stmt with
  | nop | storageLive _ | storageDead _ | assignConst _ _
  | assignCopyLocal _ _ | borrowShared _ _ | borrowMut _ _
  | assignToDeref _ _ | placeMentionLocal _ =>
    rfl
  | assignFromDeref dst r =>
    dsimp [refPropSharedStmt]
    cases hrr : Nat.beq r refLoc with
    | false => rfl
    | true =>
      have heq : r = refLoc := Nat.eq_of_beq_eq_true hrr
      subst heq
      dsimp [execRefStmt, resolveRefDeref, directReadLocal]
      rw [href]; dsimp; rw [hlive]; dsimp; rw [hgen, Nat.beq_refl gen]; dsimp
      rw [hlive]
      cases optTarget with
      | none => rfl
      | some v =>
        dsimp
        rw [htEntry] at hnoopTargetUpdate
        rw [hnoopTargetUpdate]
  | placeMentionDeref r =>
    dsimp [refPropSharedStmt]
    cases hrr : Nat.beq r refLoc with
    | false => rfl
    | true =>
      have heq : r = refLoc := Nat.eq_of_beq_eq_true hrr
      subst heq
      dsimp [execRefStmt, resolveRefDeref]
      rw [href]; dsimp; rw [hlive]; dsimp; rw [hgen, Nat.beq_refl gen]; rfl

/-- All-or-nothing `&mut` `ReferencePropagation` over an entire SSA copy-equivalence
class `inClass : LocalId → Bool` (`fully_replaceable_locals` +
`ssa.meet_copy_equivalence`, `ref_prop.rs:361-375`, followed by
`remove_unused_definitions`, `ref_prop.rs:132`):
  - Every `r` in `inClass` has all derefs (`*r`) rewritten to `target` AND its
    copy-propagation assignments `r2 = copy r1` (for `inClass r2 && inClass r1`)
    rewritten to `.nop`. -/
def refPropMutStmt (inClass : LocalId → Bool) (target : LocalId)
    (stmt : RefStmt) : RefStmt :=
  match stmt with
  | .assignCopyLocal dst src =>
    if inClass dst && inClass src then .nop else stmt
  | .assignFromDeref dst r =>
    if inClass r then .assignCopyLocal dst target else stmt
  | .assignToDeref r n =>
    if inClass r then .assignConst target n else stmt
  | .placeMentionDeref r =>
    if inClass r then .placeMentionLocal target else stmt
  | _ => stmt

/-- Syntactic admissibility of statements inside the live lifetime of a
fully-replaceable `&mut target` copy-equivalence class `inClass`:
  1. `inClass target = false` (`assert_ne!(place.local, local)` in `ref_prop.rs:275`),
  2. Locals in `inClass` are NEVER used directly outside intra-class copies
     (`ssa.num_direct_uses == 0` after `meet_copy_equivalence`, `ssa.rs:346, 366`)
     and are SSA (never overwritten or `StorageDead` inside the region),
  3. While `inClass` still has live dereference uses, `target` is NEVER directly
     read, written, reborrowed, or `StorageDead` (`!maybeStorageDead`). -/
def MutClassStmtAdmitted (inClass : LocalId → Bool) (target : LocalId) :
    RefStmt → Bool
  | .nop => true
  | .storageLive l | .storageDead l =>
    !inClass l && !Nat.beq l target
  | .assignConst dst _ =>
    !inClass dst && !Nat.beq dst target
  | .assignCopyLocal dst src =>
    if inClass dst then
      inClass src
    else
      !inClass src && !Nat.beq dst target && !Nat.beq src target
  | .borrowShared refLoc t =>
    !inClass refLoc && !inClass t && !Nat.beq refLoc target && !Nat.beq t target
  | .borrowMut _ _ =>
    false
  | .assignFromDeref dst r =>
    !inClass dst && !Nat.beq dst target && inClass r
  | .assignToDeref r _ =>
    inClass r
  | .placeMentionLocal l =>
    !inClass l
  | .placeMentionDeref r =>
    inClass r

/-- Coupling relation between `src` (executing with active `&mut target` capability
`bid` held by initialized class members `initialized : LocalId → Bool`) and `tgt`
(executing with `&mut target` completely eliminated and `activeMutBorrow = none`). -/
def MutRefBisimRel (inClass : LocalId → Bool) (initialized : LocalId → Bool)
    (target : LocalId) (gen : GenId) (bid : BorrowId)
    (src tgt : RefMachineState) : Prop :=
  inClass target = false ∧
  (∀ k, inClass k = false → k ≠ target → src.locals k = tgt.locals k) ∧
  (∀ r, inClass r = true →
    (initialized r = true → (src.locals r).slot = .live (some (.mutRef target gen bid))) ∧
    (initialized r = false → ∃ opt, (src.locals r).slot = .live opt)) ∧
  (∃ optT,
    src.locals target = { slot := .live optT, gen := gen, activeMutBorrow := some bid } ∧
    tgt.locals target = { slot := .live optT, gen := gen, activeMutBorrow := none })

/-- Next `initialized` map after executing `stmt` (marks `dst` initialized on
intra-class `dst = copy src` when `initialized src = true`). -/
def stepInitClass (inClass initialized : LocalId → Bool) : RefStmt → (LocalId → Bool)
  | .assignCopyLocal dst src =>
    if inClass dst && inClass src then updateFn initialized dst true
    else initialized
  | _ => initialized

/-- All dereferences of `inClass` locals in `stmt` read an already-initialized
member of `inClass` (SSA dominance: `ssa.rs:121-130`). -/
def MutClassSsaDominated (inClass initialized : LocalId → Bool) : RefStmt → Bool
  | .assignCopyLocal dst src =>
    if inClass dst then initialized src else true
  | .assignFromDeref _ r | .assignToDeref r _ | .placeMentionDeref r =>
    if inClass r then initialized r else true
  | _ => true

/-- Single-step bisimulation for all-or-nothing `&mut` `ReferencePropagation`. -/
theorem refProp_mut_step_bisimulation
    (inClass initialized : LocalId → Bool) (target : LocalId)
    (gen : GenId) (bid : BorrowId)
    (src tgt : RefMachineState) (stmt : RefStmt)
    (hrel : MutRefBisimRel inClass initialized target gen bid src tgt)
    (hadm : MutClassStmtAdmitted inClass target stmt = true)
    (hdom : MutClassSsaDominated inClass initialized stmt = true) :
    (∀ src', execRefStmt src stmt = .ok src' →
      ∃ tgt', execRefStmt tgt (refPropMutStmt inClass target stmt) = .ok tgt' ∧
        MutRefBisimRel inClass (stepInitClass inClass initialized stmt) target gen bid src' tgt') ∧
    (∀ err, execRefStmt src stmt = .ub err ↔
      execRefStmt tgt (refPropMutStmt inClass target stmt) = .ub err) := by
  rcases hrel with ⟨htNotClass, hframe, hclass, ⟨optT, hsrcT, htgtT⟩⟩
  have hnoopTgtTarget :
      updateFn tgt.locals target { tgt.locals target with activeMutBorrow := none } =
        tgt.locals := by
    funext x
    cases hxt : Nat.beq x target with
    | true => have heq := Nat.eq_of_beq_eq_true hxt; subst heq; rw [updateFn_self, htgtT]
    | false => exact updateFn_ne tgt.locals target x _ ((nat_beq_eq_false_iff x target).mp hxt)
  cases stmt with
  | nop =>
    exact ⟨fun _ h => by injection h with hs; subst hs; exact ⟨tgt, rfl, ⟨htNotClass, hframe, hclass, ⟨optT, hsrcT, htgtT⟩⟩⟩,
           fun _ => ⟨fun h => by contradiction, fun h => by contradiction⟩⟩
  | placeMentionLocal l =>
    exact ⟨fun _ h => by injection h with hs; subst hs; exact ⟨tgt, rfl, ⟨htNotClass, hframe, hclass, ⟨optT, hsrcT, htgtT⟩⟩⟩,
           fun _ => ⟨fun h => by contradiction, fun h => by contradiction⟩⟩
  | storageLive l =>
    dsimp [MutClassStmtAdmitted] at hadm
    have ⟨hlNotC, hltB⟩ := Bool.and_eq_true_iff.mp hadm
    have hlC : inClass l = false := bool_not_eq_true_to_eq_false hlNotC
    have hlt : l ≠ target := not_beq_true_to_ne hltB
    have hleEq : src.locals l = tgt.locals l := hframe l hlC hlt
    refine ⟨?_, fun _ => ⟨fun h => by contradiction, fun h => by contradiction⟩⟩
    intro _ h
    dsimp [refPropMutStmt, execRefStmt] at h ⊢; injection h with hs; subst hs
    refine ⟨_, rfl, ⟨htNotClass, ?_, ?_, ⟨optT, ?_, ?_⟩⟩⟩
    · intro k hkC hkt
      dsimp
      cases hkl : Nat.beq k l with
      | true =>
        have heq := Nat.eq_of_beq_eq_true hkl; subst heq
        rw [updateFn_self, updateFn_self, hleEq]
      | false =>
        have hne := (nat_beq_eq_false_iff k l).mp hkl
        rw [updateFn_ne _ l k _ hne, updateFn_ne _ l k _ hne]
        exact hframe k hkC hkt
    · intro r hrC
      dsimp
      have hrl : r ≠ l := fun heq => by subst heq; rw [hlC] at hrC; contradiction
      rw [updateFn_ne _ l r _ hrl]; exact hclass r hrC
    · dsimp; rw [updateFn_ne _ l target _ (Ne.symm hlt)]; exact hsrcT
    · dsimp; rw [updateFn_ne _ l target _ (Ne.symm hlt)]; exact htgtT
  | storageDead l =>
    dsimp [MutClassStmtAdmitted] at hadm
    have ⟨hlNotC, hltB⟩ := Bool.and_eq_true_iff.mp hadm
    have hlC : inClass l = false := bool_not_eq_true_to_eq_false hlNotC
    have hlt : l ≠ target := not_beq_true_to_ne hltB
    have hleEq : src.locals l = tgt.locals l := hframe l hlC hlt
    refine ⟨?_, fun _ => ⟨fun h => by contradiction, fun h => by contradiction⟩⟩
    intro _ h
    dsimp [refPropMutStmt, execRefStmt] at h ⊢; injection h with hs; subst hs
    refine ⟨_, rfl, ⟨htNotClass, ?_, ?_, ⟨optT, ?_, ?_⟩⟩⟩
    · intro k hkC hkt
      dsimp
      cases hkl : Nat.beq k l with
      | true =>
        have heq := Nat.eq_of_beq_eq_true hkl; subst heq
        rw [updateFn_self, updateFn_self, hleEq]
      | false =>
        have hne := (nat_beq_eq_false_iff k l).mp hkl
        rw [updateFn_ne _ l k _ hne, updateFn_ne _ l k _ hne]
        exact hframe k hkC hkt
    · intro r hrC
      dsimp
      have hrl : r ≠ l := fun heq => by subst heq; rw [hlC] at hrC; contradiction
      rw [updateFn_ne _ l r _ hrl]; exact hclass r hrC
    · dsimp; rw [updateFn_ne _ l target _ (Ne.symm hlt)]; exact hsrcT
    · dsimp; rw [updateFn_ne _ l target _ (Ne.symm hlt)]; exact htgtT
  | assignConst dst n =>
    dsimp [MutClassStmtAdmitted] at hadm
    have ⟨hdNotC, hdtB⟩ := Bool.and_eq_true_iff.mp hadm
    have hdC : inClass dst = false := bool_not_eq_true_to_eq_false hdNotC
    have hdt : dst ≠ target := not_beq_true_to_ne hdtB
    have hdeEq : tgt.locals dst = src.locals dst := (hframe dst hdC hdt).symm
    dsimp [refPropMutStmt, execRefStmt, directWriteLocal]
    rw [hdeEq]
    cases hds : (src.locals dst).slot with
    | dead =>
      exact ⟨fun _ h => by contradiction, fun _ => Iff.rfl⟩
    | live _ =>
      refine ⟨?_, fun _ => ⟨fun h => by contradiction, fun h => by contradiction⟩⟩
      intro _ h; injection h with hs; subst hs
      refine ⟨_, rfl, ⟨htNotClass, ?_, ?_, ⟨optT, ?_, ?_⟩⟩⟩
      · intro k hkC hkt
        dsimp
        cases hkd : Nat.beq k dst with
        | true =>
          have heq := Nat.eq_of_beq_eq_true hkd; subst heq
          rw [updateFn_self, updateFn_self, hdeEq.symm]
        | false =>
          have hne := (nat_beq_eq_false_iff k dst).mp hkd
          rw [updateFn_ne _ dst k _ hne, updateFn_ne _ dst k _ hne]
          exact hframe k hkC hkt
      · intro r hrC
        dsimp
        have hrd : r ≠ dst := fun heq => by subst heq; rw [hdC] at hrC; contradiction
        rw [updateFn_ne _ dst r _ hrd]; exact hclass r hrC
      · dsimp; rw [updateFn_ne _ dst target _ (Ne.symm hdt)]; exact hsrcT
      · dsimp; rw [updateFn_ne _ dst target _ (Ne.symm hdt)]; exact htgtT
  | assignCopyLocal dst s =>
    dsimp [MutClassStmtAdmitted] at hadm
    dsimp [MutClassSsaDominated] at hdom
    cases hdC : inClass dst with
    | true =>
      rw [hdC] at hadm hdom; dsimp at hadm hdom
      dsimp [refPropMutStmt, stepInitClass]
      rw [hdC, hadm]; dsimp
      have hsSlot : (src.locals s).slot = .live (some (.mutRef target gen bid)) :=
        (hclass s hadm).1 hdom
      have hdLive : ∃ optD, (src.locals dst).slot = .live optD := by
        cases hid : initialized dst with
        | true => exact ⟨_, (hclass dst hdC).1 hid⟩
        | false => exact (hclass dst hdC).2 hid
      rcases hdLive with ⟨optD, hdSlot⟩
      dsimp [execRefStmt, directReadLocal]
      rw [hsSlot]; dsimp [directWriteLocal]
      let entryS : RefLocalEntry :=
        { slot := .live (some (.mutRef target gen bid)), gen := (src.locals s).gen, activeMutBorrow := none }
      have hdSlot1 : (updateFn src.locals s entryS dst).slot = (src.locals dst).slot := by
        cases hds : Nat.beq dst s with
        | true =>
          have heq := Nat.eq_of_beq_eq_true hds; subst heq
          rw [updateFn_self]; exact hsSlot.symm
        | false =>
          have hne := (nat_beq_eq_false_iff dst s).mp hds
          rw [updateFn_ne _ s dst _ hne]
      rw [hdSlot1, hdSlot]; dsimp
      have hst : s ≠ target := fun heq => by subst heq; rw [htNotClass] at hadm; contradiction
      have hdt : dst ≠ target := fun heq => by subst heq; rw [htNotClass] at hdC; contradiction
      refine ⟨?_, fun _ => ⟨fun h => by contradiction, fun h => by contradiction⟩⟩
      intro _ h; injection h with hs'; subst hs'
      refine ⟨tgt, rfl, ⟨htNotClass, ?_, ?_, ⟨optT, ?_, htgtT⟩⟩⟩
      · intro k hkC hkt
        dsimp
        have hkd : k ≠ dst := fun heq => by subst heq; rw [hdC] at hkC; contradiction
        have hks : k ≠ s := fun heq => by subst heq; rw [hadm] at hkC; contradiction
        rw [updateFn_ne _ dst k _ hkd, updateFn_ne _ s k _ hks]
        exact hframe k hkC hkt
      · intro r hrC
        dsimp
        cases hrd : Nat.beq r dst with
        | true =>
          have heq := Nat.eq_of_beq_eq_true hrd; subst heq
          rw [updateFn_self, updateFn_self]
          exact ⟨fun _ => rfl, fun hf => by contradiction⟩
        | false =>
          have hneD := (nat_beq_eq_false_iff r dst).mp hrd
          rw [updateFn_ne _ dst r _ hneD, updateFn_ne _ dst r _ hneD]
          cases hrs : Nat.beq r s with
          | true =>
            have heqS := Nat.eq_of_beq_eq_true hrs; subst heqS
            rw [updateFn_self]
            exact ⟨fun _ => rfl, fun hf => by rw [hdom] at hf; contradiction⟩
          | false =>
            have hneS := (nat_beq_eq_false_iff r s).mp hrs
            rw [updateFn_ne _ s r _ hneS]
            exact hclass r hrC
      · dsimp
        rw [updateFn_ne _ dst target _ (Ne.symm hdt), updateFn_ne _ s target _ (Ne.symm hst)]
        exact hsrcT
    | false =>
      rw [hdC] at hadm; dsimp at hadm
      have ⟨h12, hstB⟩ := Bool.and_eq_true_iff.mp hadm
      have ⟨hsNotC, hdtB⟩ := Bool.and_eq_true_iff.mp h12
      have hsC : inClass s = false := bool_not_eq_true_to_eq_false hsNotC
      have hdt : dst ≠ target := not_beq_true_to_ne hdtB
      have hst : s ≠ target := not_beq_true_to_ne hstB
      dsimp [refPropMutStmt, stepInitClass]
      rw [hdC]; dsimp
      have hseEq : tgt.locals s = src.locals s := (hframe s hsC hst).symm
      dsimp [execRefStmt, directReadLocal]
      rw [hseEq]
      cases hss : (src.locals s).slot with
      | dead => exact ⟨fun _ h => by contradiction, fun _ => Iff.rfl⟩
      | live optS =>
        cases optS with
        | none => exact ⟨fun _ h => by contradiction, fun _ => Iff.rfl⟩
        | some v =>
          let entryS : RefLocalEntry :=
            { slot := .live (some v), gen := (src.locals s).gen, activeMutBorrow := none }
          have hdeEq1 :
              updateFn tgt.locals s entryS dst =
              updateFn src.locals s entryS dst := by
            cases hds : Nat.beq dst s with
            | true =>
              have heq := Nat.eq_of_beq_eq_true hds; subst heq
              rw [updateFn_self, updateFn_self]
            | false =>
              have hne := (nat_beq_eq_false_iff dst s).mp hds
              rw [updateFn_ne _ s dst _ hne, updateFn_ne _ s dst _ hne]
              exact (hframe dst hdC hdt).symm
          dsimp [directWriteLocal]
          have hdeSlotEq :
              (updateFn tgt.locals s entryS dst).slot =
              (updateFn src.locals s entryS dst).slot :=
            congrArg RefLocalEntry.slot hdeEq1
          rw [hdeSlotEq]
          cases hdsSlot : (updateFn src.locals s entryS dst).slot with
          | dead => exact ⟨fun _ h => by contradiction, fun _ => Iff.rfl⟩
          | live _ =>
            refine ⟨?_, fun _ => ⟨fun h => by contradiction, fun h => by contradiction⟩⟩
            intro _ h; injection h with hs'; subst hs'
            refine ⟨_, rfl, ⟨htNotClass, ?_, ?_, ⟨optT, ?_, ?_⟩⟩⟩
            · intro k hkC hkt
              dsimp
              cases hkd : Nat.beq k dst with
              | true =>
                have heq := Nat.eq_of_beq_eq_true hkd; subst heq
                rw [updateFn_self, updateFn_self, hdeEq1.symm]
              | false =>
                have hneD := (nat_beq_eq_false_iff k dst).mp hkd
                rw [updateFn_ne _ dst k _ hneD, updateFn_ne _ dst k _ hneD]
                cases hks : Nat.beq k s with
                | true =>
                  have heqS := Nat.eq_of_beq_eq_true hks; subst heqS
                  rw [updateFn_self, updateFn_self]
                | false =>
                  have hneS := (nat_beq_eq_false_iff k s).mp hks
                  rw [updateFn_ne _ s k _ hneS, updateFn_ne _ s k _ hneS]
                  exact hframe k hkC hkt
            · intro r hrC
              dsimp
              have hrd : r ≠ dst := fun heq => by subst heq; rw [hdC] at hrC; contradiction
              have hrs : r ≠ s := fun heq => by subst heq; rw [hsC] at hrC; contradiction
              rw [updateFn_ne _ dst r _ hrd, updateFn_ne _ s r _ hrs]
              exact hclass r hrC
            · dsimp; rw [updateFn_ne _ dst target _ (Ne.symm hdt), updateFn_ne _ s target _ (Ne.symm hst)]
              exact hsrcT
            · dsimp; rw [updateFn_ne _ dst target _ (Ne.symm hdt), updateFn_ne _ s target _ (Ne.symm hst)]
              exact htgtT
  | borrowShared refLoc t =>
    dsimp [MutClassStmtAdmitted] at hadm
    have ⟨h123, httB⟩ := Bool.and_eq_true_iff.mp hadm
    have ⟨h12, hrtB⟩ := Bool.and_eq_true_iff.mp h123
    have ⟨hrNotC, htNotC'⟩ := Bool.and_eq_true_iff.mp h12
    have hrC : inClass refLoc = false := bool_not_eq_true_to_eq_false hrNotC
    have htC : inClass t = false := bool_not_eq_true_to_eq_false htNotC'
    have hrt : refLoc ≠ target := not_beq_true_to_ne hrtB
    have htt : t ≠ target := not_beq_true_to_ne httB
    have hteEq : tgt.locals t = src.locals t := (hframe t htC htt).symm
    dsimp [refPropMutStmt, stepInitClass, execRefStmt]
    rw [hteEq]
    cases hts : (src.locals t).slot with
    | dead => exact ⟨fun _ h => by contradiction, fun _ => Iff.rfl⟩
    | live optVal =>
      let entryT : RefLocalEntry :=
        { slot := .live optVal, gen := (src.locals t).gen, activeMutBorrow := none }
      have hreEq :
          updateFn tgt.locals t entryT refLoc =
          updateFn src.locals t entryT refLoc := by
        cases hrt2 : Nat.beq refLoc t with
        | true => have heq := Nat.eq_of_beq_eq_true hrt2; subst heq; rw [updateFn_self, updateFn_self]
        | false =>
          have hne := (nat_beq_eq_false_iff refLoc t).mp hrt2
          rw [updateFn_ne _ t refLoc _ hne, updateFn_ne _ t refLoc _ hne]
          exact (hframe refLoc hrC hrt).symm
      have hreSlotEq :
          (updateFn tgt.locals t entryT refLoc).slot =
          (updateFn src.locals t entryT refLoc).slot :=
        congrArg RefLocalEntry.slot hreEq
      dsimp [directWriteLocal]
      rw [hreSlotEq]
      cases hrs : (updateFn src.locals t entryT refLoc).slot with
      | dead => exact ⟨fun _ h => by contradiction, fun _ => Iff.rfl⟩
      | live _ =>
        refine ⟨?_, fun _ => ⟨fun h => by contradiction, fun h => by contradiction⟩⟩
        intro _ h; injection h with hs'; subst hs'
        refine ⟨_, rfl, ⟨htNotClass, ?_, ?_, ⟨optT, ?_, ?_⟩⟩⟩
        · intro k hkC hkt
          dsimp
          cases hkr : Nat.beq k refLoc with
          | true => have heq := Nat.eq_of_beq_eq_true hkr; subst heq; rw [updateFn_self, updateFn_self, hreEq.symm]
          | false =>
            have hneR := (nat_beq_eq_false_iff k refLoc).mp hkr
            rw [updateFn_ne _ refLoc k _ hneR, updateFn_ne _ refLoc k _ hneR]
            cases hkt2 : Nat.beq k t with
            | true => have heqT := Nat.eq_of_beq_eq_true hkt2; subst heqT; rw [updateFn_self, updateFn_self]
            | false =>
              have hneT := (nat_beq_eq_false_iff k t).mp hkt2
              rw [updateFn_ne _ t k _ hneT, updateFn_ne _ t k _ hneT]
              exact hframe k hkC hkt
        · intro r hrC'
          dsimp
          have hrr : r ≠ refLoc := fun heq => by subst heq; rw [hrC] at hrC'; contradiction
          have hrt3 : r ≠ t := fun heq => by subst heq; rw [htC] at hrC'; contradiction
          rw [updateFn_ne _ refLoc r _ hrr, updateFn_ne _ t r _ hrt3]
          exact hclass r hrC'
        · dsimp; rw [updateFn_ne _ refLoc target _ (Ne.symm hrt), updateFn_ne _ t target _ (Ne.symm htt)]
          exact hsrcT
        · dsimp; rw [updateFn_ne _ refLoc target _ (Ne.symm hrt), updateFn_ne _ t target _ (Ne.symm htt)]
          exact htgtT
  | borrowMut _ _ =>
    dsimp [MutClassStmtAdmitted] at hadm
    contradiction
  | assignFromDeref dst r =>
    dsimp [MutClassStmtAdmitted] at hadm
    dsimp [MutClassSsaDominated] at hdom
    have ⟨hd12, hrC⟩ := Bool.and_eq_true_iff.mp hadm
    have ⟨hdNotC, hdtB⟩ := Bool.and_eq_true_iff.mp hd12
    have hdC : inClass dst = false := bool_not_eq_true_to_eq_false hdNotC
    have hdt : dst ≠ target := not_beq_true_to_ne hdtB
    have hdeEq : tgt.locals dst = src.locals dst := (hframe dst hdC hdt).symm
    rw [hrC] at hdom; dsimp at hdom
    have hrSlot : (src.locals r).slot = .live (some (.mutRef target gen bid)) :=
      (hclass r hrC).1 hdom
    dsimp [refPropMutStmt, stepInitClass]; rw [hrC]; dsimp
    dsimp [execRefStmt, resolveRefDeref, directReadLocal]
    rw [hrSlot]; dsimp; rw [hsrcT, htgtT]; dsimp
    rw [Nat.beq_refl gen, Nat.beq_refl bid]; dsimp
    rw [hsrcT]; dsimp
    cases optT with
    | none => exact ⟨fun _ h => by contradiction, fun _ => Iff.rfl⟩
    | some v =>
      dsimp [directWriteLocal]
      have hnoop2 :
          updateFn tgt.locals target { slot := .live (some v), gen := gen, activeMutBorrow := none } =
          tgt.locals := by
        rw [htgtT] at hnoopTgtTarget; exact hnoopTgtTarget
      rw [hnoop2]
      have hdeSlotEq : (tgt.locals dst).slot = (src.locals dst).slot :=
        congrArg RefLocalEntry.slot hdeEq
      rw [hdeSlotEq]
      cases hds : (src.locals dst).slot with
      | dead => exact ⟨fun _ h => by contradiction, fun _ => Iff.rfl⟩
      | live _ =>
        refine ⟨?_, fun _ => ⟨fun h => by contradiction, fun h => by contradiction⟩⟩
        intro _ h; injection h with hs'; subst hs'
        refine ⟨_, rfl, ⟨htNotClass, ?_, ?_, ⟨some v, ?_, ?_⟩⟩⟩
        · intro k hkC hkt
          dsimp
          cases hkd : Nat.beq k dst with
          | true => have heq := Nat.eq_of_beq_eq_true hkd; subst heq; rw [updateFn_self, updateFn_self, hdeEq.symm]
          | false =>
            have hne := (nat_beq_eq_false_iff k dst).mp hkd
            rw [updateFn_ne _ dst k _ hne, updateFn_ne _ dst k _ hne]; exact hframe k hkC hkt
        · intro r' hrC'
          dsimp
          have hrd : r' ≠ dst := fun heq => by subst heq; rw [hdC] at hrC'; contradiction
          rw [updateFn_ne _ dst r' _ hrd]; exact hclass r' hrC'
        · dsimp; rw [updateFn_ne _ dst target _ (Ne.symm hdt)]; exact hsrcT
        · dsimp; rw [updateFn_ne _ dst target _ (Ne.symm hdt)]; exact htgtT
  | assignToDeref r n =>
    dsimp [MutClassStmtAdmitted] at hadm
    dsimp [MutClassSsaDominated] at hdom
    rw [hadm] at hdom; dsimp at hdom
    have hrSlot : (src.locals r).slot = .live (some (.mutRef target gen bid)) :=
      (hclass r hadm).1 hdom
    dsimp [refPropMutStmt, stepInitClass]; rw [hadm]; dsimp
    dsimp [execRefStmt, resolveRefDeref, directWriteLocal]
    rw [hrSlot]; dsimp; rw [hsrcT, htgtT]; dsimp
    rw [Nat.beq_refl gen, Nat.beq_refl bid]; dsimp
    refine ⟨?_, fun _ => ⟨fun h => by contradiction, fun h => by contradiction⟩⟩
    intro _ h; injection h with hs; subst hs
    refine ⟨_, rfl, ⟨htNotClass, ?_, ?_, ⟨some (.scalar n), ?_, ?_⟩⟩⟩
    · intro k hkC hkt
      dsimp
      rw [updateFn_ne _ target k _ hkt, updateFn_ne _ target k _ hkt]
      exact hframe k hkC hkt
    · intro r' hrC'
      dsimp
      have hrt : r' ≠ target := fun heq => by subst heq; rw [htNotClass] at hrC'; contradiction
      rw [updateFn_ne _ target r' _ hrt]; exact hclass r' hrC'
    · dsimp; rw [updateFn_self, hsrcT]
    · dsimp; rw [updateFn_self]
  | placeMentionDeref r =>
    dsimp [MutClassStmtAdmitted] at hadm
    dsimp [MutClassSsaDominated] at hdom
    rw [hadm] at hdom; dsimp at hdom
    have hrSlot : (src.locals r).slot = .live (some (.mutRef target gen bid)) :=
      (hclass r hadm).1 hdom
    dsimp [refPropMutStmt, stepInitClass]; rw [hadm]; dsimp
    dsimp [execRefStmt, resolveRefDeref]
    rw [hrSlot]; dsimp; rw [hsrcT]; dsimp
    rw [Nat.beq_refl gen, Nat.beq_refl bid]; dsimp
    exact ⟨fun _ h => by injection h with hs; subst hs; exact ⟨tgt, rfl, ⟨htNotClass, hframe, hclass, ⟨optT, hsrcT, htgtT⟩⟩⟩,
           fun _ => ⟨fun h => by contradiction, fun h => by contradiction⟩⟩

/-- Lift `refPropMutStmt` across an arbitrary statement trace. -/
noncomputable def refPropMutProg (inClass : LocalId → Bool) (target : LocalId) :
    List RefStmt → List RefStmt
  | [] => []
  | s :: rest => refPropMutStmt inClass target s :: refPropMutProg inClass target rest

/-- Check statement admissibility and SSA dominance across a statement trace. -/
noncomputable def MutProgAdmittedAndDominated (inClass initialized : LocalId → Bool)
    (target : LocalId) : List RefStmt → Bool
  | [] => true
  | s :: rest =>
    MutClassStmtAdmitted inClass target s &&
    MutClassSsaDominated inClass initialized s &&
    MutProgAdmittedAndDominated inClass (stepInitClass inClass initialized s) target rest

/-- Final initialized-member map after executing `prog`. -/
noncomputable def stepInitClassProg (inClass initialized : LocalId → Bool) :
    List RefStmt → (LocalId → Bool)
  | [] => initialized
  | s :: rest => stepInitClassProg inClass (stepInitClass inClass initialized s) rest

/-- **Main Theorem 3b (`refProp_mut_all_or_nothing_exact_bisimulation`):**
Across any statement sequence `prog` in which an entire SSA copy-equivalence
class `inClass` of `&mut target` locals (`r1 = &mut target; r2 = copy r1; ...`)
is admitted (`fully_replaceable_locals` + `ssa.meet_copy_equivalence` +
`!maybeStorageDead(target)`) and SSA-dominated, all-or-nothing `&mut`
`ReferencePropagation` (`refPropMutProg`) satisfies exact bidirectional state
bisimulation AND exact bidirectional UB identity (`execRefProg = .ub err` iff
transformed `execRefProg = .ub err`). -/
theorem refProp_mut_all_or_nothing_exact_bisimulation
    (inClass initialized : LocalId → Bool) (target : LocalId)
    (gen : GenId) (bid : BorrowId)
    (src tgt : RefMachineState) (prog : List RefStmt)
    (hrel : MutRefBisimRel inClass initialized target gen bid src tgt)
    (hprog : MutProgAdmittedAndDominated inClass initialized target prog = true) :
    (∀ src', execRefProg src prog = .ok src' →
      ∃ tgt', execRefProg tgt (refPropMutProg inClass target prog) = .ok tgt' ∧
        MutRefBisimRel inClass (stepInitClassProg inClass initialized prog) target gen bid src' tgt') ∧
    (∀ err, execRefProg src prog = .ub err ↔
      execRefProg tgt (refPropMutProg inClass target prog) = .ub err) := by
  induction prog generalizing initialized src tgt with
  | nil =>
    refine ⟨fun _ h => ?_, fun _ => ⟨fun h => by contradiction, fun h => by contradiction⟩⟩
    injection h with hs; subst hs
    exact ⟨tgt, rfl, hrel⟩
  | cons s rest ih =>
    dsimp [MutProgAdmittedAndDominated] at hprog
    have ⟨h12, hrest⟩ := Bool.and_eq_true_iff.mp hprog
    have ⟨hadm, hdom⟩ := Bool.and_eq_true_iff.mp h12
    have ⟨hsOk, hsUb⟩ :=
      refProp_mut_step_bisimulation inClass initialized target gen bid src tgt s hrel hadm hdom
    dsimp [refPropMutProg, execRefProg, stepInitClassProg]
    refine ⟨?_, ?_⟩
    · intro src' h
      cases hs : execRefStmt src s with
      | ub _ => rw [hs] at h; contradiction
      | ok src1 =>
        rw [hs] at h
        rcases hsOk src1 hs with ⟨tgt1, hsTgt, hrel1⟩
        rw [hsTgt]
        exact (ih (stepInitClass inClass initialized s) src1 tgt1 hrel1 hrest).1 src' h
    · intro err
      cases hs : execRefStmt src s with
      | ub e =>
        have hsTgt : execRefStmt tgt (refPropMutStmt inClass target s) = .ub e :=
          (hsUb e).mp hs
        rw [hsTgt]
      | ok src1 =>
        rcases hsOk src1 hs with ⟨tgt1, hsTgt, hrel1⟩
        rw [hsTgt]
        exact (ih (stepInitClass inClass initialized s) src1 tgt1 hrel1 hrest).2 err

/-! ### 3.1 Sharpness Counterexamples 2 & 3 (`MaybeStorageDead` & Partial `&mut` Aliasing) -/

def ce2InitState : RefMachineState :=
  { locals := fun l =>
      if Nat.beq l 1 then
        { slot := .live (some (.sharedRef 2 1)), gen := 1, activeMutBorrow := none }
      else if Nat.beq l 2 then
        { slot := .live (some (.scalar 10)), gen := 1, activeMutBorrow := none }
      else
        { slot := .live (some (.scalar 0)), gen := 1, activeMutBorrow := none }
  , nextBorrowId := 0 }

/-- Dead-target trace: `StorageDead(2); _3 = *_1`. -/
def ce2DeadProg : List RefStmt :=
  [.storageDead 2, .assignFromDeref 3 1]

/-- Unsound liveness-blind substitution (`ref_prop.rs:205-217` without
`MaybeStorageDead`): `StorageDead(2); _3 = copy _2`. -/
def ce2DeadProgUnsoundSubst : List RefStmt :=
  [.storageDead 2, .assignCopyLocal 3 2]

/-- Reincarnated-slot trace (`ref_prop.rs:196` without `has_single_storage`):
`StorageDead(2); StorageLive(2); _2 = 99; _3 = *_1`. -/
def ce2ReincarnatedProg : List RefStmt :=
  [.storageDead 2, .storageLive 2, .assignConst 2 99, .assignFromDeref 3 1]

/-- Unsound generation-blind substitution:
`StorageDead(2); StorageLive(2); _2 = 99; _3 = copy _2`. -/
def ce2ReincarnatedProgUnsoundSubst : List RefStmt :=
  [.storageDead 2, .storageLive 2, .assignConst 2 99, .assignCopyLocal 3 2]

/-- **Counterexample 2 (`ce2_refprop_into_storage_dead_target_dangling_ub`):**
Necessity of `MaybeStorageDead` (`ref_prop.rs:205-217`) and `has_single_storage`
(`ref_prop.rs:196`):
  1. Across `StorageDead(target)`, pre-pass `*_1` faults with
     `.ub (.danglingAfterStorageDead 2)`, whereas liveness-blind substitution
     turns the dereference into a direct `.deadLocal 2` access.
  2. Across `StorageDead(target); StorageLive(target); target = 99` (`gen: 1 -> 2`),
     pre-pass `*_1` faults with `.ub (.danglingAfterStorageDead 2)` (`gen 1 ≠ 2`),
     whereas generation-blind substitution **erases the dangling-pointer UB**
     and silently reads the reincarnated value `99` (`.ok`)! -/
theorem ce2_refprop_into_storage_dead_target_dangling_ub :
    execRefProg ce2InitState ce2DeadProg =
      .ub (.danglingAfterStorageDead 2) ∧
    execRefProg ce2InitState ce2DeadProgUnsoundSubst =
      .ub (.deadLocal 2) ∧
    execRefProg ce2InitState ce2ReincarnatedProg =
      .ub (.danglingAfterStorageDead 2) ∧
    (∃ st', execRefProg ce2InitState ce2ReincarnatedProgUnsoundSubst = .ok st' ∧
      (st'.locals 3).slot = .live (some (.scalar 99))) :=
  ⟨rfl, rfl, rfl, by refine ⟨_, rfl, ?_⟩; rfl⟩

def ce3InitState : RefMachineState :=
  { locals := fun l =>
      if Nat.beq l 0 then
        { slot := .live (some (.scalar 10)), gen := 1, activeMutBorrow := none }
      else
        { slot := .live none, gen := 1, activeMutBorrow := none }
  , nextBorrowId := 0 }

/-- Defined input program with two copy-equivalent `&mut _0` locals `_1` and `_2`:
`_1 = &mut _0; _2 = copy _1; *_1 = 42; _3 = *_2`. -/
def ce3SrcProg : List RefStmt :=
  [.borrowMut 1 0, .assignCopyLocal 2 1, .assignToDeref 1 42, .assignFromDeref 3 2]

/-- Unsound partial `&mut` `ReferencePropagation` (violating
`fully_replaceable_locals` / `ssa.meet_copy_equivalence` in `ref_prop.rs:361-375`):
rewrites `*_1 = 42` to direct `_0 = 42` while leaving `_1 = &mut _0`,
`_2 = copy _1`, and `_3 = *_2` in place! -/
def ce3PartialMutRefPropProg : List RefStmt :=
  [.borrowMut 1 0, .assignCopyLocal 2 1, .assignConst 0 42, .assignFromDeref 3 2]

/-- Sound all-or-nothing `&mut` `ReferencePropagation` across `{_1, _2}`
(deleting `_1 = &mut _0` and `_2 = copy _1`, and rewriting both `*_1` and `*_2`
to `_0`). -/
def ce3AllOrNothingMutRefPropProg : List RefStmt :=
  [.nop, .nop, .assignConst 0 42, .assignCopyLocal 3 0]

/-- **Counterexample 3 (`ce3_partial_mut_refprop_interleaving_aliasing_unsound`):**
Necessity of all-or-nothing `&mut` replacement closed under `ssa.meet_copy_equivalence`:
  1. `ce3SrcProg` executes without UB (`.ok`) and stores `42` into `_3`.
  2. Partial `&mut` replacement (`ce3PartialMutRefPropProg`) interleaves a direct
     parent write `_0 = 42` between `_1 = &mut _0; _2 = copy _1` and `_3 = *_2`,
     invalidating capability `bid = 0` and **introducing fresh Undefined Behavior**
     `.ub (.mutBorrowAliasingViolation 0 0)` into a defined program!
  3. All-or-nothing replacement (`ce3AllOrNothingMutRefPropProg`) executes
     without UB (`.ok`) and stores the identical value `42` into `_3`. -/
theorem ce3_partial_mut_refprop_interleaving_aliasing_unsound :
    (∃ stSrc, execRefProg ce3InitState ce3SrcProg = .ok stSrc ∧
      (stSrc.locals 3).slot = .live (some (.scalar 42))) ∧
    execRefProg ce3InitState ce3PartialMutRefPropProg =
      .ub (.mutBorrowAliasingViolation 0 0) ∧
    (∃ stTgt, execRefProg ce3InitState ce3AllOrNothingMutRefPropProg = .ok stTgt ∧
      (stTgt.locals 3).slot = .live (some (.scalar 42))) :=
  ⟨by refine ⟨_, rfl, ?_⟩; rfl, rfl, by refine ⟨_, rfl, ?_⟩; rfl⟩

end RemoveZstsSroaAndRefPropSoundness

