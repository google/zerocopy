/-!
# Soundness of `rustc` Static Allocations, Promoted Rvalues, ELF `PT_TLS`, and `SHF_GNU_RETAIN`

Standalone kernel-checked formalization (Lean `v4.34.1`, `0` `sorry`, `0` `Classical.choice`,
`0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec`) of:
1. Global & TLS ELF section classification (`isSuitableForBSS` vs `GV->isConstant()`,
   `.rodata`, `.data.rel.ro`, `.data`, `.bss`, `.tdata`, `.tbss`) and two-step
   `PT_GNU_RELRO` write-then-freeze operational semantics.
2. Observational equivalence of `promote_consts` (`PromoteTemps`) for pure,
   `UnsafeCell`-free, `Drop`-free rvalues (including the `&mut []` ZST carve-out),
   together with totality of CTFE on promoted expressions.
3. `PT_TLS` template instantiation (`.tdata ++ zeros(.tbss)`), cross-thread TLS
   non-interference, equivalence of all four ELF TLS access models
   (`GeneralDynamic`, `LocalDynamic`, `InitialExec`, `LocalExec`), and dynamic
   per-thread LIFO TLS destructor execution with pre-drop `State::Destroyed`
   re-entrancy protection.
4. `#[used(linker)]` (`SHF_GNU_RETAIN`) and `.init_array` survival across LLVM
   GlobalDCE and linker `--gc-sections`, plus pre-`main` constructor ordering.
5. Two concrete sharpness counterexamples:
   - `ce1_promoting_unsafecell_into_rodata_unsound`
   - `ce2_used_compiler_dropped_by_linker_gc`
-/

namespace StaticsPromotedsAndTlsSoundness

/-! ## 1. Constructive List & Arithmetic Helpers (Zero `._unsafe_rec`) -/

theorem natBeq_refl (n : Nat) : Nat.beq n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

theorem natBeq_eq {a b : Nat} (h : Nat.beq a b = true) : a = b :=
  Nat.eq_of_beq_eq_true h

theorem natBeq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hbeq : Nat.beq a b
  · rfl
  · exact False.elim (h (natBeq_eq hbeq))

def replicateZero (n : Nat) : List UInt8 :=
  Nat.repeat (fun acc => (0 : UInt8) :: acc) n []

theorem replicateZero_succ (n : Nat) :
    replicateZero (n + 1) = (0 : UInt8) :: replicateZero n := rfl

theorem replicateZero_length (n : Nat) : (replicateZero n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [replicateZero_succ, List.length_cons, ih]

theorem replicateZero_getElem (n i : Nat) (h : i < (replicateZero n).length) :
    (replicateZero n)[i] = (0 : UInt8) := by
  induction n generalizing i with
  | zero =>
    dsimp only [replicateZero, List.length_nil] at h
    exact False.elim (Nat.not_lt_zero i h)
  | succ k ih =>
    cases i with
    | zero => rfl
    | succ j =>
      simp only [replicateZero_succ, List.length_cons] at h
      exact ih j (Nat.lt_of_succ_lt_succ h)

theorem mem_append_left {α : Type} {x : α} {xs ys : List α} (h : x ∈ xs) :
    x ∈ xs ++ ys :=
  List.mem_append.mpr (.inl h)

theorem mem_append_right {α : Type} {x : α} {xs ys : List α} (h : x ∈ ys) :
    x ∈ xs ++ ys :=
  List.mem_append.mpr (.inr h)

def listContainsNat (xs : List Nat) (x : Nat) : Bool :=
  xs.foldr (fun y acc => if Nat.beq y x then true else acc) false

theorem listContainsNat_true_iff_mem (xs : List Nat) (x : Nat) :
    listContainsNat xs x = true ↔ x ∈ xs := by
  induction xs with
  | nil =>
    constructor
    · intro h; cases h
    · intro h; cases h
  | cons y ys ih =>
    constructor
    · intro h
      dsimp only [listContainsNat, List.foldr] at h
      cases hyx : Nat.beq y x
      · rw [hyx] at h
        exact List.mem_cons_of_mem y (ih.mp h)
      · have h_eq : y = x := natBeq_eq hyx
        subst h_eq
        exact List.mem_cons_self
    · intro h
      dsimp only [listContainsNat, List.foldr]
      cases h with
      | head =>
        simp only [natBeq_refl, ↓reduceIte]
      | tail _ hmem =>
        cases hyx : Nat.beq y x
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact ih.mpr hmem
        · rfl

theorem listContainsNat_false_iff_not_mem (xs : List Nat) (x : Nat) :
    listContainsNat xs x = false ↔ x ∉ xs := by
  constructor
  · intro h_false h_mem
    have h_true := (listContainsNat_true_iff_mem xs x).mpr h_mem
    rw [h_false] at h_true
    cases h_true
  · intro h_not_mem
    cases h_val : listContainsNat xs x
    · rfl
    · exact False.elim (h_not_mem ((listContainsNat_true_iff_mem xs x).mp h_val))

def listLookupNat {α : Type} (xs : List (Nat × α)) (k : Nat) : Option α :=
  xs.foldr (fun p acc => if Nat.beq p.1 k then some p.2 else acc) none

def listUpdateNat {α : Type} (xs : List (Nat × α)) (k : Nat) (v : α) : List (Nat × α) :=
  (k, v) :: xs

theorem listLookupNat_update_eq {α : Type} (xs : List (Nat × α)) (k : Nat) (v : α) :
    listLookupNat (listUpdateNat xs k v) k = some v := by
  dsimp only [listUpdateNat, listLookupNat, List.foldr]
  simp only [natBeq_refl, ↓reduceIte]

theorem listLookupNat_update_ne {α : Type} (xs : List (Nat × α)) (k target : Nat) (v : α)
    (hne : k ≠ target) :
    listLookupNat (listUpdateNat xs k v) target = listLookupNat xs target := by
  dsimp only [listUpdateNat, listLookupNat, List.foldr]
  simp only [natBeq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte]

/-! ## 2. Global Section Classification & Two-Step `PT_GNU_RELRO` Memory Model -/

inductive ElfSectionClass where
  | rodata
  | dataRelRo
  | data
  | bss
  | tdata
  | tbss
  deriving DecidableEq

/-- Models `intern_const_alloc_recursive` (`consts.rs:474`, `intern.rs:221`) composed
with LLVM `TargetLoweringObjectFile::getKindForGlobal` (`isSuitableForBSS` rejects
globals with `GV->isConstant() == true`, placing zero-initialized `Freeze` items into
`.rodata`/`.tdata` rather than `.bss`/`.tbss`). -/
def classifyGlobalSection
    (isThreadLocal : Bool)
    (isFreeze : Bool)
    (isStaticMut : Bool)
    (hasZeroInit : Bool)
    (hasRelocs : Bool)
    (isPic : Bool) : ElfSectionClass :=
  let llvmConstant := isFreeze && !isStaticMut
  if isThreadLocal then
    if hasZeroInit && !llvmConstant then .tbss else .tdata
  else
    if hasZeroInit && !llvmConstant then
      .bss
    else if llvmConstant then
      if hasRelocs && isPic then .dataRelRo else .rodata
    else
      .data

theorem zero_freeze_static_lands_in_rodata_not_bss :
    classifyGlobalSection false true false true false true = .rodata := by
  rfl

theorem zero_freeze_tls_lands_in_tdata_not_tbss :
    classifyGlobalSection true true false true false true = .tdata := by
  rfl

theorem zero_mut_tls_lands_in_tbss :
    classifyGlobalSection true false false true false true = .tbss := by
  rfl

theorem pointer_bearing_freeze_static_lands_in_data_rel_ro_under_pic :
    classifyGlobalSection false true false false true true = .dataRelRo := by
  rfl

theorem pointer_bearing_freeze_static_lands_in_rodata_under_static_reloc :
    classifyGlobalSection false true false false true false = .rodata := by
  rfl

inductive LoaderMode where
  | relocating
  | running
  deriving DecidableEq

inductive SegmentKind where
  | rodata
  | dataRelRo
  | data
  | bss
  | stack (tid : Nat)
  | tls (tid : Nat)
  deriving DecidableEq

def segmentWritable (mode : LoaderMode) : SegmentKind → Bool
  | .rodata => false
  | .dataRelRo => match mode with | .relocating => true | .running => false
  | .data => true
  | .bss => true
  | .stack _ => true
  | .tls _ => true

inductive SegFault where
  | permissionViolation (seg : SegmentKind)
  deriving DecidableEq

structure ModuleMemory where
  mode : LoaderMode
  rodataVal : Nat
  dataRelRoVal : Nat
  dataVal : Nat
  bssVal : Nat
  deriving DecidableEq

def freezeRelro (m : ModuleMemory) : ModuleMemory :=
  { m with mode := .running }

inductive MemOp where
  | writeData (v : Nat)
  | writeBss (v : Nat)
  | writeRelro (v : Nat)
  | writeRodata (v : Nat)
  deriving DecidableEq

def stepMem (m : ModuleMemory) (op : MemOp) : Except SegFault ModuleMemory :=
  match op with
  | .writeData v => .ok { m with dataVal := v }
  | .writeBss v => .ok { m with bssVal := v }
  | .writeRelro v =>
    if segmentWritable m.mode .dataRelRo then
      .ok { m with dataRelRoVal := v }
    else
      .error (.permissionViolation .dataRelRo)
  | .writeRodata v =>
    if segmentWritable m.mode .rodata then
      .ok { m with rodataVal := v }
    else
      .error (.permissionViolation .rodata)

def runMemOps (m : ModuleMemory) (ops : List MemOp) : Except SegFault ModuleMemory :=
  ops.foldl
    (fun acc op =>
      match acc with
      | .error f => .error f
      | .ok cur => stepMem cur op)
    (.ok m)

theorem relro_writable_during_reloc_and_frozen_at_runtime (m : ModuleMemory) (v : Nat) :
    stepMem { m with mode := .relocating } (.writeRelro v) =
      .ok { m with mode := .relocating, dataRelRoVal := v } ∧
    stepMem (freezeRelro m) (.writeRelro v) = .error (.permissionViolation .dataRelRo) := by
  constructor <;> rfl

theorem running_step_preserves_rodata_and_dataRelRo
    (m m' : ModuleMemory) (hmode : m.mode = .running) (op : MemOp)
    (hstep : stepMem m op = .ok m') :
    m'.mode = .running ∧ m'.rodataVal = m.rodataVal ∧ m'.dataRelRoVal = m.dataRelRoVal := by
  cases op with
  | writeData v =>
    dsimp only [stepMem] at hstep
    injection hstep with heq
    subst heq
    exact ⟨hmode, rfl, rfl⟩
  | writeBss v =>
    dsimp only [stepMem] at hstep
    injection hstep with heq
    subst heq
    exact ⟨hmode, rfl, rfl⟩
  | writeRelro v =>
    dsimp only [stepMem] at hstep
    rw [hmode] at hstep
    cases hstep
  | writeRodata v =>
    dsimp only [stepMem] at hstep
    cases hstep

theorem running_trace_preserves_rodata_and_dataRelRo
    (ops : List MemOp) (m m' : ModuleMemory) (hmode : m.mode = .running)
    (hrun : runMemOps m ops = .ok m') :
    m'.mode = .running ∧ m'.rodataVal = m.rodataVal ∧ m'.dataRelRoVal = m.dataRelRoVal := by
  induction ops generalizing m with
  | nil =>
    dsimp only [runMemOps, List.foldl] at hrun
    injection hrun with heq
    subst heq
    exact ⟨hmode, rfl, rfl⟩
  | cons op rest ih =>
    dsimp only [runMemOps, List.foldl] at hrun
    cases hstep : stepMem m op with
    | error f =>
      rw [hstep] at hrun
      have herr : ∀ (xs : List MemOp),
          xs.foldl (fun acc o => match acc with | Except.error e => Except.error e | Except.ok c => stepMem c o)
            (Except.error f) = Except.error f := by
        intro xs
        induction xs with
        | nil => rfl
        | cons _ _ ihx => exact ihx
      rw [herr rest] at hrun
      cases hrun
    | ok m1 =>
      rw [hstep] at hrun
      obtain ⟨hm1, hro1, hrel1⟩ := running_step_preserves_rodata_and_dataRelRo m m1 hmode op hstep
      obtain ⟨hm', hro', hrel'⟩ := ih m1 hm1 hrun
      exact ⟨hm', hro'.trans hro1, hrel'.trans hrel1⟩

/-! ## 3. Implicit Rvalue Promotion (`promote_consts`) Soundness -/

structure TypeQualifs where
  hasUnsafeCell : Bool
  needsDrop : Bool
  isZeroLenArray : Bool
  deriving DecidableEq

inductive BorrowMode where
  | shared
  | mutBorrow
  deriving DecidableEq

inductive PromoExpr where
  | lit (n : Nat)
  | add (a b : PromoExpr)
  | sub (a b : PromoExpr)
  | mul (a b : PromoExpr)
  | divConst (a : PromoExpr) (divisor : Nat)
  | arrayIndex (elems : List Nat) (idx : Nat)
  | mutEmptySlice

def natLtBool (a b : Nat) : Bool := Nat.blt a b

theorem natLtBool_true_iff_lt (a b : Nat) : natLtBool a b = true ↔ a < b := by
  dsimp only [natLtBool]
  rw [Nat.blt_eq]

def promoWfStep (sub : PromoExpr → Bool) (e : PromoExpr) : Bool :=
  match e with
  | .lit _ => true
  | .add a b => sub a && sub b
  | .sub a b => sub a && sub b
  | .mul a b => sub a && sub b
  | .divConst a d => sub a && !(Nat.beq d 0)
  | .arrayIndex elems idx => natLtBool idx elems.length
  | .mutEmptySlice => true

def promoExprWellFormed (fuel : Nat) (e : PromoExpr) : Bool :=
  (Nat.repeat promoWfStep fuel (fun _ => false)) e

/-- Models `Validator::validate_candidate` / `validate_ref` / `validate_rvalue`
in `compiler/rustc_mir_transform/src/promote_consts.rs`. -/
def canPromoteRef (fuel : Nat) (mode : BorrowMode) (q : TypeQualifs) (e : PromoExpr) : Bool :=
  !q.needsDrop &&
  promoExprWellFormed fuel e &&
  match mode with
  | .shared => !q.hasUnsafeCell
  | .mutBorrow => q.isZeroLenArray

inductive EvalPanic where
  | outOfFuel
  | divByZero
  | indexOutOfBounds
  deriving DecidableEq

def ctfeEvalPromoStep (eval : PromoExpr → Except EvalPanic Nat) (e : PromoExpr) :
    Except EvalPanic Nat :=
  match e with
  | .lit n => .ok n
  | .add a b =>
    match eval a, eval b with
    | .ok va, .ok vb => .ok (va + vb)
    | .error err, _ => .error err
    | _, .error err => .error err
  | .sub a b =>
    match eval a, eval b with
    | .ok va, .ok vb => .ok (va - vb)
    | .error err, _ => .error err
    | _, .error err => .error err
  | .mul a b =>
    match eval a, eval b with
    | .ok va, .ok vb => .ok (va * vb)
    | .error err, _ => .error err
    | _, .error err => .error err
  | .divConst a d =>
    if Nat.beq d 0 then
      .error .divByZero
    else
      match eval a with
      | .ok va => .ok (va / d)
      | .error err => .error err
  | .arrayIndex elems idx =>
    match elems[idx]? with
    | some v => .ok v
    | none => .error .indexOutOfBounds
  | .mutEmptySlice => .ok 0

def ctfeEvalPromo (fuel : Nat) (e : PromoExpr) : Except EvalPanic Nat :=
  (Nat.repeat ctfeEvalPromoStep fuel (fun _ => .error .outOfFuel)) e

theorem list_getElem?_some_of_lt {α : Type} (xs : List α) (i : Nat) (h : i < xs.length) :
    ∃ v, xs[i]? = some v := by
  induction xs generalizing i with
  | nil =>
    simp only [List.length_nil] at h
    exact False.elim (Nat.not_lt_zero i h)
  | cons x rest ih =>
    cases i with
    | zero => exact ⟨x, rfl⟩
    | succ j =>
      simp only [List.length_cons] at h
      exact ih j (Nat.lt_of_succ_lt_succ h)

theorem promoExprWellFormed_implies_ctfe_total (fuel : Nat) (e : PromoExpr)
    (hwf : promoExprWellFormed fuel e = true) :
    ∃ v, ctfeEvalPromo fuel e = .ok v := by
  induction fuel generalizing e with
  | zero =>
    dsimp only [promoExprWellFormed, Nat.repeat] at hwf
    cases hwf
  | succ k ih =>
    dsimp only [promoExprWellFormed] at hwf
    change promoWfStep (promoExprWellFormed k) e = true at hwf
    cases e with
    | lit n => exact ⟨n, rfl⟩
    | add a b =>
      dsimp only [promoWfStep] at hwf
      cases hwa : promoExprWellFormed k a <;> cases hwb : promoExprWellFormed k b
      · rw [hwa] at hwf; cases hwf
      · rw [hwa] at hwf; cases hwf
      · rw [hwa, hwb] at hwf; cases hwf
      · obtain ⟨va, hva⟩ := ih a hwa
        obtain ⟨vb, hvb⟩ := ih b hwb
        refine ⟨va + vb, ?_⟩
        change ctfeEvalPromoStep (ctfeEvalPromo k) (.add a b) = Except.ok (va + vb)
        dsimp only [ctfeEvalPromoStep]
        rw [hva, hvb]
    | sub a b =>
      dsimp only [promoWfStep] at hwf
      cases hwa : promoExprWellFormed k a <;> cases hwb : promoExprWellFormed k b
      · rw [hwa] at hwf; cases hwf
      · rw [hwa] at hwf; cases hwf
      · rw [hwa, hwb] at hwf; cases hwf
      · obtain ⟨va, hva⟩ := ih a hwa
        obtain ⟨vb, hvb⟩ := ih b hwb
        refine ⟨va - vb, ?_⟩
        change ctfeEvalPromoStep (ctfeEvalPromo k) (.sub a b) = Except.ok (va - vb)
        dsimp only [ctfeEvalPromoStep]
        rw [hva, hvb]
    | mul a b =>
      dsimp only [promoWfStep] at hwf
      cases hwa : promoExprWellFormed k a <;> cases hwb : promoExprWellFormed k b
      · rw [hwa] at hwf; cases hwf
      · rw [hwa] at hwf; cases hwf
      · rw [hwa, hwb] at hwf; cases hwf
      · obtain ⟨va, hva⟩ := ih a hwa
        obtain ⟨vb, hvb⟩ := ih b hwb
        refine ⟨va * vb, ?_⟩
        change ctfeEvalPromoStep (ctfeEvalPromo k) (.mul a b) = Except.ok (va * vb)
        dsimp only [ctfeEvalPromoStep]
        rw [hva, hvb]
    | divConst a d =>
      dsimp only [promoWfStep] at hwf
      cases hwa : promoExprWellFormed k a
      · rw [hwa] at hwf; cases hwf
      · rw [hwa] at hwf
        cases h0 : Nat.beq d 0
        · obtain ⟨va, hva⟩ := ih a hwa
          refine ⟨va / d, ?_⟩
          change ctfeEvalPromoStep (ctfeEvalPromo k) (.divConst a d) = Except.ok (va / d)
          dsimp only [ctfeEvalPromoStep]
          rw [h0, hva]
          rfl
        · rw [h0] at hwf
          cases hwf
    | arrayIndex elems idx =>
      dsimp only [promoWfStep] at hwf
      have hlt : idx < elems.length := (natLtBool_true_iff_lt idx elems.length).mp hwf
      obtain ⟨v, hv⟩ := list_getElem?_some_of_lt elems idx hlt
      refine ⟨v, ?_⟩
      change ctfeEvalPromoStep (ctfeEvalPromo k) (.arrayIndex elems idx) = Except.ok v
      dsimp only [ctfeEvalPromoStep]
      rw [hv]
    | mutEmptySlice => exact ⟨0, rfl⟩

theorem canPromoteRef_implies_ctfe_total (fuel : Nat) (mode : BorrowMode) (q : TypeQualifs) (e : PromoExpr)
    (h : canPromoteRef fuel mode q e = true) :
    ∃ v, ctfeEvalPromo fuel e = .ok v := by
  dsimp only [canPromoteRef] at h
  cases hdrop : q.needsDrop <;> cases hwf : promoExprWellFormed fuel e
  · rw [hdrop, hwf] at h; cases h
  · exact promoExprWellFormed_implies_ctfe_total fuel e hwf
  · rw [hdrop] at h; cases h
  · rw [hdrop] at h; cases h

inductive RefUseOp where
  | readBorrowed
  | writeZeroLenZst
  | writeInterior (delta : Nat)
  deriving DecidableEq

def validRefUseOne (mode : BorrowMode) (q : TypeQualifs) (op : RefUseOp) : Bool :=
  match op with
  | .readBorrowed => true
  | .writeZeroLenZst => q.isZeroLenArray && (mode == .mutBorrow)
  | .writeInterior _ => q.hasUnsafeCell && !q.isZeroLenArray

def validRefUses (mode : BorrowMode) (q : TypeQualifs) (ops : List RefUseOp) : Bool :=
  ops.foldr (fun op acc => validRefUseOne mode q op && acc) true

structure ExecOutcome where
  outputs : List Nat
  dropsRun : Nat
  deriving DecidableEq

def runUsesStep (isRodata isZeroLen : Bool) (op : RefUseOp)
    (ih : Nat → Except SegFault (Nat × List Nat)) (cur : Nat) :
    Except SegFault (Nat × List Nat) :=
  match op with
  | .readBorrowed =>
    match ih cur with
    | .ok (v', outs) => .ok (v', cur :: outs)
    | .error f => .error f
  | .writeZeroLenZst =>
    -- ZST zero-byte writes are sound no-ops even on read-only targets (`machine.rs:985`)
    if isZeroLen then
      match ih cur with
      | .ok (v', outs) => .ok (v', outs)
      | .error f => .error f
    else if isRodata then
      .error (.permissionViolation .rodata)
    else
      match ih cur with
      | .ok (v', outs) => .ok (v', outs)
      | .error f => .error f
  | .writeInterior delta =>
    if isZeroLen then
      match ih cur with
      | .ok (v', outs) => .ok (v', outs)
      | .error f => .error f
    else if isRodata then
      .error (.permissionViolation .rodata)
    else
      let nextVal := cur + delta
      match ih nextVal with
      | .ok (v', outs) => .ok (v', nextVal :: outs)
      | .error f => .error f

def runUsesInSlot (slotVal : Nat) (isRodata : Bool) (isZeroLen : Bool)
    (ops : List RefUseOp) : Except SegFault (Nat × List Nat) :=
  (ops.foldr (runUsesStep isRodata isZeroLen) (fun cur => .ok (cur, []))) slotVal

/-- Unpromoted execution allocates a fresh stack slot per call and runs `Drop` on scope exit
whenever `q.needsDrop = true`. -/
def evalUnpromotedCalls (fuel : Nat) (q : TypeQualifs) (e : PromoExpr) (calls : List (List RefUseOp)) :
    Except (Sum EvalPanic SegFault) ExecOutcome :=
  calls.foldr
    (fun ops ih =>
      match ctfeEvalPromo fuel e with
      | .error p => .error (.inl p)
      | .ok initVal =>
        match runUsesInSlot initVal false q.isZeroLenArray ops with
        | .error f => .error (.inr f)
        | .ok (_, outs) =>
          match ih with
          | .error err => .error err
          | .ok tail =>
            let d := if q.needsDrop then 1 else 0
            .ok ⟨outs ++ tail.outputs, d + tail.dropsRun⟩)
    (.ok ⟨[], 0⟩)

def evalPromotedCallsLoop (isZeroLen rodataBacked : Bool) (curVal : Nat)
    (cs : List (List RefUseOp)) : Except SegFault (List Nat) :=
  (cs.foldr
    (fun ops ih cur =>
      match runUsesInSlot cur rodataBacked isZeroLen ops with
      | .error f => .error f
      | .ok (nextVal, outs) =>
        match ih nextVal with
        | .error f => .error f
        | .ok tailOuts => .ok (outs ++ tailOuts))
    (fun _ => .ok [])) curVal

/-- Promoted execution evaluates `e` once into shared `.rodata` (unless forced into
a writable global slot in counterexample modeling) and skips drop glue. -/
def evalPromotedCalls (fuel : Nat) (q : TypeQualifs) (e : PromoExpr) (rodataBacked : Bool)
    (calls : List (List RefUseOp)) :
    Except (Sum EvalPanic SegFault) ExecOutcome :=
  match ctfeEvalPromo fuel e with
  | .error p => .error (.inl p)
  | .ok roVal =>
    match evalPromotedCallsLoop q.isZeroLenArray rodataBacked roVal calls with
    | .error f => .error (.inr f)
    | .ok allOuts => .ok ⟨allOuts, 0⟩

theorem validRefUses_cons (mode : BorrowMode) (q : TypeQualifs) (op : RefUseOp) (rest : List RefUseOp) :
    validRefUses mode q (op :: rest) = (validRefUseOne mode q op && validRefUses mode q rest) := rfl

theorem runUsesInSlot_cons_read (v : Nat) (isRo isZst : Bool) (rest : List RefUseOp) :
    runUsesInSlot v isRo isZst (.readBorrowed :: rest) =
      match runUsesInSlot v isRo isZst rest with
      | Except.ok (v', outs) => Except.ok (v', v :: outs)
      | Except.error f => Except.error f := rfl

theorem runUsesInSlot_cons_writeZst_true (v : Nat) (isRo : Bool) (rest : List RefUseOp) :
    runUsesInSlot v isRo true (.writeZeroLenZst :: rest) =
      match runUsesInSlot v isRo true rest with
      | Except.ok (v', outs) => Except.ok (v', outs)
      | Except.error f => Except.error f := rfl

theorem runUsesInSlot_pure_matches
    (v : Nat) (mode : BorrowMode) (q : TypeQualifs) (ops : List RefUseOp)
    (h_no_cell : (q.hasUnsafeCell && !q.isZeroLenArray) = false)
    (h_valid : validRefUses mode q ops = true) :
    runUsesInSlot v true q.isZeroLenArray ops = runUsesInSlot v false q.isZeroLenArray ops ∧
    ∃ outs, runUsesInSlot v false q.isZeroLenArray ops = .ok (v, outs) := by
  induction ops with
  | nil =>
    exact ⟨rfl, [], rfl⟩
  | cons op rest ih =>
    rw [validRefUses_cons] at h_valid
    cases op with
    | readBorrowed =>
      dsimp only [validRefUseOne, Bool.true_and] at h_valid
      obtain ⟨h_eq, outs, h_ok⟩ := ih h_valid
      constructor
      · rw [runUsesInSlot_cons_read, runUsesInSlot_cons_read, h_eq, h_ok]
      · rw [runUsesInSlot_cons_read, h_ok]
        exact ⟨v :: outs, rfl⟩
    | writeZeroLenZst =>
      dsimp only [validRefUseOne] at h_valid
      cases h_zst : q.isZeroLenArray
      · rw [h_zst] at h_valid; cases h_valid
      · rw [h_zst] at h_valid
        have h_rest : validRefUses mode q rest = true := by
          cases hm : (mode == .mutBorrow)
          · rw [hm] at h_valid; cases h_valid
          · rw [hm] at h_valid; exact h_valid
        obtain ⟨h_eq, outs, h_ok⟩ := ih h_rest
        rw [h_zst] at h_eq h_ok
        constructor
        · rw [runUsesInSlot_cons_writeZst_true, runUsesInSlot_cons_writeZst_true, h_eq, h_ok]
        · rw [runUsesInSlot_cons_writeZst_true, h_ok]
          exact ⟨outs, rfl⟩
    | writeInterior delta =>
      dsimp only [validRefUseOne] at h_valid
      rw [h_no_cell] at h_valid
      cases h_valid

theorem runUsesInSlot_shared_rodata_matches
    (v : Nat) (q : TypeQualifs) (ops : List RefUseOp)
    (h_no_cell : q.hasUnsafeCell = false)
    (h_valid : validRefUses .shared q ops = true) :
    runUsesInSlot v true q.isZeroLenArray ops = runUsesInSlot v false q.isZeroLenArray ops ∧
    ∃ outs, runUsesInSlot v false q.isZeroLenArray ops = .ok (v, outs) := by
  apply runUsesInSlot_pure_matches v .shared q ops
  · rw [h_no_cell]; rfl
  · exact h_valid

theorem runUsesInSlot_mut_zst_matches
    (v : Nat) (q : TypeQualifs) (ops : List RefUseOp)
    (h_zst : q.isZeroLenArray = true)
    (h_valid : validRefUses .mutBorrow q ops = true) :
    runUsesInSlot v true q.isZeroLenArray ops = runUsesInSlot v false q.isZeroLenArray ops ∧
    ∃ outs, runUsesInSlot v false q.isZeroLenArray ops = .ok (v, outs) := by
  apply runUsesInSlot_pure_matches v .mutBorrow q ops
  · rw [h_zst]
    exact Bool.and_false _
  · exact h_valid

theorem promote_rvalue_observational_equivalence
    (fuel : Nat) (mode : BorrowMode) (q : TypeQualifs) (e : PromoExpr) (calls : List (List RefUseOp))
    (h_promo : canPromoteRef fuel mode q e = true)
    (h_valid_calls : ∀ ops, ops ∈ calls → validRefUses mode q ops = true) :
    evalPromotedCalls fuel q e true calls = evalUnpromotedCalls fuel q e calls ∧
    ∃ outs, evalPromotedCalls fuel q e true calls = .ok ⟨outs, 0⟩ := by
  have h_promo_copy := h_promo
  dsimp only [canPromoteRef] at h_promo
  cases h_drop : q.needsDrop
  · rw [h_drop] at h_promo
    obtain ⟨v, hv⟩ := canPromoteRef_implies_ctfe_total fuel mode q e h_promo_copy
    have h_mode_spec :
        ∀ ops, validRefUses mode q ops = true →
          runUsesInSlot v true q.isZeroLenArray ops = runUsesInSlot v false q.isZeroLenArray ops ∧
          ∃ outs, runUsesInSlot v false q.isZeroLenArray ops = .ok (v, outs) := by
      cases mode with
      | shared =>
        intro ops hops
        have h_cell : q.hasUnsafeCell = false := by
          cases hwf : promoExprWellFormed fuel e
          · rw [hwf] at h_promo; cases h_promo
          · rw [hwf] at h_promo
            cases hc : q.hasUnsafeCell
            · rfl
            · rw [hc] at h_promo; cases h_promo
        exact runUsesInSlot_shared_rodata_matches v q ops h_cell hops
      | mutBorrow =>
        intro ops hops
        have h_zst : q.isZeroLenArray = true := by
          cases hwf : promoExprWellFormed fuel e
          · rw [hwf] at h_promo; cases h_promo
          · rw [hwf] at h_promo
            exact h_promo
        exact runUsesInSlot_mut_zst_matches v q ops h_zst hops
    have h_loop : ∀ cs : List (List RefUseOp),
        (∀ ops, ops ∈ cs → validRefUses mode q ops = true) →
        evalPromotedCalls fuel q e true cs = evalUnpromotedCalls fuel q e cs ∧
        ∃ outs, evalPromotedCalls fuel q e true cs = .ok ⟨outs, 0⟩ := by
      intro cs hcs
      induction cs with
      | nil =>
        dsimp only [evalPromotedCalls, evalPromotedCallsLoop, evalUnpromotedCalls, List.foldr]
        rw [hv]
        exact ⟨rfl, [], rfl⟩
      | cons ops rest ih =>
        have hops_valid : validRefUses mode q ops = true := hcs ops List.mem_cons_self
        have hrest_valid : ∀ o, o ∈ rest → validRefUses mode q o = true :=
          fun o ho => hcs o (List.mem_cons_of_mem ops ho)
        obtain ⟨ih_eq, restOuts, ih_ok⟩ := ih hrest_valid
        obtain ⟨h_slot_eq, outs, h_slot_ok⟩ := h_mode_spec ops hops_valid
        have h_slot_true : runUsesInSlot v true q.isZeroLenArray ops = .ok (v, outs) :=
          h_slot_eq.trans h_slot_ok
        have h_loop_rest : evalPromotedCallsLoop q.isZeroLenArray true v rest = .ok restOuts := by
          dsimp only [evalPromotedCalls] at ih_ok
          rw [hv] at ih_ok
          dsimp only at ih_ok
          cases h_lr : evalPromotedCallsLoop q.isZeroLenArray true v rest with
          | error f =>
            rw [h_lr] at ih_ok
            cases ih_ok
          | ok ts =>
            rw [h_lr] at ih_ok
            dsimp only at ih_ok
            injection ih_ok with h_pair
            injection h_pair with h_ts
            rw [h_ts]
        have h_unp_rest : evalUnpromotedCalls fuel q e rest = .ok ⟨restOuts, 0⟩ :=
          ih_eq.symm.trans ih_ok
        constructor
        · dsimp only [evalPromotedCalls, evalPromotedCallsLoop, List.foldr]
          rw [hv]
          dsimp only
          rw [h_slot_true]
          dsimp only
          change (match (match evalPromotedCallsLoop q.isZeroLenArray true v rest with
            | Except.error f => Except.error f
            | Except.ok tailOuts => Except.ok (outs ++ tailOuts)) with
            | Except.error f => Except.error (Sum.inr f)
            | Except.ok allOuts => Except.ok (ExecOutcome.mk allOuts 0)) =
            (match ctfeEvalPromo fuel e with
            | Except.error p => Except.error (Sum.inl p)
            | Except.ok initVal =>
              match runUsesInSlot initVal false q.isZeroLenArray ops with
              | Except.error f => Except.error (Sum.inr f)
              | Except.ok (_, outs) =>
                match evalUnpromotedCalls fuel q e rest with
                | Except.error err => Except.error err
                | Except.ok tail =>
                  let d := if q.needsDrop then 1 else 0
                  Except.ok (ExecOutcome.mk (outs ++ tail.outputs) (d + tail.dropsRun)))
          rw [h_loop_rest, hv]
          dsimp only
          rw [h_slot_ok]
          dsimp only
          rw [h_unp_rest]
          dsimp only
          rw [h_drop]
          rfl
        · dsimp only [evalPromotedCalls, evalPromotedCallsLoop, List.foldr]
          rw [hv]
          dsimp only
          rw [h_slot_true]
          dsimp only
          refine ⟨outs ++ restOuts, ?_⟩
          change (match (match evalPromotedCallsLoop q.isZeroLenArray true v rest with
            | Except.error f => Except.error f
            | Except.ok tailOuts => Except.ok (outs ++ tailOuts)) with
            | Except.error f => Except.error (Sum.inr f)
            | Except.ok allOuts => Except.ok (ExecOutcome.mk allOuts 0)) =
            Except.ok (ExecOutcome.mk (outs ++ restOuts) 0)
          rw [h_loop_rest]
    exact h_loop calls h_valid_calls
  · rw [h_drop] at h_promo
    cases h_promo

/-! ## 4. ELF `PT_TLS` Template, Cross-Thread Non-Interference, 4 TLS Models, and LIFO Destructors -/

structure PtTlsTemplate where
  tdataBytes : List UInt8
  tbssZeroLen : Nat
  deriving DecidableEq

def PtTlsTemplate.pFilesz (tmpl : PtTlsTemplate) : Nat := tmpl.tdataBytes.length
def PtTlsTemplate.pMemsz (tmpl : PtTlsTemplate) : Nat := tmpl.tdataBytes.length + tmpl.tbssZeroLen

def instantiatePtTls (tmpl : PtTlsTemplate) : List UInt8 :=
  tmpl.tdataBytes ++ replicateZero tmpl.tbssZeroLen

theorem pt_tls_instantiate_length (tmpl : PtTlsTemplate) :
    (instantiatePtTls tmpl).length = tmpl.pMemsz := by
  dsimp only [instantiatePtTls, PtTlsTemplate.pMemsz]
  rw [List.length_append, replicateZero_length]

theorem pt_tls_tdata_prefix_exact (tmpl : PtTlsTemplate) (i : Nat)
    (hi : i < tmpl.pFilesz) :
    (instantiatePtTls tmpl)[i]'(by
      rw [pt_tls_instantiate_length]
      exact Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _)) = tmpl.tdataBytes[i]'hi := by
  dsimp only [instantiatePtTls]
  exact List.getElem_append_left hi

theorem append_replicateZero_getElem (xs : List UInt8) (n j : Nat) (hj : j < n) :
    (xs ++ replicateZero n)[xs.length + j]'(by
      rw [List.length_append, replicateZero_length]
      exact Nat.add_lt_add_left hj _) = (0 : UInt8) := by
  have hle : xs.length ≤ xs.length + j := Nat.le_add_right _ _
  rw [List.getElem_append_right hle]
  have hsub : xs.length + j - xs.length = j := Nat.add_sub_cancel_left _ _
  simp only [hsub]
  exact replicateZero_getElem n j (by rw [replicateZero_length]; exact hj)

theorem pt_tls_tbss_zero_exact (tmpl : PtTlsTemplate) (j : Nat) (hj : j < tmpl.tbssZeroLen) :
    (instantiatePtTls tmpl)[tmpl.pFilesz + j]'(by
      rw [pt_tls_instantiate_length, PtTlsTemplate.pMemsz, PtTlsTemplate.pFilesz]
      exact Nat.add_lt_add_left hj _) = (0 : UInt8) := by
  exact append_replicateZero_getElem tmpl.tdataBytes tmpl.tbssZeroLen j hj

inductive TlsAccessModel where
  | generalDynamic
  | localDynamic
  | initialExec
  | localExec
  deriving DecidableEq

structure TlsModuleLayout where
  tpBase : Nat → Nat
  moduleDtvAddr : Nat → Nat → Nat
  gotTpOff : Nat → Nat
  dtpOff : Nat → Nat
  tpOff : Nat → Nat

/-- For executable-local ELF TLS symbols (or after linker `GD->LE`/`LD->LE`/`IE->LE`
relaxation), `DTV[m] + dtpoff(s) == tp(tid) - tpoff(s)` and `got[s] == tpoff(s)`. -/
structure ValidTlsLayout (lay : TlsModuleLayout) (modId : Nat) : Prop where
  dtv_coherent : ∀ tid symOffset,
    lay.moduleDtvAddr tid modId + lay.dtpOff symOffset = lay.tpBase tid - lay.tpOff symOffset
  got_coherent : ∀ symOffset,
    lay.gotTpOff symOffset = lay.tpOff symOffset

def resolveTlsAddr (lay : TlsModuleLayout) (tid modId symOffset : Nat) :
    TlsAccessModel → Nat
  | .generalDynamic => lay.moduleDtvAddr tid modId + lay.dtpOff symOffset
  | .localDynamic   => lay.moduleDtvAddr tid modId + lay.dtpOff symOffset
  | .initialExec    => lay.tpBase tid - lay.gotTpOff symOffset
  | .localExec      => lay.tpBase tid - lay.tpOff symOffset

theorem elf_tls_four_models_address_equivalent
    (lay : TlsModuleLayout) (modId tid symOffset : Nat)
    (hvalid : ValidTlsLayout lay modId) :
    resolveTlsAddr lay tid modId symOffset .generalDynamic =
      lay.tpBase tid - lay.tpOff symOffset ∧
    resolveTlsAddr lay tid modId symOffset .localDynamic =
      lay.tpBase tid - lay.tpOff symOffset ∧
    resolveTlsAddr lay tid modId symOffset .initialExec =
      lay.tpBase tid - lay.tpOff symOffset ∧
    resolveTlsAddr lay tid modId symOffset .localExec =
      lay.tpBase tid - lay.tpOff symOffset := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · exact hvalid.dtv_coherent tid symOffset
  · exact hvalid.dtv_coherent tid symOffset
  · dsimp only [resolveTlsAddr]
    rw [hvalid.got_coherent symOffset]

/-! ### 4a. Multi-Thread `PT_TLS` State & Cross-Thread Non-Interference -/

inductive DtorSlotState where
  | uninitialized
  | alive (val : Nat)
  | destroyed
  deriving DecidableEq

structure ThreadTlsBlock where
  rawBytes : List UInt8
  slots : List (Nat × DtorSlotState)
  dtorList : List Nat
  deriving DecidableEq

def initThreadTlsBlock (tmpl : PtTlsTemplate) : ThreadTlsBlock :=
  { rawBytes := instantiatePtTls tmpl, slots := [], dtorList := [] }

structure MultiThreadTlsState where
  template : PtTlsTemplate
  threads : List (Nat × ThreadTlsBlock)
  deriving DecidableEq

def projectThreadTls (s : MultiThreadTlsState) (tid : Nat) : Option ThreadTlsBlock :=
  listLookupNat s.threads tid

inductive TlsOp where
  | spawn (tid : Nat)
  | writeByte (tid : Nat) (off : Nat) (b : UInt8)
  | lazyInitSlot (tid : Nat) (keyId : Nat) (val : Nat) (hasDrop : Bool)
  | runExitDtors (tid : Nat)
  deriving DecidableEq

def tlsOpTargetTid : TlsOp → Nat
  | .spawn tid => tid
  | .writeByte tid _ _ => tid
  | .lazyInitSlot tid _ _ _ => tid
  | .runExitDtors tid => tid

def drainDtorList (slots : List (Nat × DtorSlotState)) (dtors : List Nat) :
    (List (Nat × DtorSlotState) × List Nat) :=
  (dtors.foldr
    (fun k ih sl =>
      -- State transitions to `.destroyed` BEFORE destructor body runs (`eager.rs:70`, `lazy.rs:116`)
      let sl' := listUpdateNat sl k .destroyed
      let res := ih sl'
      (res.1, k :: res.2))
    (fun sl => (sl, []))) slots

def stepTlsOp (s : MultiThreadTlsState) (op : TlsOp) : MultiThreadTlsState :=
  match op with
  | .spawn tid =>
    { s with threads := listUpdateNat s.threads tid (initThreadTlsBlock s.template) }
  | .writeByte tid off b =>
    match listLookupNat s.threads tid with
    | none => s
    | some blk =>
      let blk' := { blk with rawBytes := blk.rawBytes.set off b }
      { s with threads := listUpdateNat s.threads tid blk' }
  | .lazyInitSlot tid keyId val hasDrop =>
    match listLookupNat s.threads tid with
    | none => s
    | some blk =>
      match listLookupNat blk.slots keyId with
      | some (.alive _) => s
      | some .destroyed => s
      | _ =>
        let slots' := listUpdateNat blk.slots keyId (.alive val)
        let dtors' := if hasDrop then keyId :: blk.dtorList else blk.dtorList
        { s with threads := listUpdateNat s.threads tid { blk with slots := slots', dtorList := dtors' } }
  | .runExitDtors tid =>
    match listLookupNat s.threads tid with
    | none => s
    | some blk =>
      let (slots', _) := drainDtorList blk.slots blk.dtorList
      { s with threads := listUpdateNat s.threads tid { blk with slots := slots', dtorList := [] } }

def runTlsTrace (s : MultiThreadTlsState) (ops : List TlsOp) : MultiThreadTlsState :=
  ops.foldl stepTlsOp s

theorem pt_tls_spawn_fresh_template_sound (s : MultiThreadTlsState) (tid : Nat) :
    projectThreadTls (stepTlsOp s (.spawn tid)) tid = some (initThreadTlsBlock s.template) ∧
    (∀ other, other ≠ tid →
      projectThreadTls (stepTlsOp s (.spawn tid)) other = projectThreadTls s other) := by
  constructor
  · dsimp only [stepTlsOp, projectThreadTls]
    exact listLookupNat_update_eq s.threads tid (initThreadTlsBlock s.template)
  · intro other hne
    dsimp only [stepTlsOp, projectThreadTls]
    exact listLookupNat_update_ne s.threads tid other (initThreadTlsBlock s.template) hne.symm

theorem stepTlsOp_noninterference (s : MultiThreadTlsState) (op : TlsOp) (targetTid : Nat)
    (hne : tlsOpTargetTid op ≠ targetTid) :
    projectThreadTls (stepTlsOp s op) targetTid = projectThreadTls s targetTid := by
  cases op with
  | spawn tid =>
    dsimp only [tlsOpTargetTid] at hne
    dsimp only [stepTlsOp, projectThreadTls]
    exact listLookupNat_update_ne s.threads tid targetTid (initThreadTlsBlock s.template) hne
  | writeByte tid off b =>
    dsimp only [tlsOpTargetTid] at hne
    dsimp only [stepTlsOp, projectThreadTls]
    cases h : listLookupNat s.threads tid with
    | none => rfl
    | some blk =>
      dsimp only
      exact listLookupNat_update_ne s.threads tid targetTid _ hne
  | lazyInitSlot tid keyId val hasDrop =>
    dsimp only [tlsOpTargetTid] at hne
    dsimp only [stepTlsOp, projectThreadTls]
    cases h : listLookupNat s.threads tid with
    | none => rfl
    | some blk =>
      dsimp only
      cases hslot : listLookupNat blk.slots keyId with
      | none =>
        dsimp only
        exact listLookupNat_update_ne s.threads tid targetTid _ hne
      | some st =>
        cases st with
        | uninitialized =>
          dsimp only
          exact listLookupNat_update_ne s.threads tid targetTid _ hne
        | alive _ => rfl
        | destroyed => rfl
  | runExitDtors tid =>
    dsimp only [tlsOpTargetTid] at hne
    dsimp only [stepTlsOp, projectThreadTls]
    cases h : listLookupNat s.threads tid with
    | none => rfl
    | some blk =>
      dsimp only
      exact listLookupNat_update_ne s.threads tid targetTid _ hne

theorem pt_tls_cross_thread_noninterference
    (s : MultiThreadTlsState) (ops : List TlsOp) (targetTid : Nat)
    (h_disjoint : ∀ op, op ∈ ops → tlsOpTargetTid op ≠ targetTid) :
    projectThreadTls (runTlsTrace s ops) targetTid = projectThreadTls s targetTid := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih =>
    have h_op : tlsOpTargetTid op ≠ targetTid := h_disjoint op List.mem_cons_self
    have h_rest : ∀ o, o ∈ rest → tlsOpTargetTid o ≠ targetTid :=
      fun o ho => h_disjoint o (List.mem_cons_of_mem op ho)
    change projectThreadTls (runTlsTrace (stepTlsOp s op) rest) targetTid = projectThreadTls s targetTid
    rw [ih (stepTlsOp s op) h_rest]
    exact stepTlsOp_noninterference s op targetTid h_op

/-! ### 4b. Dynamic Per-Thread LIFO Destructors & Pre-Drop `Destroyed` Re-Entrancy Safety -/

def accessSlot (slots : List (Nat × DtorSlotState)) (keyId : Nat) : Option Nat :=
  match listLookupNat slots keyId with
  | some (.alive v) => some v
  | _ => none

def drainDtorsStepwise (slots : List (Nat × DtorSlotState)) (dtors : List Nat) :
    (List (Nat × DtorSlotState) × List (Nat × Option Nat)) :=
  (dtors.foldr
    (fun k ih sl =>
      -- Write `.destroyed` BEFORE running destructor body; re-entrant `accessSlot k` sees `none`.
      let slotsMarked := listUpdateNat sl k .destroyed
      let reentrantRead := accessSlot slotsMarked k
      let res := ih slotsMarked
      (res.1, (k, reentrantRead) :: res.2))
    (fun sl => (sl, []))) slots

theorem drainDtorList_order_eq_stack (slots : List (Nat × DtorSlotState)) (dtors : List Nat) :
    (drainDtorList slots dtors).2 = dtors := by
  induction dtors generalizing slots with
  | nil => rfl
  | cons k rest ih =>
    dsimp only [drainDtorList, List.foldr]
    exact congrArg (k :: ·) (ih (listUpdateNat slots k .destroyed))

theorem drainDtorsStepwise_reentrant_none (slots : List (Nat × DtorSlotState)) (dtors : List Nat) :
    ∀ k r, (k, r) ∈ (drainDtorsStepwise slots dtors).2 → r = none := by
  induction dtors generalizing slots with
  | nil =>
    intro k r h
    cases h
  | cons d rest ih =>
    intro k r h
    dsimp only [drainDtorsStepwise, List.foldr] at h
    have h_re : accessSlot (listUpdateNat slots d .destroyed) d = none := by
      dsimp only [accessSlot]
      rw [listLookupNat_update_eq]
    cases h with
    | head => exact h_re
    | tail _ hmem =>
      exact ih (listUpdateNat slots d .destroyed) k r hmem

def recordTlsInitOrder (initOrder : List Nat) (keyId : Nat) (hasDrop : Bool) : List Nat :=
  if hasDrop then initOrder ++ [keyId] else initOrder

def pushTlsDtorStack (dtorStack : List Nat) (keyId : Nat) (hasDrop : Bool) : List Nat :=
  if hasDrop then keyId :: dtorStack else dtorStack

theorem tls_dtor_lifo_order_and_reentrant_access_safety
    (initEvents : List (Nat × Bool)) (slots : List (Nat × DtorSlotState)) :
    let initOrder := initEvents.foldl (fun acc p => recordTlsInitOrder acc p.1 p.2) []
    let dtorStack := initEvents.foldl (fun acc p => pushTlsDtorStack acc p.1 p.2) []
    (drainDtorList slots dtorStack).2 = initOrder.reverse ∧
    (∀ k r, (k, r) ∈ (drainDtorsStepwise slots dtorStack).2 → r = none) := by
  have h_rev :
      ∀ (evs : List (Nat × Bool)) (accFwd accRev : List Nat),
        accRev = accFwd.reverse →
        (evs.foldl (fun acc p => pushTlsDtorStack acc p.1 p.2) accRev) =
          (evs.foldl (fun acc p => recordTlsInitOrder acc p.1 p.2) accFwd).reverse := by
    intro evs
    induction evs with
    | nil =>
      intro accFwd accRev h
      exact h
    | cons ev rest ih =>
      intro accFwd accRev h
      rcases ev with ⟨kid, hasDrop⟩
      dsimp only [List.foldl]
      apply ih
      cases hasDrop
      · exact h
      · dsimp only [pushTlsDtorStack, recordTlsInitOrder]
        simp only [↓reduceIte, List.reverse_append, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.singleton_append]
        rw [h]
  constructor
  · rw [drainDtorList_order_eq_stack]
    exact h_rev initEvents [] [] rfl
  · exact drainDtorsStepwise_reentrant_none slots _

/-! ## 5. `#[used(linker)]` (`SHF_GNU_RETAIN`) & `.init_array` Survival Under `--gc-sections` -/

inductive UsedAttr where
  | none
  | usedCompiler
  | usedLinker
  deriving DecidableEq

structure ElfSection where
  secId : Nat
  usedAttr : UsedAttr
  isInitArray : Bool
  relocTargets : List Nat
  deriving DecidableEq

def ElfSection.inLlvmUsed (s : ElfSection) : Bool :=
  s.usedAttr == .usedLinker

def ElfSection.inLlvmCompilerUsed (s : ElfSection) : Bool :=
  s.usedAttr == .usedCompiler

def ElfSection.shfGnuRetain (s : ElfSection) : Bool :=
  s.usedAttr == .usedLinker

def ElfSection.isGcRoot (s : ElfSection) (entrySec : Nat) : Bool :=
  Nat.beq s.secId entrySec || s.shfGnuRetain || s.isInitArray

def survivesLlvmGlobalDce (referencedInTu : List Nat) (s : ElfSection) : Bool :=
  listContainsNat referencedInTu s.secId || s.inLlvmUsed || s.inLlvmCompilerUsed

def llvmGlobalDce (referencedInTu : List Nat) (secs : List ElfSection) : List ElfSection :=
  secs.filter (survivesLlvmGlobalDce referencedInTu)

def lookupSection (secs : List ElfSection) (sid : Nat) : Option ElfSection :=
  secs.foldr (fun s acc => if Nat.beq s.secId sid then some s else acc) none

def collectTargets (secs : List ElfSection) (liveIds : List Nat) : List Nat :=
  liveIds.foldr
    (fun sid acc =>
      match lookupSection secs sid with
      | none => acc
      | some sec => sec.relocTargets ++ acc)
    []

def gcRootIds (entrySec : Nat) (secs : List ElfSection) : List Nat :=
  (secs.filter (fun s => s.isGcRoot entrySec)).map ElfSection.secId

def gcLiveStep (secs : List ElfSection) (liveIds : List Nat) : List Nat :=
  liveIds ++ collectTargets secs liveIds

def gcLiveSections (entrySec : Nat) (secs : List ElfSection) (fuel : Nat) : List Nat :=
  Nat.repeat (gcLiveStep secs) fuel (gcRootIds entrySec secs)

theorem mem_filter_map_id {s : ElfSection} {secs : List ElfSection} {p : ElfSection → Bool}
    (hs : s ∈ secs) (hp : p s = true) :
    s.secId ∈ (secs.filter p).map ElfSection.secId := by
  induction secs with
  | nil => cases hs
  | cons x rest ih =>
    cases hs with
    | head =>
      dsimp only [List.filter]
      rw [hp]
      exact List.mem_cons_self
    | tail _ hmem =>
      dsimp only [List.filter]
      cases hpx : p x
      · exact ih hmem
      · exact List.mem_cons_of_mem x.secId (ih hmem)

theorem gcLiveSections_monotone_base (entrySec : Nat) (secs : List ElfSection) (fuel : Nat)
    {sid : Nat} (h0 : sid ∈ gcLiveSections entrySec secs 0) :
    sid ∈ gcLiveSections entrySec secs fuel := by
  induction fuel with
  | zero => exact h0
  | succ k ih =>
    change sid ∈ gcLiveStep secs (gcLiveSections entrySec secs k)
    dsimp only [gcLiveStep]
    exact mem_append_left ih

theorem gcLiveSections_step_preserves (entrySec : Nat) (secs : List ElfSection) (fuel : Nat)
    {sid : Nat} (h : sid ∈ gcLiveSections entrySec secs fuel) :
    sid ∈ gcLiveSections entrySec secs (fuel + 1) := by
  change sid ∈ gcLiveStep secs (gcLiveSections entrySec secs fuel)
  dsimp only [gcLiveStep]
  exact mem_append_left h

theorem used_linker_shf_gnu_retain_survives_gc_sections
    (entrySec : Nat) (referencedInTu : List Nat) (secs : List ElfSection)
    (s : ElfSection) (hs : s ∈ secs) (h_used : s.usedAttr = .usedLinker) (fuel : Nat) :
    s ∈ llvmGlobalDce referencedInTu secs ∧
    s.shfGnuRetain = true ∧
    s.secId ∈ gcLiveSections entrySec (llvmGlobalDce referencedInTu secs) fuel := by
  have h_surv : survivesLlvmGlobalDce referencedInTu s = true := by
    dsimp only [survivesLlvmGlobalDce, ElfSection.inLlvmUsed]
    rw [h_used]
    simp only [beq_self_eq_true, Bool.or_true, Bool.true_or]
  have h_in_dce : s ∈ llvmGlobalDce referencedInTu secs :=
    List.mem_filter.mpr ⟨hs, h_surv⟩
  have h_retain : s.shfGnuRetain = true := by
    dsimp only [ElfSection.shfGnuRetain]
    rw [h_used]
    rfl
  have h_root : s.isGcRoot entrySec = true := by
    dsimp only [ElfSection.isGcRoot]
    rw [h_retain]
    simp only [Bool.or_true, Bool.true_or]
  have h_in_0 : s.secId ∈ gcLiveSections entrySec (llvmGlobalDce referencedInTu secs) 0 := by
    dsimp only [gcLiveSections, Nat.repeat, gcRootIds]
    exact mem_filter_map_id h_in_dce h_root
  exact ⟨h_in_dce, h_retain, gcLiveSections_monotone_base entrySec (llvmGlobalDce referencedInTu secs) fuel h_in_0⟩

theorem init_array_section_survives_gc_sections
    (entrySec : Nat) (referencedInTu : List Nat) (secs : List ElfSection)
    (s : ElfSection) (hs : s ∈ secs) (_h_init : s.isInitArray = true)
    (h_used : s.usedAttr = .usedLinker) (fuel : Nat) :
    s ∈ llvmGlobalDce referencedInTu secs ∧
    s.secId ∈ gcLiveSections entrySec (llvmGlobalDce referencedInTu secs) fuel := by
  obtain ⟨hdce, _, hgc⟩ :=
    used_linker_shf_gnu_retain_survives_gc_sections entrySec referencedInTu secs s hs h_used fuel
  exact ⟨hdce, hgc⟩

inductive StartupEvent where
  | ctor (secId : Nat)
  | mainEntry
  deriving DecidableEq

def runInitArrayThenMain (retainedInitArrays : List Nat) : List StartupEvent :=
  retainedInitArrays.map StartupEvent.ctor ++ [.mainEntry]

theorem init_array_runs_before_main (retainedInitArrays : List Nat) (cid : Nat)
    (hcid : cid ∈ retainedInitArrays) :
    ∃ prefixEvs suffixEvs,
      runInitArrayThenMain retainedInitArrays =
        prefixEvs ++ [StartupEvent.ctor cid] ++ suffixEvs ∧
      StartupEvent.mainEntry ∈ suffixEvs := by
  induction retainedInitArrays with
  | nil => cases hcid
  | cons x rest ih =>
    cases hcid with
    | head =>
      refine ⟨[], rest.map StartupEvent.ctor ++ [.mainEntry], ?_, ?_⟩
      · dsimp only [runInitArrayThenMain, List.map_cons]
        rfl
      · exact mem_append_right List.mem_cons_self
    | tail _ hmem =>
      obtain ⟨p, sf, heq, hmain⟩ := ih hmem
      refine ⟨StartupEvent.ctor x :: p, sf, ?_, hmain⟩
      dsimp only [runInitArrayThenMain]
      dsimp only [runInitArrayThenMain] at heq
      rw [List.map_cons, List.cons_append, heq]
      simp only [List.cons_append, List.append_assoc]

/-! ## 6. Concrete Sharpness Counterexamples -/

/-- **Counterexample 1 (`ce1_promoting_unsafecell_into_rodata_unsound`)**:
Promoting a concrete `UnsafeCell<u32>` rvalue (`&Cell::new(0)`) into shared memory is
unsound under both implementations:
1. `promote_consts` (`HasMutInterior`) correctly rejects `&Cell::new(0)`.
2. Forcing promotion into `.rodata` (`rodataBacked = true`) causes the runtime write
   (`writeInterior 1`) to fault with `SegFault.permissionViolation .rodata`, whereas
   unpromoted stack execution succeeds and returns `[1, 1]` across two calls.
3. Forcing promotion into writable shared global memory (`rodataBacked = false`) mutates
   the shared slot across calls, returning `[1, 2] ≠ [1, 1]`. -/
theorem ce1_promoting_unsafecell_into_rodata_unsound :
    let cellQualifs : TypeQualifs := ⟨true, false, false⟩
    let cellExpr : PromoExpr := .lit 0
    let twoCalls : List (List RefUseOp) := [[.writeInterior 1], [.writeInterior 1]]
    canPromoteRef 4 .shared cellQualifs cellExpr = false ∧
    evalUnpromotedCalls 4 cellQualifs cellExpr twoCalls = .ok ⟨[1, 1], 0⟩ ∧
    evalPromotedCalls 4 cellQualifs cellExpr true twoCalls =
      .error (.inr (.permissionViolation .rodata)) ∧
    evalPromotedCalls 4 cellQualifs cellExpr false twoCalls = .ok ⟨[1, 2], 0⟩ := by
  refine ⟨rfl, rfl, rfl, rfl⟩

private def ce2MainSec : ElfSection := ⟨1, .none, false, []⟩
private def ce2RegCompiler : ElfSection := ⟨2, .usedCompiler, false, []⟩
private def ce2RegLinker : ElfSection := ⟨2, .usedLinker, false, []⟩

/-- **Counterexample 2 (`ce2_used_compiler_dropped_by_linker_gc`)**:
Given an unreferenced registration static `ce2Reg*` (secId = 2) alongside `ce2MainSec` (secId = 1):
- With `#[used(compiler)]` (`llvm.compiler.used`), `ce2RegCompiler` survives LLVM GlobalDCE
  yet has `shfGnuRetain = false` and is **discarded** by `--gc-sections`
  (`2 ∉ gcLiveSections 1 ... 3`).
- With `#[used(linker)]` (`llvm.used` + `SHF_GNU_RETAIN`), the exact same unreferenced
  section survives both LLVM GlobalDCE and `--gc-sections` (`2 ∈ gcLiveSections 1 ... 3`). -/
theorem ce2_used_compiler_dropped_by_linker_gc :
    ce2RegCompiler ∈ llvmGlobalDce [1] [ce2MainSec, ce2RegCompiler] ∧
    ce2RegCompiler.shfGnuRetain = false ∧
    2 ∉ gcLiveSections 1 (llvmGlobalDce [1] [ce2MainSec, ce2RegCompiler]) 3 ∧
    ce2RegLinker ∈ llvmGlobalDce [1] [ce2MainSec, ce2RegLinker] ∧
    ce2RegLinker.shfGnuRetain = true ∧
    2 ∈ gcLiveSections 1 (llvmGlobalDce [1] [ce2MainSec, ce2RegLinker]) 3 := by
  refine ⟨?_, rfl, ?_, ?_, rfl, ?_⟩
  · exact List.mem_cons_of_mem ce2MainSec List.mem_cons_self
  · intro hmem
    have hfalse :
        listContainsNat (gcLiveSections 1 (llvmGlobalDce [1] [ce2MainSec, ce2RegCompiler]) 3) 2 = false := by
      rfl
    exact absurd hmem ((listContainsNat_false_iff_not_mem _ 2).mp hfalse)
  · exact List.mem_cons_of_mem ce2MainSec List.mem_cons_self
  · have htrue :
        listContainsNat (gcLiveSections 1 (llvmGlobalDce [1] [ce2MainSec, ce2RegLinker]) 3) 2 = true := by
      rfl
    exact (listContainsNat_true_iff_mem _ 2).mp htrue

end StaticsPromotedsAndTlsSoundness
