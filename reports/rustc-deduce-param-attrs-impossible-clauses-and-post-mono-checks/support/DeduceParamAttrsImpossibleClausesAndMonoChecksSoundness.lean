/-
  DeduceParamAttrsImpossibleClausesAndMonoChecksSoundness.lean

  A self-contained Lean 4 development (core library only; `import Lean` is used
  solely by the audit command at the end of the file) about three mechanisms of
  `rustc`, read at `rust-lang/rust` commit
  `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`:

    1. `deduce_param_attrs`  (`compiler/rustc_mir_transform/src/deduce_param_attrs.rs`,
       `compiler/rustc_middle/src/middle/deduced_param_attrs.rs`)
    2. `ImpossibleClauses`   (`compiler/rustc_mir_transform/src/impossible_clauses.rs`)
    3. `abi_check`           (`compiler/rustc_monomorphize/src/mono_checks/abi_check.rs`)

  WHAT IS AND IS NOT PROVED.  Everything below is about *models written in this
  file*.  The decision procedures (`classify`, `readOnly`, `capturesNone`,
  `trim`, `hasImpossibleClauses`, `checkCallSite`, ...) are hand transcriptions
  of the cited Rust functions.  The operational semantics (`applyUse`, `run`,
  `transfer256`, ...) are authored here to express the reasons given in rustc's
  own comments; they are not extracted from rustc, LLVM, or any MIR semantics.
  The theorems therefore establish that the transcribed rules are sound and
  sharp *with respect to these models*; they are not a proof about the Rust
  compiler binary.  The file imports nothing from any other project.

  Style constraints honoured here and re-checked mechanically by the final
  `#eval`: no admitted goal, no use of the classical choice axiom, no proof by
  compiled evaluation, no SAT- or arithmetic-decision-procedure tactics, no
  partial or unsafe declarations, no well-founded recursion, no opaque
  constants, no added axioms, and no unsafe recursion companions.  (The
  forbidden identifiers are deliberately not spelled out anywhere in this file,
  so that a plain-text search of the source for them finds nothing; the audit
  command assembles the names from fragments and checks the environment.)

  On `noncomputable`: with this toolchain the code generator emits an unsafe
  companion constant, named by appending an `_unsafe` + `_rec` suffix, for
  *every* compiled recursive definition, including plain structural recursion.  Every recursive function here, and
  every definition that uses one, is therefore marked `noncomputable`: it is
  defined for the kernel only and never compiled.  Kernel evaluation (`rfl`,
  `decide`) is unaffected.  For the same reason no `match` below uses a
  catch-all arm on an inductive type: such arms elaborate through an auxiliary
  that depends on `propext`.
-/
import Lean

set_option autoImplicit false

namespace DeduceParamAttrs

/-! ## 0. Small Boolean facts (proved by exhaustive evaluation, no axioms) -/

theorem and_true_left {x y : Bool} : (x && y) = true → x = true := by
  cases x <;> cases y <;> decide

theorem and_true_right {x y : Bool} : (x && y) = true → y = true := by
  cases x <;> cases y <;> decide

theorem and_false_of_left_true {x y : Bool} : (x && y) = false → x = true → y = false := by
  cases x <;> cases y <;> decide

theorem or_true_cases {x y : Bool} : (x || y) = true → x = true ∨ y = true := by
  cases x <;> cases y <;> decide

theorem not_and_not_true {x y : Bool} : (!x && !y) = true → x = false ∧ y = false := by
  cases x <;> cases y <;> decide

/-- `if c then a else b = b` when `c` is false (stated here to avoid depending on
library lemma names that change between toolchain releases). -/
theorem ite_of_neg {α : Type} {c : Prop} [inst : Decidable c] (hn : ¬ c) (a b : α) :
    (if c then a else b) = b := by
  cases inst with
  | isTrue hc => exact absurd hc hn
  | isFalse _ => rfl

theorem ite_of_pos {α : Type} {c : Prop} [inst : Decidable c] (hc : c) (a b : α) :
    (if c then a else b) = a := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hn => exact absurd hc hn

theorem eq_nil_of_isEmpty {α : Type} : ∀ {l : List α}, l.isEmpty = true → l = []
  | [], _ => rfl
  | _ :: _, h => by
    have h' : false = true := h
    cases h'

/-! ## 1. `UsageSummary`: a four-flag join-semilattice

`rustc_middle::middle::deduced_param_attrs::UsageSummary` is a `u8` `bitflags`
value with `DROP = 1 << 0`, `SHARED_BORROW = 1 << 1`, `MUTATE = 1 << 2`,
`CAPTURE = 1 << 3`.  The visitor only ever combines summaries with `|=`. -/

structure Usage where
  drop : Bool
  sharedBorrow : Bool
  mutate : Bool
  capture : Bool
deriving DecidableEq

namespace Usage

def empty : Usage := ⟨false, false, false, false⟩
def dropOnly : Usage := ⟨true, false, false, false⟩
def sharedBorrowCapture : Usage := ⟨false, true, false, true⟩
def mutateOnly : Usage := ⟨false, false, true, false⟩
def mutateCapture : Usage := ⟨false, false, true, true⟩

/-- `a | b` on the flag sets. -/
def join (a b : Usage) : Usage :=
  ⟨a.drop || b.drop, a.sharedBorrow || b.sharedBorrow, a.mutate || b.mutate,
    a.capture || b.capture⟩

/-- The `u8` value of the flag set. -/
def bits (u : Usage) : Nat :=
  (if u.drop then 1 else 0) + (if u.sharedBorrow then 2 else 0)
    + (if u.mutate then 4 else 0) + (if u.capture then 8 else 0)

def ofBits (n : Nat) : Usage := ⟨n.testBit 0, n.testBit 1, n.testBit 2, n.testBit 3⟩

/-- `DeducedParamAttrs::is_default`: `usage.contains(MUTATE | CAPTURE)`. -/
def isDefault (u : Usage) : Bool := u.mutate && u.capture

theorem ext' : ∀ {a b : Usage}, a.drop = b.drop → a.sharedBorrow = b.sharedBorrow →
    a.mutate = b.mutate → a.capture = b.capture → a = b
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl, rfl, rfl, rfl => rfl

/-- The record view and the `u8` view are in bijection on `0..16`. -/
theorem ofBits_bits (u : Usage) : ofBits u.bits = u := by
  obtain ⟨d, s, m, c⟩ := u
  cases d <;> cases s <;> cases m <;> cases c <;> rfl

theorem bits_lt_sixteen (u : Usage) : u.bits < 16 := by
  obtain ⟨d, s, m, c⟩ := u
  cases d <;> cases s <;> cases m <;> cases c <;> decide

/-- `join` is exactly bitwise OR on the `u8` encoding used by rustc. -/
theorem bits_join (a b : Usage) : (a.join b).bits = a.bits ||| b.bits := by
  obtain ⟨d, s, m, c⟩ := a
  obtain ⟨d', s', m', c'⟩ := b
  cases d <;> cases s <;> cases m <;> cases c <;>
    cases d' <;> cases s' <;> cases m' <;> cases c' <;> rfl

theorem join_comm (a b : Usage) : a.join b = b.join a :=
  ext' (Bool.or_comm _ _) (Bool.or_comm _ _) (Bool.or_comm _ _) (Bool.or_comm _ _)

theorem join_assoc (a b c : Usage) : (a.join b).join c = a.join (b.join c) :=
  ext' (Bool.or_assoc _ _ _) (Bool.or_assoc _ _ _) (Bool.or_assoc _ _ _) (Bool.or_assoc _ _ _)

theorem join_idem (a : Usage) : a.join a = a :=
  ext' (Bool.or_self _) (Bool.or_self _) (Bool.or_self _) (Bool.or_self _)

theorem empty_join (a : Usage) : empty.join a = a :=
  ext' (Bool.false_or _) (Bool.false_or _) (Bool.false_or _) (Bool.false_or _)

theorem join_empty (a : Usage) : a.join empty = a := by
  rw [join_comm, empty_join]

/-- The semilattice order induced by `join`. -/
def le (a b : Usage) : Prop := a.join b = b

theorem le_refl (a : Usage) : le a a := join_idem a

theorem le_trans {a b c : Usage} (h₁ : le a b) (h₂ : le b c) : le a c := by
  unfold le at *
  calc a.join c = a.join (b.join c) := by rw [h₂]
    _ = (a.join b).join c := (join_assoc a b c).symm
    _ = b.join c := by rw [h₁]
    _ = c := h₂

theorem le_antisymm {a b : Usage} (h₁ : le a b) (h₂ : le b a) : a = b := by
  unfold le at *
  calc a = b.join a := h₂.symm
    _ = a.join b := join_comm b a
    _ = b := h₁

theorem empty_le (a : Usage) : le empty a := empty_join a

theorem le_join_left (a b : Usage) : le a (a.join b) := by
  unfold le
  rw [← join_assoc, join_idem]

theorem le_join_right (a b : Usage) : le b (a.join b) := by
  unfold le
  rw [join_comm a b, ← join_assoc, join_idem]

/-- `join` is the least upper bound. -/
theorem join_least {a b c : Usage} (h₁ : le a c) (h₂ : le b c) : le (a.join b) c := by
  unfold le at *
  rw [join_assoc, h₂, h₁]

end Usage

/-! ## 2. From a summary to attributes, per monomorphic type

`DeducedParamAttrs::read_only` and `::captures_none` take the *instantiated*
parameter type and consult `needs_drop` and `is_freeze`. -/

/-- The two type-level facts the deduction consults after monomorphization. -/
structure TyFacts where
  needsDrop : Bool
  isFreeze : Bool
deriving DecidableEq

/-- `DeducedParamAttrs::read_only`. -/
def readOnly (u : Usage) (t : TyFacts) : Bool :=
  !u.mutate && !(u.drop && t.needsDrop) && !(u.sharedBorrow && !t.isFreeze)

/-- `DeducedParamAttrs::captures_none`. -/
def capturesNone (u : Usage) (t : TyFacts) : Bool :=
  !u.capture && !(u.drop && t.needsDrop)

/-- `read_only` turns joins into conjunctions: one offending use anywhere kills it. -/
theorem readOnly_join (a b : Usage) (t : TyFacts) :
    readOnly (a.join b) t = (readOnly a t && readOnly b t) := by
  obtain ⟨d, s, m, c⟩ := a
  obtain ⟨d', s', m', c'⟩ := b
  obtain ⟨n, f⟩ := t
  cases d <;> cases s <;> cases m <;> cases d' <;> cases s' <;> cases m' <;>
    cases n <;> cases f <;> rfl

theorem capturesNone_join (a b : Usage) (t : TyFacts) :
    capturesNone (a.join b) t = (capturesNone a t && capturesNone b t) := by
  obtain ⟨d, s, m, c⟩ := a
  obtain ⟨d', s', m', c'⟩ := b
  obtain ⟨n, f⟩ := t
  cases d <;> cases c <;> cases d' <;> cases c' <;> cases n <;> rfl

theorem readOnly_mutateCapture (t : TyFacts) : readOnly Usage.mutateCapture t = false := rfl
theorem capturesNone_mutateCapture (t : TyFacts) : capturesNone Usage.mutateCapture t = false := rfl
theorem readOnly_mutateOnly (t : TyFacts) : readOnly Usage.mutateOnly t = false := rfl

/-- The attribute pair attached to one indirectly passed parameter. -/
structure Attrs where
  readonly : Bool
  capturesNone : Bool
deriving DecidableEq

/-- No deduced attribute: what an absent table entry means. -/
def Attrs.noAttrs : Attrs := ⟨false, false⟩

def attrsOf (u : Usage) (t : TyFacts) : Attrs := ⟨readOnly u t, capturesNone u t⟩

theorem noAttrs_not_readonly : ¬ (Attrs.noAttrs.readonly = true) := by decide
theorem noAttrs_not_capturesNone : ¬ (Attrs.noAttrs.capturesNone = true) := by decide

/-- An entry for which `is_default` holds never contributes an attribute. -/
theorem attrsOf_default {u : Usage} (h : u.isDefault = true) (t : TyFacts) :
    attrsOf u t = Attrs.noAttrs := by
  obtain ⟨d, s, m, c⟩ := u
  obtain ⟨n, f⟩ := t
  revert h
  cases d <;> cases s <;> cases m <;> cases c <;> cases n <;> cases f <;> decide

/-! ## 3. Metadata compression: popping trailing default entries

`deduced_param_attrs` ends with
`while let Some((last, rest)) = attrs.split_last() && last.is_default() { attrs = rest }`
and the consumer `apply_deduced_attributes` does `deduced.get(idx)` and adds
nothing on `None`. -/

/-- Remove the maximal suffix of default entries. -/
noncomputable def trim : List Usage → List Usage
  | [] => []
  | u :: us => if ((trim us).isEmpty && u.isDefault) = true then [] else u :: trim us

theorem trim_cons_of_true {u : Usage} {us : List Usage}
    (h : ((trim us).isEmpty && u.isDefault) = true) : trim (u :: us) = [] := by
  show (if ((trim us).isEmpty && u.isDefault) = true then [] else u :: trim us) = []
  rw [h]
  rfl

theorem trim_cons_of_false {u : Usage} {us : List Usage}
    (h : ((trim us).isEmpty && u.isDefault) = false) : trim (u :: us) = u :: trim us := by
  show (if ((trim us).isEmpty && u.isDefault) = true then [] else u :: trim us) = u :: trim us
  rw [h]
  rfl

/-- `slice.get(idx)`. -/
noncomputable def lookup : List Usage → Nat → Option Usage
  | [], _ => none
  | u :: _, 0 => some u
  | _ :: us, i + 1 => lookup us i

/-- What `apply_deduced_attributes` adds for table index `i` at type `t`. -/
noncomputable def lookupAttrs (tbl : List Usage) (i : Nat) (t : TyFacts) : Attrs :=
  match lookup tbl i with
  | some u => attrsOf u t
  | none => Attrs.noAttrs

theorem lookupAttrs_nil (i : Nat) (t : TyFacts) : lookupAttrs [] i t = Attrs.noAttrs := by
  cases i <;> rfl

/-- **Compression is unobservable.**  Looking up any index in the trimmed
table yields the same attributes as looking it up in the full table, for every
monomorphic type. -/
theorem rmeta_trim_lookup_eq (tbl : List Usage) (t : TyFacts) :
    ∀ i, lookupAttrs (trim tbl) i t = lookupAttrs tbl i t := by
  induction tbl with
  | nil => intro i; rfl
  | cons u us ih =>
    intro i
    cases hb : ((trim us).isEmpty && u.isDefault) with
    | false =>
      rw [trim_cons_of_false hb]
      cases i with
      | zero => rfl
      | succ j => exact ih j
    | true =>
      rw [trim_cons_of_true hb]
      have hnil : trim us = [] := eq_nil_of_isEmpty (and_true_left hb)
      have hdef : u.isDefault = true := and_true_right hb
      cases i with
      | zero =>
        show Attrs.noAttrs = attrsOf u t
        exact (attrsOf_default hdef t).symm
      | succ j =>
        have h := ih j
        rw [hnil, lookupAttrs_nil] at h
        rw [lookupAttrs_nil]
        exact h

theorem trim_idem (xs : List Usage) : trim (trim xs) = trim xs := by
  induction xs with
  | nil => rfl
  | cons u us ih =>
    cases hb : ((trim us).isEmpty && u.isDefault) with
    | true => rw [trim_cons_of_true hb]; rfl
    | false =>
      rw [trim_cons_of_false hb]
      have hb' : ((trim (trim us)).isEmpty && u.isDefault) = false := by rw [ih]; exact hb
      rw [trim_cons_of_false hb', ih]

/-- Decoder side: extend a table to arity `n` with the canonical default entry. -/
noncomputable def padTo : Nat → List Usage → List Usage
  | 0, xs => xs
  | n + 1, [] => Usage.mutateCapture :: padTo n []
  | n + 1, x :: xs => x :: padTo n xs

/-- A table is canonical when every default-class entry is literally `MUTATE | CAPTURE`. -/
noncomputable def Canonical : List Usage → Prop
  | [] => True
  | u :: us => (u.isDefault = true → u = Usage.mutateCapture) ∧ Canonical us

/-- Encoding after decoding is the identity on encodings: padding with defaults
is erased again by `trim`. -/
theorem trim_padTo (n : Nat) : ∀ ys : List Usage, trim (padTo n ys) = trim ys := by
  induction n with
  | zero => intro ys; rfl
  | succ n ih =>
    intro ys
    cases ys with
    | nil =>
      show (if ((trim (padTo n [])).isEmpty && Usage.mutateCapture.isDefault) = true then []
            else Usage.mutateCapture :: trim (padTo n [])) = []
      rw [ih []]
      rfl
    | cons y ys =>
      show (if ((trim (padTo n ys)).isEmpty && y.isDefault) = true then []
            else y :: trim (padTo n ys))
          = (if ((trim ys).isEmpty && y.isDefault) = true then [] else y :: trim ys)
      rw [ih ys]

/-- Decoding after encoding is the identity on canonical tables of known arity.
Together with `trim_padTo` and `trim_idem` this is the compression bijection
between canonical arity-`n` tables and trimmed tables of length at most `n`. -/
theorem padTo_trim_of_canonical : ∀ xs : List Usage, Canonical xs →
    padTo xs.length (trim xs) = xs := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons u us ih =>
    intro h
    obtain ⟨hu, hus⟩ := h
    cases hb : ((trim us).isEmpty && u.isDefault) with
    | false =>
      rw [trim_cons_of_false hb]
      show u :: padTo us.length (trim us) = u :: us
      rw [ih hus]
    | true =>
      rw [trim_cons_of_true hb]
      have hnil : trim us = [] := eq_nil_of_isEmpty (and_true_left hb)
      have h₁ := ih hus
      rw [hnil] at h₁
      show Usage.mutateCapture :: padTo us.length [] = u :: us
      rw [h₁, hu (and_true_right hb)]

/-! ## 4. An operational model of one indirectly passed parameter

A by-value parameter passed as `PassMode::Indirect` lives in a memory slot whose
address the caller supplies.  `Use` enumerates the ways optimized MIR can touch
that parameter local (the cases of `DeduceParamAttrs::visit_place` and
`visit_terminator`).  Constructors that can write or leak carry an adversarial
payload: the value written, whether the write happens, and whether the address
is retained beyond the call.  Quantifying over all payloads quantifies over all
callee behaviours the corresponding MIR construct permits. -/

inductive Use where
  /-- `PlaceContext::NonUse` (storage markers and the like). -/
  | nonUse
  /-- `Inspect`, `Copy`, `Move` outside call arguments, `FakeBorrow`,
      `PlaceMention`, non-mutating `Projection`. -/
  | read
  /-- A place whose first projection is `Deref`: the access goes through the
      value stored in the slot, not to the slot. -/
  | derefAccess
  /-- `Store`, `SetDiscriminant`, `AsmOutput`, mutating `Projection`. -/
  | store (v : Nat)
  /-- `Drop` of the whole local (empty projection). -/
  | dropWhole (v : Nat) (doWrite doEscape : Bool)
  /-- `Drop` of a projection of the local. -/
  | dropProjected (v : Nat) (doWrite doEscape : Bool)
  /-- `&mut x`, `&raw mut x`, call destination, `Yield` resume place. -/
  | mutBorrow (v : Nat) (doWrite doEscape : Bool)
  /-- `&raw const x`. -/
  | rawConstBorrow (v : Nat) (doWrite doEscape : Bool)
  /-- `&x`. -/
  | sharedBorrow (v : Nat) (doWrite doEscape : Bool)
  /-- `f(move x)`: the callee receives the very same pointer. -/
  | callMove (v : Nat) (doWrite doEscape : Bool)

/-- Transcription of the visitor's contribution for one use. -/
def classify : Use → Usage
  | .nonUse => Usage.empty
  | .read => Usage.empty
  | .derefAccess => Usage.empty
  | .store _ => Usage.mutateOnly
  | .dropWhole _ _ _ => Usage.dropOnly
  | .dropProjected _ _ _ => Usage.mutateCapture
  | .mutBorrow _ _ _ => Usage.mutateCapture
  | .rawConstBorrow _ _ _ => Usage.mutateCapture
  | .sharedBorrow _ _ _ => Usage.sharedBorrowCapture
  | .callMove _ _ _ => Usage.mutateCapture

namespace Use

/-- Does this use write the parameter's slot, at monomorphic type facts `t`?
Drop glue exists only if the type needs drop; a shared borrow can be written
through only if the type is not `Freeze`. -/
def writes (t : TyFacts) : Use → Bool
  | .nonUse => false
  | .read => false
  | .derefAccess => false
  | .store _ => true
  | .dropWhole _ w _ => w && t.needsDrop
  | .dropProjected _ w _ => w
  | .mutBorrow _ w _ => w
  | .rawConstBorrow _ w _ => w
  | .sharedBorrow _ w _ => w && !t.isFreeze
  | .callMove _ w _ => w

def payload : Use → Nat
  | .nonUse => 0
  | .read => 0
  | .derefAccess => 0
  | .store v => v
  | .dropWhole v _ _ => v
  | .dropProjected v _ _ => v
  | .mutBorrow v _ _ => v
  | .rawConstBorrow v _ _ => v
  | .sharedBorrow v _ _ => v
  | .callMove v _ _ => v

/-- Does this use let the slot's address outlive the call? -/
def escapes (t : TyFacts) : Use → Bool
  | .nonUse => false
  | .read => false
  | .derefAccess => false
  | .store _ => false
  | .dropWhole _ _ e => e && t.needsDrop
  | .dropProjected _ _ e => e
  | .mutBorrow _ _ e => e
  | .rawConstBorrow _ _ e => e
  | .sharedBorrow _ _ e => e
  | .callMove _ _ e => e

end Use

/-- Per-use soundness of `read_only`: the two can never both be true. -/
theorem classify_readOnly_excludes_write (u : Use) (t : TyFacts) :
    (readOnly (classify u) t && u.writes t) = false := by
  obtain ⟨n, f⟩ := t
  cases u with
  | nonUse => cases n <;> cases f <;> rfl
  | read => cases n <;> cases f <;> rfl
  | derefAccess => cases n <;> cases f <;> rfl
  | store v => rfl
  | dropWhole v w e => cases n <;> cases w <;> rfl
  | dropProjected v w e => rfl
  | mutBorrow v w e => rfl
  | rawConstBorrow v w e => rfl
  | sharedBorrow v w e => cases f <;> cases w <;> rfl
  | callMove v w e => rfl

/-- Per-use soundness of `captures_none`. -/
theorem classify_capturesNone_excludes_escape (u : Use) (t : TyFacts) :
    (capturesNone (classify u) t && u.escapes t) = false := by
  obtain ⟨n, f⟩ := t
  cases u with
  | nonUse => cases n <;> rfl
  | read => cases n <;> rfl
  | derefAccess => cases n <;> rfl
  | store v => cases n <;> rfl
  | dropWhole v w e => cases n <;> cases e <;> rfl
  | dropProjected v w e => rfl
  | mutBorrow v w e => rfl
  | rawConstBorrow v w e => rfl
  | sharedBorrow v w e => rfl
  | callMove v w e => rfl

/-- Memory contents and the set of addresses retained beyond the current call. -/
structure State where
  mem : Nat → Nat
  escaped : Nat → Bool

/-- Execute one use of a parameter whose slot is at address `a`. -/
def applyUse (a : Nat) (t : TyFacts) (u : Use) (σ : State) : State :=
  { mem := if u.writes t = true then (fun x => if x = a then u.payload else σ.mem x) else σ.mem
    escaped := if u.escapes t = true then (fun x => if x = a then true else σ.escaped x)
               else σ.escaped }

theorem applyUse_mem_of_not_writes {a : Nat} {t : TyFacts} {u : Use} (σ : State)
    (h : u.writes t = false) : (applyUse a t u σ).mem = σ.mem := by
  show (if u.writes t = true then (fun x => if x = a then u.payload else σ.mem x) else σ.mem)
      = σ.mem
  rw [h]
  rfl

theorem applyUse_escaped_of_not_escapes {a : Nat} {t : TyFacts} {u : Use} (σ : State)
    (h : u.escapes t = false) : (applyUse a t u σ).escaped = σ.escaped := by
  show (if u.escapes t = true then (fun x => if x = a then true else σ.escaped x)
        else σ.escaped) = σ.escaped
  rw [h]
  rfl

/-- A use of one parameter never touches memory outside that parameter's slot. -/
theorem applyUse_mem_frame {a x : Nat} (t : TyFacts) (u : Use) (σ : State) (hx : x ≠ a) :
    (applyUse a t u σ).mem x = σ.mem x := by
  show (if u.writes t = true then (fun y => if y = a then u.payload else σ.mem y) else σ.mem) x
      = σ.mem x
  cases u.writes t with
  | false => rfl
  | true =>
    show (if x = a then u.payload else σ.mem x) = σ.mem x
    exact ite_of_neg hx _ _

theorem applyUse_escaped_frame {a x : Nat} (t : TyFacts) (u : Use) (σ : State) (hx : x ≠ a) :
    (applyUse a t u σ).escaped x = σ.escaped x := by
  show (if u.escapes t = true then (fun y => if y = a then true else σ.escaped y)
        else σ.escaped) x = σ.escaped x
  cases u.escapes t with
  | false => rfl
  | true =>
    show (if x = a then true else σ.escaped x) = σ.escaped x
    exact ite_of_neg hx _ _

/-- Run a single-parameter callee: a sequence of uses of the parameter at address `a`. -/
noncomputable def run1 (a : Nat) (t : TyFacts) : List Use → State → State
  | [], σ => σ
  | u :: us, σ => run1 a t us (applyUse a t u σ)

/-- Flow-insensitive summary under an arbitrary per-use classification. -/
noncomputable def summaryWith (cls : Use → Usage) : List Use → Usage
  | [] => Usage.empty
  | u :: us => (cls u).join (summaryWith cls us)

/-- The summary rustc computes for an argument (arguments start from `empty`). -/
noncomputable def summary1 (us : List Use) : Usage := summaryWith classify us

theorem run1_mem_frame (a x : Nat) (t : TyFacts) (hx : x ≠ a) :
    ∀ (us : List Use) (σ : State), (run1 a t us σ).mem x = σ.mem x
  | [], _ => rfl
  | u :: us, σ => by
    show (run1 a t us (applyUse a t u σ)).mem x = σ.mem x
    rw [run1_mem_frame a x t hx us (applyUse a t u σ), applyUse_mem_frame t u σ hx]

theorem run1_escaped_frame (a x : Nat) (t : TyFacts) (hx : x ≠ a) :
    ∀ (us : List Use) (σ : State), (run1 a t us σ).escaped x = σ.escaped x
  | [], _ => rfl
  | u :: us, σ => by
    show (run1 a t us (applyUse a t u σ)).escaped x = σ.escaped x
    rw [run1_escaped_frame a x t hx us (applyUse a t u σ), applyUse_escaped_frame t u σ hx]

/-- If `read_only` is deduced, no execution of the callee changes the slot. -/
theorem run1_readOnly_preserves (a : Nat) (t : TyFacts) :
    ∀ (us : List Use) (σ : State), readOnly (summary1 us) t = true →
      (run1 a t us σ).mem a = σ.mem a
  | [], _, _ => rfl
  | u :: us, σ, h => by
    have hj : (readOnly (classify u) t && readOnly (summary1 us) t) = true := by
      rw [← readOnly_join]
      exact h
    have hw : u.writes t = false :=
      and_false_of_left_true (classify_readOnly_excludes_write u t) (and_true_left hj)
    show (run1 a t us (applyUse a t u σ)).mem a = σ.mem a
    rw [run1_readOnly_preserves a t us (applyUse a t u σ) (and_true_right hj),
      applyUse_mem_of_not_writes σ hw]

/-- If `captures_none` is deduced, the slot's address is not retained. -/
theorem run1_capturesNone_no_escape (a : Nat) (t : TyFacts) :
    ∀ (us : List Use) (σ : State), capturesNone (summary1 us) t = true →
      (run1 a t us σ).escaped a = σ.escaped a
  | [], _, _ => rfl
  | u :: us, σ, h => by
    have hj : (capturesNone (classify u) t && capturesNone (summary1 us) t) = true := by
      rw [← capturesNone_join]
      exact h
    have he : u.escapes t = false :=
      and_false_of_left_true (classify_capturesNone_excludes_escape u t) (and_true_left hj)
    show (run1 a t us (applyUse a t u σ)).escaped a = σ.escaped a
    rw [run1_capturesNone_no_escape a t us (applyUse a t u σ) (and_true_right hj),
      applyUse_escaped_of_not_escapes σ he]

/-! ## 5. Whole bodies: several parameters, the return place, tail calls

Table index `0` is the return place and is seeded with `MUTATE`; arguments are
indices `1, 2, …` and start empty.  A guaranteed tail call lets the backend
overwrite *any* indirect argument slot of the caller, so the visitor marks
every entry `MUTATE | CAPTURE`. -/

inductive Stmt where
  | use (p : Nat) (u : Use)
  /-- `become f(..)`: the backend stores a new argument value into slot `p`. -/
  | tailCall (p : Nat) (v : Nat)

def stmtUsage : Stmt → Nat → Usage
  | .use p u, q => if p = q then classify u else Usage.empty
  | .tailCall _ _, _ => Usage.mutateCapture

/-- `DeduceParamAttrs::new`: `usage[RETURN_PLACE] |= MUTATE`. -/
def initUsage (q : Nat) : Usage := if q = 0 then Usage.mutateOnly else Usage.empty

noncomputable def summary : List Stmt → Nat → Usage
  | [], _ => Usage.empty
  | s :: ss, q => (stmtUsage s q).join (summary ss q)

/-- The table entry rustc computes for index `q`. -/
noncomputable def analyze (body : List Stmt) (q : Nat) : Usage := (initUsage q).join (summary body q)

/-- `ρ` assigns each table index its slot address; `Γ` its monomorphic type facts. -/
def execStmt (ρ : Nat → Nat) (Γ : Nat → TyFacts) : Stmt → State → State
  | .use p u, σ => applyUse (ρ p) (Γ p) u σ
  | .tailCall p v, σ => { σ with mem := fun x => if x = ρ p then v else σ.mem x }

noncomputable def run (ρ : Nat → Nat) (Γ : Nat → TyFacts) : List Stmt → State → State
  | [], σ => σ
  | s :: ss, σ => run ρ Γ ss (execStmt ρ Γ s σ)

theorem execStmt_preserves_readOnly_slot (ρ : Nat → Nat) (hρ : ∀ p q, ρ p = ρ q → p = q)
    (Γ : Nat → TyFacts) (s : Stmt) (q : Nat) (h : readOnly (stmtUsage s q) (Γ q) = true)
    (σ : State) : (execStmt ρ Γ s σ).mem (ρ q) = σ.mem (ρ q) := by
  cases s with
  | use p u =>
    show (applyUse (ρ p) (Γ p) u σ).mem (ρ q) = σ.mem (ρ q)
    cases Nat.decEq p q with
    | isTrue hpq =>
      subst hpq
      have hc : readOnly (classify u) (Γ p) = true := by
        have hs : stmtUsage (Stmt.use p u) p = classify u := ite_of_pos rfl _ _
        rw [hs] at h
        exact h
      have hw : u.writes (Γ p) = false :=
        and_false_of_left_true (classify_readOnly_excludes_write u (Γ p)) hc
      rw [applyUse_mem_of_not_writes σ hw]
    | isFalse hpq =>
      exact applyUse_mem_frame (Γ p) u σ (fun heq => hpq (hρ q p heq).symm)
  | tailCall p v =>
    have h' : readOnly Usage.mutateCapture (Γ q) = true := h
    rw [readOnly_mutateCapture] at h'
    cases h'

theorem run_preserves_readOnly_slot (ρ : Nat → Nat) (hρ : ∀ p q, ρ p = ρ q → p = q)
    (Γ : Nat → TyFacts) (q : Nat) :
    ∀ (body : List Stmt) (σ : State), readOnly (summary body q) (Γ q) = true →
      (run ρ Γ body σ).mem (ρ q) = σ.mem (ρ q)
  | [], _, _ => rfl
  | s :: ss, σ, h => by
    have hj : (readOnly (stmtUsage s q) (Γ q) && readOnly (summary ss q) (Γ q)) = true := by
      rw [← readOnly_join]
      exact h
    show (run ρ Γ ss (execStmt ρ Γ s σ)).mem (ρ q) = σ.mem (ρ q)
    rw [run_preserves_readOnly_slot ρ hρ Γ q ss (execStmt ρ Γ s σ) (and_true_right hj),
      execStmt_preserves_readOnly_slot ρ hρ Γ s q (and_true_left hj) σ]

/-- **Soundness of deduced `readonly`.**  Let distinct table indices occupy
distinct slots (`noalias`).  If `read_only` holds for index `q` at its
monomorphic type, then for every body and every adversarial payload in it, the
caller-provided slot of `q` holds the same value after the body as before. -/
theorem deducedReadOnly_no_caller_slot_mutation (ρ : Nat → Nat)
    (hρ : ∀ p q, ρ p = ρ q → p = q) (Γ : Nat → TyFacts) (body : List Stmt) (q : Nat)
    (h : readOnly (analyze body q) (Γ q) = true) (σ : State) :
    (run ρ Γ body σ).mem (ρ q) = σ.mem (ρ q) := by
  have hj : (readOnly (initUsage q) (Γ q) && readOnly (summary body q) (Γ q)) = true := by
    rw [← readOnly_join]
    exact h
  exact run_preserves_readOnly_slot ρ hρ Γ q body σ (and_true_right hj)

/-- The return place is never `readonly`, whatever the body does or omits. -/
theorem returnPlace_never_readonly (body : List Stmt) (t : TyFacts) :
    readOnly (analyze body 0) t = false := by
  unfold analyze
  rw [readOnly_join]
  rfl

/-! ## 6. Why the attributes matter: argument forwarding in the caller

LLVM's `MemCpyOptPass::processImmutArgument` replaces a call argument that is a
fresh `alloca` filled by `memcpy(tmp, src)` with `src` itself when the parameter
is `noalias`, read-only and not captured.  We model a caller that keeps using
`src` after the call, and an environment that may later write through any
address the callee retained. -/

/-- After the call returns, the environment writes `v` through every retained address. -/
def envStep (v : Nat) (σ : State) : State :=
  { σ with mem := fun x => if σ.escaped x = true then v else σ.mem x }

/-- Reference lowering of `f(copy src); … read src`: pass a pointer to a fresh copy. -/
noncomputable def callerReference (t : TyFacts) (callee : List Use) (src tmp envVal : Nat) (σ : State) : Nat :=
  (envStep envVal
    (run1 tmp t callee { σ with mem := fun x => if x = tmp then σ.mem src else σ.mem x })).mem src

/-- Lowering after forwarding: pass `src` itself. -/
noncomputable def callerForwarded (t : TyFacts) (callee : List Use) (src envVal : Nat) (σ : State) : Nat :=
  (envStep envVal (run1 src t callee σ)).mem src

theorem callerReference_eq (t : TyFacts) (callee : List Use) (src tmp envVal : Nat) (σ : State)
    (hne : tmp ≠ src) (hesc : σ.escaped src = false) :
    callerReference t callee src tmp envVal σ = σ.mem src := by
  have hne' : src ≠ tmp := fun h => hne h.symm
  have he : (run1 tmp t callee
      { σ with mem := fun x => if x = tmp then σ.mem src else σ.mem x }).escaped src = false := by
    rw [run1_escaped_frame tmp src t hne']
    exact hesc
  show (if (run1 tmp t callee
        { σ with mem := fun x => if x = tmp then σ.mem src else σ.mem x }).escaped src = true
        then envVal
        else (run1 tmp t callee
          { σ with mem := fun x => if x = tmp then σ.mem src else σ.mem x }).mem src) = σ.mem src
  rw [he, run1_mem_frame tmp src t hne']
  show (if src = tmp then σ.mem src else σ.mem src) = σ.mem src
  exact ite_of_neg hne' _ _

/-- **Forwarding is sound under the deduced attributes.** -/
theorem forwarding_sound_of_deduced_attrs (t : TyFacts) (callee : List Use)
    (src tmp envVal : Nat) (σ : State) (hne : tmp ≠ src) (hesc : σ.escaped src = false)
    (hro : readOnly (summary1 callee) t = true) (hcn : capturesNone (summary1 callee) t = true) :
    callerForwarded t callee src envVal σ = callerReference t callee src tmp envVal σ := by
  rw [callerReference_eq t callee src tmp envVal σ hne hesc]
  have he : (run1 src t callee σ).escaped src = false := by
    rw [run1_capturesNone_no_escape src t callee σ hcn]
    exact hesc
  show (if (run1 src t callee σ).escaped src = true then envVal
        else (run1 src t callee σ).mem src) = σ.mem src
  rw [he, run1_readOnly_preserves src t callee σ hro]
  rfl

/-! ## 7. Post-monomorphization `DROP` refinement and the empty table -/

/-- A parameter that is only dropped is `readonly` and `captures(none)` exactly
at the instantiations whose type has no drop glue. -/
theorem generic_drop_readonly_iff_not_needsDrop (t : TyFacts) :
    (readOnly Usage.dropOnly t = true ↔ t.needsDrop = false) ∧
    (capturesNone Usage.dropOnly t = true ↔ t.needsDrop = false) := by
  obtain ⟨n, f⟩ := t
  cases n <;> cases f <;> decide

/-- The same statement against the operational model: the generic body
`fn consume<T>(_x: T) {}` is slot-preserving for every drop-free instantiation,
and for every instantiation with drop glue some glue changes the slot. -/
theorem generic_drop_semantic_exactness (t : TyFacts) :
    (t.needsDrop = false →
      ∀ (v : Nat) (w e : Bool) (a : Nat) (σ : State),
        (run1 a t [Use.dropWhole v w e] σ).mem a = σ.mem a) ∧
    (t.needsDrop = true →
      ∃ (v : Nat) (w e : Bool) (a : Nat) (σ : State),
        (run1 a t [Use.dropWhole v w e] σ).mem a ≠ σ.mem a) := by
  obtain ⟨n, f⟩ := t
  constructor
  · intro hn v w e a σ
    have hn' : n = false := hn
    subst hn'
    cases w <;> rfl
  · intro hn
    have hn' : n = true := hn
    subst hn'
    refine ⟨1, true, false, 0, ⟨fun _ => 0, fun _ => false⟩, ?_⟩
    intro h
    exact absurd (show (1 : Nat) = 0 from h) (by decide)

/-- Better type facts can only add attributes (monotone refinement at mono time). -/
theorem attrs_monotone_in_type_facts (u : Usage) (f : Bool) :
    (readOnly u ⟨true, f⟩ = true → readOnly u ⟨false, f⟩ = true) ∧
    (capturesNone u ⟨true, f⟩ = true → capturesNone u ⟨false, f⟩ = true) ∧
    (readOnly u ⟨f, false⟩ = true → readOnly u ⟨f, true⟩ = true) := by
  obtain ⟨d, s, m, c⟩ := u
  cases d <;> cases s <;> cases m <;> cases c <;> cases f <;> decide

/-- `A ≤ B`: every attribute in `A` is also in `B`. -/
def Attrs.le (a b : Attrs) : Prop :=
  (a.readonly = true → b.readonly = true) ∧ (a.capturesNone = true → b.capturesNone = true)

/-- An attribute pair is sound for a callee when each attribute it contains is true of
every execution. -/
noncomputable def Sound (callee : List Use) (t : TyFacts) (A : Attrs) : Prop :=
  (A.readonly = true → ∀ (a : Nat) (σ : State), (run1 a t callee σ).mem a = σ.mem a) ∧
  (A.capturesNone = true → ∀ (a : Nat) (σ : State), (run1 a t callee σ).escaped a = σ.escaped a)

theorem deduced_attrs_sound (callee : List Use) (t : TyFacts) :
    Sound callee t (attrsOf (summary1 callee) t) :=
  ⟨fun h a σ => run1_readOnly_preserves a t callee σ h,
   fun h a σ => run1_capturesNone_no_escape a t callee σ h⟩

/-- Soundness is closed under dropping attributes. -/
theorem sound_of_le {callee : List Use} {t : TyFacts} {A B : Attrs} (hle : Attrs.le A B)
    (hB : Sound callee t B) : Sound callee t A :=
  ⟨fun h => hB.1 (hle.1 h), fun h => hB.2 (hle.2 h)⟩

/-- The three session gates: the defining crate must be optimized and
non-incremental for a table to exist, and the using crate must be optimized
and non-incremental to consult it. -/
noncomputable def effectiveAttrs (producerActive consumerActive : Bool) (tbl : List Usage) (i : Nat)
    (t : TyFacts) : Attrs :=
  if (producerActive && consumerActive) = true then lookupAttrs tbl i t else Attrs.noAttrs

/-- **The empty table is a sound coarsening.**  With `-C incremental` (or at
`opt-level=0`) the table is `&[]`: every parameter gets no deduced attribute.
That result is below what any table would give, it is sound for every callee,
and any gate being off yields exactly it. -/
theorem incremental_empty_attrs_sound_coarsening (tbl : List Usage) (i : Nat) (t : TyFacts) :
    lookupAttrs [] i t = Attrs.noAttrs ∧
    Attrs.le (lookupAttrs [] i t) (lookupAttrs tbl i t) ∧
    (∀ callee : List Use, Sound callee t (lookupAttrs [] i t)) ∧
    (∀ p c : Bool, (p && c) = false → effectiveAttrs p c tbl i t = lookupAttrs [] i t) := by
  have h0 : lookupAttrs [] i t = Attrs.noAttrs := lookupAttrs_nil i t
  refine ⟨h0, ?_, ?_, ?_⟩
  · rw [h0]
    exact ⟨fun h => absurd h noAttrs_not_readonly, fun h => absurd h noAttrs_not_capturesNone⟩
  · intro callee
    rw [h0]
    exact ⟨fun h => absurd h noAttrs_not_readonly, fun h => absurd h noAttrs_not_capturesNone⟩
  · intro p c hpc
    show (if (p && c) = true then lookupAttrs tbl i t else Attrs.noAttrs) = lookupAttrs [] i t
    rw [hpc, h0]
    rfl

/-- A caller that forwards exactly when it sees both attributes. -/
noncomputable def callerWith (A : Attrs) (t : TyFacts) (callee : List Use) (src tmp envVal : Nat)
    (σ : State) : Nat :=
  if (A.readonly && A.capturesNone) = true then callerForwarded t callee src envVal σ
  else callerReference t callee src tmp envVal σ

/-- With the deduced attributes the optimizing caller agrees with the reference caller;
with the empty table it *is* the reference caller. -/
theorem callerWith_deduced_eq_reference (t : TyFacts) (callee : List Use)
    (src tmp envVal : Nat) (σ : State) (hne : tmp ≠ src) (hesc : σ.escaped src = false) :
    callerWith (attrsOf (summary1 callee) t) t callee src tmp envVal σ
      = callerReference t callee src tmp envVal σ ∧
    callerWith Attrs.noAttrs t callee src tmp envVal σ
      = callerReference t callee src tmp envVal σ := by
  constructor
  · show (if (readOnly (summary1 callee) t && capturesNone (summary1 callee) t) = true
          then callerForwarded t callee src envVal σ
          else callerReference t callee src tmp envVal σ) = _
    cases hb : (readOnly (summary1 callee) t && capturesNone (summary1 callee) t) with
    | false => rfl
    | true =>
      exact forwarding_sound_of_deduced_attrs t callee src tmp envVal σ hne hesc
        (and_true_left hb) (and_true_right hb)
  · rfl

/-! ## 8. `ImpossibleClauses`: erasing bodies whose `where` clauses cannot hold -/

/-- A small type language: enough for `String: Copy`, `str: Sized`, `dyn Trait<T>: Sized`. -/
inductive Ty where
  | u32
  | string
  | str
  | param (i : Nat)
  | slice (elem : Ty)
  | dynTrait (arg : Ty)

namespace Ty

/-- Instantiate generic parameters. -/
noncomputable def subst (σ : Nat → Ty) : Ty → Ty
  | u32 => u32
  | string => string
  | str => str
  | param i => σ i
  | slice e => slice (subst σ e)
  | dynTrait a => dynTrait (subst σ a)

/-- Mentions a generic parameter (the model's `HAS_FREE_LOCAL_NAMES`). -/
noncomputable def hasParam : Ty → Bool
  | u32 => false
  | string => false
  | str => false
  | param _ => true
  | slice e => hasParam e
  | dynTrait a => hasParam a

/-- `is_structurally_unsized`: decided by the head constructor alone. -/
def structurallyUnsized : Ty → Bool
  | u32 => false
  | string => false
  | str => true
  | param _ => false
  | slice _ => true
  | dynTrait _ => true

/-- The model's trait environment: which types are `Sized` and which are `Copy`. -/
def isSized : Ty → Bool
  | u32 => true
  | string => true
  | str => false
  | param _ => true
  | slice _ => false
  | dynTrait _ => false

def isCopy : Ty → Bool
  | u32 => true
  | string => false
  | str => false
  | param _ => false
  | slice _ => false
  | dynTrait _ => false

theorem subst_of_no_param (σ : Nat → Ty) : ∀ t : Ty, t.hasParam = false → t.subst σ = t
  | u32, _ => rfl
  | string, _ => rfl
  | str, _ => rfl
  | param _, h => by
    have h' : true = false := h
    cases h'
  | slice e, h => by
    show slice (e.subst σ) = slice e
    rw [subst_of_no_param σ e h]
  | dynTrait a, h => by
    show dynTrait (a.subst σ) = dynTrait a
    rw [subst_of_no_param σ a h]

/-- A structurally unsized type stays unsized under every instantiation. -/
theorem not_sized_of_structurallyUnsized (σ : Nat → Ty) :
    ∀ t : Ty, t.structurallyUnsized = true → (t.subst σ).isSized = false
  | u32, h => by have h' : false = true := h; cases h'
  | string, h => by have h' : false = true := h; cases h'
  | str, _ => rfl
  | param _, h => by have h' : false = true := h; cases h'
  | slice _, _ => rfl
  | dynTrait _, _ => rfl

end Ty

inductive Clause where
  | sized (t : Ty)
  | copy (t : Ty)

namespace Clause

/-- Truth of a clause at instantiation `σ`. -/
noncomputable def holds (σ : Nat → Ty) : Clause → Bool
  | sized t => (t.subst σ).isSized
  | copy t => (t.subst σ).isCopy

noncomputable def hasParam : Clause → Bool
  | sized t => t.hasParam
  | copy t => t.hasParam

/-- Truth of a clause in the empty environment, with no instantiation applied. -/
def holdsClosed : Clause → Bool
  | sized t => t.isSized
  | copy t => t.isCopy

/-- `has_structurally_impossible_sized_clause`. -/
def structurallyImpossibleSized : Clause → Bool
  | sized t => t.structurallyUnsized
  | copy _ => false

/-- A *global* clause (no generic parameter) that is false in the empty environment. -/
noncomputable def globallyImpossible (c : Clause) : Bool := !c.hasParam && !c.holdsClosed

theorem not_holds_of_structurallyImpossibleSized (σ : Nat → Ty) :
    ∀ c : Clause, c.structurallyImpossibleSized = true → c.holds σ = false
  | sized t, h => Ty.not_sized_of_structurallyUnsized σ t h
  | copy _, h => by have h' : false = true := h; cases h'

theorem not_holds_of_globallyImpossible (σ : Nat → Ty) :
    ∀ c : Clause, c.globallyImpossible = true → c.holds σ = false
  | sized t, h => by
    have hpc : t.hasParam = false ∧ t.isSized = false := not_and_not_true h
    show (t.subst σ).isSized = false
    rw [Ty.subst_of_no_param σ t hpc.1]
    exact hpc.2
  | copy t, h => by
    have hpc : t.hasParam = false ∧ t.isCopy = false := not_and_not_true h
    show (t.subst σ).isCopy = false
    rw [Ty.subst_of_no_param σ t hpc.1]
    exact hpc.2

end Clause

noncomputable def anyClause (p : Clause → Bool) : List Clause → Bool
  | [] => false
  | c :: cs => p c || anyClause p cs

/-- `has_impossible_clauses` at the pinned revision: the structural `Sized`
test runs on *all* clauses; the trait-solver test only on global ones. -/
noncomputable def hasImpossibleClauses (cs : List Clause) : Bool :=
  anyClause Clause.structurallyImpossibleSized cs || anyClause Clause.globallyImpossible cs

/-- The older `has_impossible_predicates` (as in commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`): global clauses only. -/
noncomputable def hasImpossiblePredicatesLegacy (cs : List Clause) : Bool :=
  anyClause Clause.globallyImpossible cs

/-- All `where` clauses hold at `σ`: the precondition of every well-typed use. -/
noncomputable def ClausesHold (σ : Nat → Ty) : List Clause → Prop
  | [] => True
  | c :: cs => c.holds σ = true ∧ ClausesHold σ cs

theorem not_clausesHold_of_any (σ : Nat → Ty) (p : Clause → Bool)
    (hp : ∀ c, p c = true → c.holds σ = false) :
    ∀ cs : List Clause, anyClause p cs = true → ¬ ClausesHold σ cs
  | [], h, _ => by have h' : false = true := h; cases h'
  | c :: cs, h, hold => by
    obtain ⟨hc, hcs⟩ := hold
    cases or_true_cases h with
    | inl hpc =>
      have hf := hp c hpc
      rw [hf] at hc
      cases hc
    | inr hrest => exact not_clausesHold_of_any σ p hp cs hrest hcs

/-- Detector soundness: a flagged clause list is unsatisfiable at *every* instantiation. -/
theorem hasImpossibleClauses_sound (cs : List Clause) (h : hasImpossibleClauses cs = true)
    (σ : Nat → Ty) : ¬ ClausesHold σ cs := by
  cases or_true_cases h with
  | inl hs =>
    exact not_clausesHold_of_any σ _ (Clause.not_holds_of_structurallyImpossibleSized σ) cs hs
  | inr hg =>
    exact not_clausesHold_of_any σ _ (Clause.not_holds_of_globallyImpossible σ) cs hg

/-- The current detector flags everything the legacy one did … -/
theorem legacy_implies_current (cs : List Clause)
    (h : hasImpossiblePredicatesLegacy cs = true) : hasImpossibleClauses cs = true := by
  unfold hasImpossibleClauses
  have h' : anyClause Clause.globallyImpossible cs = true := h
  rw [h']
  cases anyClause Clause.structurallyImpossibleSized cs <;> rfl

/-- … and strictly more: `dyn Trait<T>: Sized` mentions `T`, so the legacy
detector skips it, although it fails for every `T`. -/
theorem current_strictly_extends_legacy :
    hasImpossibleClauses [Clause.sized (Ty.dynTrait (Ty.param 0))] = true ∧
    hasImpossiblePredicatesLegacy [Clause.sized (Ty.dynTrait (Ty.param 0))] = false ∧
    ∀ σ : Nat → Ty, ¬ ClausesHold σ [Clause.sized (Ty.dynTrait (Ty.param 0))] :=
  ⟨rfl, rfl, fun σ => hasImpossibleClauses_sound _ rfl σ⟩

inductive Behavior where
  | ret (v : Nat)
  /-- Immediate undefined behaviour: what executing `Unreachable` means. -/
  | ub

/-- `b'` refines `b`: either the original is already UB, or the results agree. -/
def Behavior.Refines (b' b : Behavior) : Prop := b = Behavior.ub ∨ b' = b

/-- A body: its behaviour at an instantiation and an argument. -/
abbrev Body := (Nat → Ty) → Nat → Behavior

/-- The erased body: one basic block whose terminator is `Unreachable`. -/
def unreachableBody : Body := fun _ _ => Behavior.ub

/-- The MIR pass. -/
noncomputable def erasePass (cs : List Clause) (body : Body) : Body :=
  if hasImpossibleClauses cs = true then unreachableBody else body

/-- Refinement of items: on every instantiation satisfying the `where` clauses. -/
noncomputable def ItemRefines (cs : List Clause) (opt orig : Body) : Prop :=
  ∀ (σ : Nat → Ty) (arg : Nat), ClausesHold σ cs → (opt σ arg).Refines (orig σ arg)

/-- **Erasure is a refinement, and only vacuously so when it fires.** -/
theorem impossibleClauses_erase_to_unreachable_refines (cs : List Clause) (body : Body) :
    ItemRefines cs (erasePass cs body) body := by
  intro σ arg hold
  unfold erasePass
  cases h : hasImpossibleClauses cs with
  | true => exact absurd hold (hasImpossibleClauses_sound cs h σ)
  | false => exact Or.inr rfl

/-- The clause precondition is load-bearing: at an instantiation that violates
the clauses, the erased body is UB where the original returned normally. -/
theorem erasure_not_refinement_without_clause_precondition :
    ∃ (cs : List Clause) (body : Body) (σ : Nat → Ty) (arg : Nat),
      hasImpossibleClauses cs = true ∧ ¬ ClausesHold σ cs ∧
      ¬ (erasePass cs body σ arg).Refines (body σ arg) := by
  refine ⟨[Clause.copy Ty.string], fun _ x => Behavior.ret (x + 1), fun _ => Ty.u32, 1,
    rfl, hasImpossibleClauses_sound _ rfl _, ?_⟩
  intro h
  cases h with
  | inl h => cases h
  | inr h => cases h

/-! ## 9. `abi_check`: vector registers need the feature on both sides -/

inductive Abi where
  | rust
  | c

inductive VecWidth where
  | w128
  | w256
  | w512

/-- The x86 features named by `features_for_correct_fixed_length_vector_abi`:
`[(128, "sse"), (256, "avx"), (512, "avx512f")]`. -/
structure Features where
  sse : Bool
  avx : Bool
  avx512f : Bool
deriving DecidableEq

def requiredFeature : VecWidth → Features → Bool
  | .w128, f => f.sse
  | .w256, f => f.avx
  | .w512, f => f.avx512f

inductive PassMode where
  | direct
  | indirect

/-- x86-64: the Rust ABI passes vectors of at most 128 bits directly and wider
ones through memory; `extern "C"` passes vectors directly. -/
def passMode : Abi → VecWidth → PassMode
  | .rust, .w128 => .direct
  | .rust, .w256 => .indirect
  | .rust, .w512 => .indirect
  | .c, .w128 => .direct
  | .c, .w256 => .direct
  | .c, .w512 => .direct

/-- `passes_vectors_by_value` for a SIMD-vector layout. -/
def usesVectorRegisters : PassMode → Bool
  | .direct => true
  | .indirect => false

/-- Call-site check: returns early (accepts) for rustic ABIs. -/
def checkCallSite (abi : Abi) (w : VecWidth) (caller : Features) : Bool :=
  match abi with
  | .rust => true
  | .c => !usesVectorRegisters (passMode .c w) || requiredFeature w caller

/-- Definition-site check: applied to every ABI. -/
def checkDefinition (abi : Abi) (w : VecWidth) (callee : Features) : Bool :=
  !usesVectorRegisters (passMode abi w) || requiredFeature w callee

/-- An illustrative register file for one 256-bit argument, as two 128-bit
halves.  With `avx` the value travels in one 256-bit register; without it the
backend must split it over two 128-bit registers.  The only property used is
that the two conventions disagree about where the high half lives. -/
structure Regs where
  xmm0 : Nat
  ymm0hi : Nat
  xmm1 : Nat

def writeVec (avx : Bool) (v : Nat × Nat) (r : Regs) : Regs :=
  if avx = true then { r with xmm0 := v.1, ymm0hi := v.2 }
  else { r with xmm0 := v.1, xmm1 := v.2 }

def readVec (avx : Bool) (r : Regs) : Nat × Nat :=
  if avx = true then (r.xmm0, r.ymm0hi) else (r.xmm0, r.xmm1)

/-- What the callee receives for a 256-bit argument `v`. -/
def transfer256 (abi : Abi) (caller callee : Features) (v : Nat × Nat) (junk : Regs) : Nat × Nat :=
  match passMode abi .w256 with
  | .indirect => v
  | .direct => readVec callee.avx (writeVec caller.avx v junk)

/-- Rust ABI: the value goes through memory, so target features are irrelevant. -/
theorem rustAbi_vector256_transfer_faithful (caller callee : Features) (v : Nat × Nat)
    (junk : Regs) : transfer256 .rust caller callee v junk = v := rfl

/-- **If both checks accept, the callee receives the value the caller sent.** -/
theorem abiCheck_accepts_implies_vector_transfer_faithful (caller callee : Features)
    (v : Nat × Nat) (junk : Regs) (hc : checkCallSite .c .w256 caller = true)
    (hd : checkDefinition .c .w256 callee = true) :
    transfer256 .c caller callee v junk = v := by
  obtain ⟨s, a, z⟩ := caller
  obtain ⟨s', a', z'⟩ := callee
  have ha : a = true := hc
  have ha' : a' = true := hd
  subst ha
  subst ha'
  rfl

/-- The call-site rejection is tight: whenever it fires against a callee that
does use the wide register, some argument arrives corrupted. -/
theorem abiCheck_reject_is_tight (caller callee : Features)
    (hc : checkCallSite .c .w256 caller = false) (hcallee : callee.avx = true) :
    ∃ (v : Nat × Nat) (junk : Regs), transfer256 .c caller callee v junk ≠ v := by
  obtain ⟨s, a, z⟩ := caller
  obtain ⟨s', a', z'⟩ := callee
  have ha : a = false := hc
  have ha' : a' = true := hcallee
  subst ha
  subst ha'
  refine ⟨(0, 1), ⟨0, 0, 0⟩, ?_⟩
  intro h
  exact absurd (show ((0 : Nat), (0 : Nat)) = (0, 1) from h) (by decide)

/-! ### Decision-table transcriptions (no soundness claim)

`do_check_unsized_params` and the size test of `move_check`, written out so the
probe's cases can be replayed as closed computations. -/

/-- `do_check_unsized_params`: accepted iff the ABI is rustic or every parameter is sized. -/
def checkUnsizedParams (abi : Abi) (allParamsSized : Bool) : Bool :=
  match abi with
  | .rust => true
  | .c => allParamsSized

/-- The `large_assignments` size test: `limit = 0` disables it, a `Move` operand
that is itself a call argument is exempt, otherwise sizes above the limit lint. -/
def moveLint (limit size : Nat) (isMoveOperandOfCall : Bool) : Bool :=
  !(limit == 0) && !isMoveOperandOfCall && decide (limit < size)

example : checkUnsizedParams .c false = false := rfl
example : checkUnsizedParams .rust false = true := rfl
example : moveLint 64 256 false = true := rfl
example : moveLint 0 256 false = false := rfl
example : moveLint 64 256 true = false := rfl
example : checkCallSite .c .w256 ⟨true, false, false⟩ = false := rfl
example : checkCallSite .c .w256 ⟨true, true, false⟩ = true := rfl
example : checkCallSite .c .w128 ⟨true, false, false⟩ = true := rfl
example : checkDefinition .c .w256 ⟨true, false, false⟩ = false := rfl
example : checkDefinition .rust .w256 ⟨true, false, false⟩ = true := rfl

/-! ## 10. Sharpness: each rule is necessary

Every statement below exhibits concrete data; nothing is assumed. -/

/-- The visitor with the `Operand::Move` call-argument rule deleted. -/
def classifyOmitCallMove : Use → Usage
  | .nonUse => Usage.empty
  | .read => Usage.empty
  | .derefAccess => Usage.empty
  | .store _ => Usage.mutateOnly
  | .dropWhole _ _ _ => Usage.dropOnly
  | .dropProjected _ _ _ => Usage.mutateCapture
  | .mutBorrow _ _ _ => Usage.mutateCapture
  | .rawConstBorrow _ _ _ => Usage.mutateCapture
  | .sharedBorrow _ _ _ => Usage.sharedBorrowCapture
  | .callMove _ _ _ => Usage.empty

/-- **CE1.**  `fn f(x: Big) { g(x) }` where `g` writes its parameter.  Without
the call-argument rule the analysis grants `readonly` and `captures(none)`; a
caller that forwards its own object then observes `g`'s write, while the
reference lowering does not. -/
theorem ce1_omitting_indirect_call_move_mutate_causes_caller_aliasing_miscompile :
    ∃ (callee : List Use) (t : TyFacts) (σ : State) (src tmp envVal : Nat),
      tmp ≠ src ∧ σ.escaped src = false ∧
      readOnly (summaryWith classifyOmitCallMove callee) t = true ∧
      capturesNone (summaryWith classifyOmitCallMove callee) t = true ∧
      readOnly (summary1 callee) t = false ∧
      callerReference t callee src tmp envVal σ = σ.mem src ∧
      callerForwarded t callee src envVal σ ≠ callerReference t callee src tmp envVal σ :=
  ⟨[Use.callMove 99 true false], ⟨false, true⟩, ⟨fun _ => 7, fun _ => false⟩, 0, 1, 5,
    by decide, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- `read_only` with the `Freeze` test deleted. -/
def readOnlyIgnoringFreeze (u : Usage) (t : TyFacts) : Bool :=
  !u.mutate && !(u.drop && t.needsDrop)

/-- **CE2.**  `&x` on a type containing `UnsafeCell`: without the `Freeze` test
`readonly` would be emitted although the slot is written through the shared
reference.  The same body at a `Freeze` type leaves the slot alone. -/
theorem ce2_shared_borrow_non_freeze_unsafecell_violates_readonly :
    ∃ (callee : List Use) (t : TyFacts) (a : Nat) (σ : State),
      t.isFreeze = false ∧
      readOnlyIgnoringFreeze (summary1 callee) t = true ∧
      readOnly (summary1 callee) t = false ∧
      (run1 a t callee σ).mem a ≠ σ.mem a ∧
      readOnly (summary1 callee) { t with isFreeze := true } = true ∧
      (run1 a { t with isFreeze := true } callee σ).mem a = σ.mem a :=
  ⟨[Use.sharedBorrow 42 true false], ⟨false, false⟩, 0, ⟨fun _ => 7, fun _ => false⟩,
    rfl, rfl, rfl, by decide, rfl, rfl⟩

/-- The pointer attributes relevant to LLVM's verifier rule
"Attributes writable and readonly are incompatible!". -/
structure LlvmPtrAttrs where
  readonly : Bool
  writable : Bool
  capturesNone : Bool
deriving DecidableEq

def LlvmPtrAttrs.verifierAccepts (a : LlvmPtrAttrs) : Bool := !(a.writable && a.readonly)

/-- The `sret` pointer: codegen adds `writable` unconditionally when optimizing;
the deduced attributes come from table index 0. -/
def sretAttrs (u : Usage) (t : TyFacts) : LlvmPtrAttrs := ⟨readOnly u t, true, capturesNone u t⟩

/-- With the `MUTATE` seed the `sret` attribute set is always verifier-clean. -/
theorem sret_attrs_always_verifier_clean (body : List Stmt) (t : TyFacts) :
    (sretAttrs (analyze body 0) t).verifierAccepts = true := by
  show (!(true && readOnly (analyze body 0) t)) = true
  rw [returnPlace_never_readonly]
  rfl

/-- **CE3.**  A body that never writes `_0` (for example `loop {}`, or a body
erased to `unreachable`).  Without the seed the return place would be deduced
`readonly`, and the `sret` pointer would carry both `writable` and `readonly`. -/
theorem ce3_return_place_without_mutate_emits_contradictory_writable_readonly :
    ∃ (body : List Stmt) (t : TyFacts),
      (sretAttrs (summary body 0) t).readonly = true ∧
      (sretAttrs (summary body 0) t).writable = true ∧
      (sretAttrs (summary body 0) t).verifierAccepts = false ∧
      (sretAttrs (analyze body 0) t).verifierAccepts = true :=
  ⟨[], ⟨false, true⟩, rfl, rfl, rfl, rfl⟩

/-- **CE4.**  `extern "C"` with a 256-bit vector is `PassMode::Direct`.  A
caller without `avx` and a callee with it: the call-site check rejects, and if
it did not, the callee would read a high half the caller never wrote.  The same
feature sets under the Rust ABI are harmless. -/
theorem ce4_extern_c_vector_passMode_direct_without_caller_feature_faults :
    ∃ (caller callee : Features) (v : Nat × Nat) (junk : Regs),
      usesVectorRegisters (passMode .c .w256) = true ∧
      checkCallSite .c .w256 caller = false ∧
      checkDefinition .c .w256 callee = true ∧
      transfer256 .c caller callee v junk ≠ v ∧
      usesVectorRegisters (passMode .rust .w256) = false ∧
      transfer256 .rust caller callee v junk = v :=
  ⟨⟨true, false, false⟩, ⟨true, true, false⟩, (1, 2), ⟨0, 99, 0⟩,
    rfl, rfl, rfl, by decide, rfl, rfl⟩

/-- A detector that tests one sample instantiation instead of skipping clauses
that mention generic parameters. -/
noncomputable def naiveImpossible (cs : List Clause) : Bool :=
  anyClause (fun c => !c.holds (fun _ => Ty.string)) cs

/-- **CE5.**  `fn f<T: Copy>(x) { x + 1 }`.  `T: Copy` fails for `T = String`,
but erasing the body breaks the well-typed instantiation `T = u32`. -/
theorem ce5_erasing_on_instantiation_dependent_clause_breaks_valid_instantiation :
    ∃ (cs : List Clause) (body : Body) (σ : Nat → Ty) (arg : Nat),
      naiveImpossible cs = true ∧ hasImpossibleClauses cs = false ∧ ClausesHold σ cs ∧
      ¬ ((if naiveImpossible cs = true then unreachableBody else body) σ arg).Refines
          (body σ arg) := by
  refine ⟨[Clause.copy (Ty.param 0)], fun _ x => Behavior.ret (x + 1), fun _ => Ty.u32, 1,
    rfl, rfl, ⟨rfl, True.intro⟩, ?_⟩
  intro h
  cases h with
  | inl h => cases h
  | inr h => cases h

/-- **CE6.**  The tail-call rule must cover parameters the function's own
statements only read: a `become` rewrites the slot although no MIR statement
names it. -/
theorem ce6_tail_call_rewrites_slot_of_parameter_that_is_only_read :
    ∃ (body : List Stmt) (Γ : Nat → TyFacts) (σ : State),
      readOnly (summary [Stmt.use 1 Use.read] 1) (Γ 1) = true ∧
      readOnly (analyze body 1) (Γ 1) = false ∧
      (run (fun p => p) Γ body σ).mem 1 ≠ σ.mem 1 :=
  ⟨[Stmt.use 1 Use.read, Stmt.tailCall 1 9], fun _ => ⟨false, true⟩,
    ⟨fun _ => 7, fun _ => false⟩, rfl, rfl, by decide⟩

/-! ## 10b. The model's verdicts on the differential probe's functions

Each line replays, as a closed computation, the `(readonly, captures(none))`
pair the transcribed rules assign to one function of the accompanying probe,
given the uses visible in that function's optimized MIR.  The same pairs are
what the probe observed on the compiler's emitted LLVM signatures when
deduction was active.  This ties the transcription to executed behaviour on
those inputs; it is not a proof of agreement in general. -/

/-- Verdict for an argument with the listed uses. -/
noncomputable def argVerdict (us : List Use) (t : TyFacts) : Bool × Bool :=
  (readOnly (summary1 us) t, capturesNone (summary1 us) t)

/-- Verdict for table index `q` of a whole body. -/
noncomputable def indexVerdict (body : List Stmt) (q : Nat) (t : TyFacts) : Bool × Bool :=
  (readOnly (analyze body q) t, capturesNone (analyze body q) t)

/-- `[u64; 8]`-like: `Freeze`, no drop glue. -/
def freezeNoDrop : TyFacts := ⟨false, true⟩
/-- `[Cell<u64>; 8]`-like: not `Freeze`, no drop glue. -/
def cellNoDrop : TyFacts := ⟨false, false⟩
/-- `[String; 8]`-like: `Freeze`, has drop glue. -/
def freezeWithDrop : TyFacts := ⟨true, true⟩

-- `read_big_freeze`: two field reads.
example : argVerdict [.read, .read] freezeNoDrop = (true, true) := rfl
-- `shared_borrow_big_freeze`: `&_1`, then a field read.
example : argVerdict [.sharedBorrow 0 false false, .read] freezeNoDrop = (true, false) := rfl
-- `shared_borrow_big_cell`: `&_1`, then `&(_1.0)[0]`.
example : argVerdict [.sharedBorrow 0 false false, .sharedBorrow 0 false false] cellNoDrop
    = (false, false) := rfl
-- `raw_const_borrow_big_freeze`: `&raw const _1`, then a field read.
example : argVerdict [.rawConstBorrow 0 false false, .read] freezeNoDrop = (false, false) := rfl
-- `mutate_local_copy_big_freeze`: read, in-place store, two reads.
example : argVerdict [.read, .store 57005, .read, .read] freezeNoDrop = (false, true) := rfl
-- `generic_drop_only::<u64>` and `::<String>`: `drop(_1)` only.
example : argVerdict [.dropWhole 0 false false] freezeNoDrop = (true, true) := rfl
example : argVerdict [.dropWhole 0 false false] freezeWithDrop = (false, false) := rfl
-- `forward_by_move_indirect` and the hand-written-MIR `custom_call_move_arg`: `f(move _1)`.
example : argVerdict [.callMove 0 false false] freezeNoDrop = (false, false) := rfl
-- Hand-written-MIR `custom_call_copy_arg`: `f(copy _1)` is a plain read of `_1`.
example : argVerdict [.read] freezeNoDrop = (true, true) := rfl
-- `ret_never_returns`: `_0` is never mentioned.
example : indexVerdict [] 0 freezeNoDrop = (false, true) := rfl
-- `ret_not_captured`: `_0 = [copy _1; 80]`.
example : indexVerdict [.use 0 (.store 0)] 0 freezeNoDrop = (false, true) := rfl
-- `ret_captured`: `_0` is a call destination.
example : indexVerdict [.use 0 (.mutBorrow 0 false false)] 0 freezeNoDrop = (false, false) := rfl
-- `tail_reads_then_becomes`: both arguments only read, then `become`.
example : indexVerdict [.use 1 .read, .use 2 .read, .tailCall 1 0] 1 freezeNoDrop
    = (false, false) := rfl
example : indexVerdict [.use 1 .read, .use 2 .read, .tailCall 1 0] 2 freezeNoDrop
    = (false, false) := rfl
-- `mixed_read_then_forward`: index 1 read, index 2 forwarded by move.
example : indexVerdict [.use 1 .read, .use 2 (.callMove 0 false false)] 1 freezeNoDrop
    = (true, true) := rfl
example : indexVerdict [.use 1 .read, .use 2 (.callMove 0 false false)] 2 freezeNoDrop
    = (false, false) := rfl

end DeduceParamAttrs

/-! ## 11. Mechanical audit

`#print axioms` for the headline results, then a command that walks every
declaration of this module and fails elaboration on any forbidden dependency. -/

#print axioms DeduceParamAttrs.deducedReadOnly_no_caller_slot_mutation
#print axioms DeduceParamAttrs.rmeta_trim_lookup_eq
#print axioms DeduceParamAttrs.padTo_trim_of_canonical
#print axioms DeduceParamAttrs.forwarding_sound_of_deduced_attrs
#print axioms DeduceParamAttrs.incremental_empty_attrs_sound_coarsening
#print axioms DeduceParamAttrs.generic_drop_readonly_iff_not_needsDrop
#print axioms DeduceParamAttrs.impossibleClauses_erase_to_unreachable_refines
#print axioms DeduceParamAttrs.abiCheck_accepts_implies_vector_transfer_faithful
#print axioms DeduceParamAttrs.ce1_omitting_indirect_call_move_mutate_causes_caller_aliasing_miscompile
#print axioms DeduceParamAttrs.ce2_shared_borrow_non_freeze_unsafecell_violates_readonly
#print axioms DeduceParamAttrs.ce3_return_place_without_mutate_emits_contradictory_writable_readonly
#print axioms DeduceParamAttrs.ce4_extern_c_vector_passMode_direct_without_caller_feature_faults
#print axioms DeduceParamAttrs.Usage.bits_join

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let ns : Name := `DeduceParamAttrs
  -- Forbidden identifiers, assembled from fragments (see the header comment).
  let recSuffix : String := "_unsafe" ++ "_rec"
  let choiceAx : Name := Name.mkStr (Name.mkSimple "Classical") ("cho" ++ "ice")
  let admitAx : Name := Name.mkSimple ("so" ++ "rryAx")
  let reduceBoolAx : Name := Name.mkStr (Name.mkSimple "Lean") ("ofReduce" ++ "Bool")
  let compilerTrustAx : Name := Name.mkStr (Name.mkSimple "Lean") ("trust" ++ "Compiler")
  let forbidden : Array Name := #[choiceAx, admitAx, reduceBoolAx, compilerTrustAx]
  -- The audit is meaningless if a forbidden name is misspelled: each must exist.
  let unknownForbidden := forbidden.filter (fun n => !env.contains n)
  let hasRecSuffix (n : Name) : Bool := n.components.any (fun c => c.toString == recSuffix)
  -- Declarations of the module being elaborated live in the second stage of
  -- the constant map (`map₂`).  `map₁` holds imported constants only, so a
  -- check restricted to `map₁` would say nothing about this file.
  let localNames : Array Name := env.constants.map₂.foldl (fun acc n _ => acc.push n) #[]
  let mine : Array Name := localNames.filter (fun n => ns.isPrefixOf n)
  let importedInNamespace : Nat :=
    env.constants.map₁.fold (fun acc n _ => if ns.isPrefixOf n then acc + 1 else acc) 0
  let importedRecSuffixInNamespace : Nat :=
    env.constants.map₁.fold
      (fun acc n _ => if ns.isPrefixOf n && hasRecSuffix n then acc + 1 else acc) 0
  let localRecSuffix : Array Name := localNames.filter hasRecSuffix
  let mut used : Array Name := #[]
  let mut offenders : Array (Name × Name) := #[]
  let mut theorems : Nat := 0
  let mut definitions : Nat := 0
  let mut axiomFreeTheorems : Nat := 0
  let mut badKind : Array Name := #[]
  for n in mine do
    let axs ← collectAxioms n
    match env.find? n with
    | some ci =>
      if ci.isUnsafe || ci.isPartial then badKind := badKind.push n
      match ci with
      | .thmInfo _ =>
        theorems := theorems + 1
        if axs.isEmpty then axiomFreeTheorems := axiomFreeTheorems + 1
      | .defnInfo _ => definitions := definitions + 1
      | .axiomInfo _ => badKind := badKind.push n
      | .opaqueInfo _ => badKind := badKind.push n
      | _ => pure ()
    | none => pure ()
    for a in axs do
      unless used.contains a do used := used.push a
      if forbidden.contains a then offenders := offenders.push (n, a)
  -- Results that must exist and must not depend on any axiom at all.
  let strict : Array Name := #[
    `DeduceParamAttrs.deducedReadOnly_no_caller_slot_mutation,
    `DeduceParamAttrs.rmeta_trim_lookup_eq,
    `DeduceParamAttrs.trim_idem,
    `DeduceParamAttrs.trim_padTo,
    `DeduceParamAttrs.padTo_trim_of_canonical,
    `DeduceParamAttrs.forwarding_sound_of_deduced_attrs,
    `DeduceParamAttrs.returnPlace_never_readonly,
    `DeduceParamAttrs.incremental_empty_attrs_sound_coarsening,
    `DeduceParamAttrs.generic_drop_readonly_iff_not_needsDrop,
    `DeduceParamAttrs.generic_drop_semantic_exactness,
    `DeduceParamAttrs.hasImpossibleClauses_sound,
    `DeduceParamAttrs.impossibleClauses_erase_to_unreachable_refines,
    `DeduceParamAttrs.erasure_not_refinement_without_clause_precondition,
    `DeduceParamAttrs.current_strictly_extends_legacy,
    `DeduceParamAttrs.abiCheck_accepts_implies_vector_transfer_faithful,
    `DeduceParamAttrs.abiCheck_reject_is_tight,
    `DeduceParamAttrs.ce1_omitting_indirect_call_move_mutate_causes_caller_aliasing_miscompile,
    `DeduceParamAttrs.ce2_shared_borrow_non_freeze_unsafecell_violates_readonly,
    `DeduceParamAttrs.ce3_return_place_without_mutate_emits_contradictory_writable_readonly,
    `DeduceParamAttrs.ce4_extern_c_vector_passMode_direct_without_caller_feature_faults,
    `DeduceParamAttrs.ce5_erasing_on_instantiation_dependent_clause_breaks_valid_instantiation,
    `DeduceParamAttrs.ce6_tail_call_rewrites_slot_of_parameter_that_is_only_read]
  let mut missing : Array Name := #[]
  let mut strictWithAxioms : Array Name := #[]
  for n in strict do
    if env.contains n then
      let axs ← collectAxioms n
      unless axs.isEmpty do strictWithAxioms := strictWithAxioms.push n
    else
      missing := missing.push n
  logInfo m!"AUDIT module-local constants in namespace: {mine.size} \
    (theorems: {theorems}, of which axiom-free: {axiomFreeTheorems}; definitions: {definitions})"
  logInfo m!"AUDIT axioms reachable from any module-local constant, \
    auto-generated ones included: {used}"
  logInfo m!"AUDIT forbidden axiom names checked: {forbidden.size} \
    (unknown to the environment: {unknownForbidden.size}); offenders: {offenders.size}"
  logInfo m!"AUDIT headline theorems required axiom-free: {strict.size}; \
    missing: {missing.size}; depending on some axiom: {strictWithAxioms.size}"
  logInfo m!"AUDIT unsafe recursion companions: module-local (map₂) = {localRecSuffix.size}; \
    imported under this namespace (map₁) = {importedRecSuffixInNamespace} \
    of {importedInNamespace} imported constants under this namespace"
  logInfo m!"AUDIT unsafe/partial/opaque/axiom declarations: {badKind.size}"
  unless unknownForbidden.isEmpty do throwError "audit misconfigured: {unknownForbidden}"
  unless offenders.isEmpty do throwError "forbidden axioms: {offenders}"
  unless localRecSuffix.isEmpty do throwError "unsafe recursion companions: {localRecSuffix}"
  unless badKind.isEmpty do throwError "unsafe/partial/opaque/axiom declarations: {badKind}"
  unless missing.isEmpty do throwError "missing theorems: {missing}"
  unless strictWithAxioms.isEmpty do throwError "headline theorems using axioms: {strictWithAxioms}"
  unless mine.size > 0 do throwError "audit saw no module-local constants"
