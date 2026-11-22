-- Self-contained Lean 4 (`v4.34.1`) formalization of normative forwards-compatibility
-- and frontend-drift-resilient verification interfaces:
--   1. Monotonic envelope refinement (`forwards_compatible_envelope_transfer` &
--      `normative_proof_transfers_to_all_conforming_compilers`):
--      `NormativeEnvelope ⊑ PinnedCompilerProfile c` transferring safety across any
--      conforming compiler without claiming soundness over compiler bugs outside the envelope.
--   2. Non-normative non-transfer countersamples (`non_normative_layout_countersample`):
--      Proving non-transfer when specs inspect `#[repr(Rust)]` layout/size, `TypeId`/`type_name`
--      (`Infallible = !`), or stdlib private fields (`Unique<T> -> BoxRaw<T>`).
--   3. Structural proof-survival invariance under Lean 4 kernel β/ι reduction:
--      - `trunk_addition_preserves_existing_wp`: adding new `TrunkStmt` constructors (`evalExt`)
--      - `profile_flag_preserves_unaffected_wp`: adding orthogonal `SemProfile` capability flags
--      - `wp_invariant_under_temp_and_cfg_refactoring` vs. `raw_cfg_cert_breaks_on_block_split`:
--        absorbing temporary renumbering, `nopRetag` insertion, and basic-block splitting.
--   4. Opaque normative stdlib contracts vs. inlined callee MIR bodies:
--      - `callee_impl_drift_breaks_inlined_body` vs. `opaque_normative_contract_absorbs_stdlib_drift`
--        (and `inlined_stdlib_mir_breaks_across_boxraw_refactor`).
--   5. Mandatory two-route governance for non-normative dependencies:
--      - `non_normative_assumption_logged_or_compile_guarded` & `zerocopy_route_a_padding_free_witness`.
--
-- Checked with:
--   lean -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true NormativeForwardsCompatibility.lean
-- Axioms: zero (`does not depend on any axioms` verified via `#print axioms` on every theorem).

prelude
import Init.Core

namespace NormativeForwardsCompatibility

/-!
## Self-Contained `Init.Core` Arithmetic Helpers
-/

theorem nat_eq_of_beq_eq_true : ∀ {a b : Nat}, Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => nomatch h
  | _ + 1, 0, h => nomatch h
  | _ + 1, _ + 1, h => congrArg Nat.succ (nat_eq_of_beq_eq_true h)

/-!
## Section 1: Operational Outcomes, Stdlib Contracts, and the Normative Stability Envelope
-/

/-- Runtime execution outcome of a lowered MIR body. -/
inductive Outcome (Val : Type) where
  | ok : Val → Outcome Val
  | ub : Outcome Val
  | diverge : Outcome Val
  deriving DecidableEq

/-- Partial-correctness memory-safety and postcondition judgment: UB is unconditionally
    forbidden (`False`), termination must satisfy `Q`, and non-termination is memory-safe. -/
def SafeFor {Val : Type} (out : Outcome Val) (Q : Val → Prop) : Prop :=
  match out with
  | .ok v => Q v
  | .ub => False
  | .diverge => True

theorem safeFor_mono {Val : Type} {out : Outcome Val} {P Q : Val → Prop}
    (hSafe : SafeFor out P) (hImp : ∀ v, P v → Q v) : SafeFor out Q :=
  match out, hSafe with
  | .ok v, hv => hImp v hv
  | .ub, hFalse => False.elim hFalse
  | .diverge, _ => True.intro

/-- Representative `core` / `alloc` external functions called from verified user code. -/
inductive StdlibFn where
  | boxNewAndDeref
  | sliceGetUnchecked
  | atomicLoadUsize
  deriving DecidableEq

/-- Normative Category-A precondition documented in `core` / `alloc` stable API docs:
    - `Box::new` followed by dereference is safe for every single argument `x :: .nil`.
    - `slice::get_unchecked` (modeled over `baseVal :: len :: idx :: .nil`) requires `idx + 1 ≤ len`.
    - `AtomicUsize::load` (`atomicLoadUsize` over `cellVal :: orderingValid :: .nil`) requires a valid
      non-Release load ordering (`orderingValid = 1`). -/
def NormativeStdlibPre : StdlibFn → List Nat → Prop
  | .boxNewAndDeref, _ :: .nil => True
  | .boxNewAndDeref, _ => False
  | .sliceGetUnchecked, _ :: len :: idx :: .nil => Nat.ble (idx + 1) len = true
  | .sliceGetUnchecked, _ => False
  | .atomicLoadUsize, _ :: ordValid :: .nil => ordValid = 1
  | .atomicLoadUsize, _ => False

/-- Normative Category-A postcondition documented in `core` / `alloc` stable API docs. -/
def NormativeStdlibPost : StdlibFn → List Nat → Nat → Prop
  | .boxNewAndDeref, x :: .nil, ret => ret = x
  | .boxNewAndDeref, _, _ => False
  | .sliceGetUnchecked, baseVal :: _ :: idx :: .nil, ret => ret = baseVal + idx
  | .sliceGetUnchecked, _, _ => False
  | .atomicLoadUsize, cellVal :: _ :: .nil, ret => ret = cellVal
  | .atomicLoadUsize, _, _ => False

/-- Concrete compiler implementation `c`, separating Category-A normative invariants from
    Category-B cross-release / conforming-compiler degrees of freedom. -/
structure CompilerChoice where
  reprCScalarOffset : Nat
  optionNonNullZeroIsNone : Bool
  reprRustFieldAOff : Nat
  reprRustFieldBOff : Nat
  reprRustStructSize : Nat
  infallibleEqNever : Bool
  boxUsesBoxRaw : Bool
  atomicUsesGenericWrapper : Bool
  deriveDebugConcatStrings : Bool
  coreBody : StdlibFn → List Nat → Outcome Nat

/-- Opaque stdlib contract conformance: whenever a caller satisfies the documented Category-A
    precondition of `f`, compiler `c`'s concrete `core`/`alloc` implementation never triggers UB
    and establishes the documented Category-A postcondition. -/
def CallsSatisfyNormativeSpec (c : CompilerChoice) : Prop :=
  ∀ (f : StdlibFn) (args : List Nat),
    NormativeStdlibPre f args →
    SafeFor (c.coreBody f args) (NormativeStdlibPost f args)

/-- A compiler `c` conforms to Rust's normative specification (`zerocopy/POLICIES.md` +
    Rust Reference + `core`/`alloc` stable docs) iff all Category-A layout and stdlib contract
    invariants hold, leaving all Category-B choices completely unconstrained. -/
def ConformingCompiler (c : CompilerChoice) : Prop :=
  c.reprCScalarOffset = 0 ∧
  c.optionNonNullZeroIsNone = true ∧
  c.reprRustFieldAOff ≠ c.reprRustFieldBOff ∧
  Nat.ble (c.reprRustFieldAOff + 8) c.reprRustStructSize = true ∧
  Nat.ble (c.reprRustFieldBOff + 8) c.reprRustStructSize = true ∧
  CallsSatisfyNormativeSpec c

/-- Standard compliant `core` implementation for `boxNewAndDeref`, `sliceGetUnchecked`, and `atomicLoadUsize`. -/
def standardCoreBody : StdlibFn → List Nat → Outcome Nat
  | .boxNewAndDeref, x :: .nil => .ok x
  | .boxNewAndDeref, _ => .ub
  | .sliceGetUnchecked, baseVal :: len :: idx :: .nil =>
    match Nat.ble (idx + 1) len with
    | true => .ok (baseVal + idx)
    | false => .ub
  | .sliceGetUnchecked, _ => .ub
  | .atomicLoadUsize, cellVal :: ordValid :: .nil =>
    match Nat.beq ordValid 1 with
    | true => .ok cellVal
    | false => .ub
  | .atomicLoadUsize, _ => .ub

theorem standardCoreBody_satisfies_spec :
    ∀ (f : StdlibFn) (args : List Nat),
      NormativeStdlibPre f args →
      SafeFor (standardCoreBody f args) (NormativeStdlibPost f args)
  | .boxNewAndDeref, .nil, hPre => False.elim hPre
  | .boxNewAndDeref, _ :: .nil, _ => rfl
  | .boxNewAndDeref, _ :: _ :: _, hPre => False.elim hPre
  | .sliceGetUnchecked, .nil, hPre => False.elim hPre
  | .sliceGetUnchecked, _ :: .nil, hPre => False.elim hPre
  | .sliceGetUnchecked, _ :: _ :: .nil, hPre => False.elim hPre
  | .sliceGetUnchecked, baseVal :: len :: idx :: .nil, hPre => by
    change SafeFor
      (match Nat.ble (idx + 1) len with
       | true => Outcome.ok (baseVal + idx)
       | false => Outcome.ub)
      (fun ret => ret = baseVal + idx)
    rw [hPre]
    exact rfl
  | .sliceGetUnchecked, _ :: _ :: _ :: _ :: _, hPre => False.elim hPre
  | .atomicLoadUsize, .nil, hPre => False.elim hPre
  | .atomicLoadUsize, _ :: .nil, hPre => False.elim hPre
  | .atomicLoadUsize, cellVal :: ordValid :: .nil, hPre => by
    change ordValid = 1 at hPre
    cases hPre
    exact rfl
  | .atomicLoadUsize, _ :: _ :: _ :: _, hPre => False.elim hPre

/-- Concrete conforming compiler 1 (`rustc 1.94`-era):
    `#[repr(Rust)]` offsets `(0, 8)`, size `16`, `Infallible != !`, `Box.0 = Unique`,
    nominal `AtomicUsize`, legacy `#[derive(Debug)]`. -/
def rustc_1_96 : CompilerChoice :=
  { reprCScalarOffset := 0
    optionNonNullZeroIsNone := true
    reprRustFieldAOff := 0
    reprRustFieldBOff := 8
    reprRustStructSize := 16
    infallibleEqNever := false
    boxUsesBoxRaw := false
    atomicUsesGenericWrapper := false
    deriveDebugConcatStrings := false
    coreBody := standardCoreBody }

/-- Concrete conforming compiler 2 (`rustc 1.102-nightly` + `-Z randomize-layout`):
    `#[repr(Rust)]` offsets `(16, 0)` with padding (`size = 24`), `Infallible = !`,
    `Box.0 = BoxRaw`, generic `Atomic<usize>`, concatenated `#[derive(Debug)]` field strings. -/
def rustc_1_100_rand : CompilerChoice :=
  { reprCScalarOffset := 0
    optionNonNullZeroIsNone := true
    reprRustFieldAOff := 16
    reprRustFieldBOff := 0
    reprRustStructSize := 24
    infallibleEqNever := true
    boxUsesBoxRaw := true
    atomicUsesGenericWrapper := true
    deriveDebugConcatStrings := true
    coreBody := standardCoreBody }

theorem rustc_1_96_conforming : ConformingCompiler rustc_1_96 :=
  And.intro rfl
    (And.intro rfl
      (And.intro (fun h => nomatch h)
        (And.intro rfl
          (And.intro rfl standardCoreBody_satisfies_spec))))

theorem rustc_1_100_rand_conforming : ConformingCompiler rustc_1_100_rand :=
  And.intro rfl
    (And.intro rfl
      (And.intro (fun h => nomatch h)
        (And.intro rfl
          (And.intro rfl standardCoreBody_satisfies_spec))))

theorem conforming_compilers_disagree_on_category_b :
    rustc_1_96.reprRustStructSize ≠ rustc_1_100_rand.reprRustStructSize ∧
    rustc_1_96.infallibleEqNever ≠ rustc_1_100_rand.infallibleEqNever ∧
    rustc_1_96.boxUsesBoxRaw ≠ rustc_1_100_rand.boxUsesBoxRaw ∧
    rustc_1_96.atomicUsesGenericWrapper ≠ rustc_1_100_rand.atomicUsesGenericWrapper :=
  And.intro (fun h => nomatch h)
    (And.intro (fun h => nomatch h)
      (And.intro (fun h => nomatch h) (fun h => nomatch h)))

/-!
## Section 2: Verification Profiles and Refinement Preorder (`RefinesProfile`)
-/

/-- A verification profile pairs a set of admissible compilers with a monotonic relational
    call contract used to verify external `core`/`alloc` calls. -/
structure SemProfile where
  admissible : CompilerChoice → Prop
  callContract : StdlibFn → List Nat → (Nat → Prop) → Prop
  callMono : ∀ (f : StdlibFn) (args : List Nat) (P Q : Nat → Prop),
    (∀ v, P v → Q v) → callContract f args P → callContract f args Q

/-- Refinement preorder `RefinesProfile P_abs P_conc` (`P_abs ⊑ P_conc`): `P_abs` is a sound
    over-approximation of `P_conc` when every compiler admitted by `P_conc` is covered by
    `P_abs` and every call obligation proved against `P_abs` establishes `P_conc.callContract`. -/
def RefinesProfile (P_abs P_conc : SemProfile) : Prop :=
  (∀ c, P_conc.admissible c → P_abs.admissible c) ∧
  (∀ f args Q, P_abs.callContract f args Q → P_conc.callContract f args Q)

theorem refinesProfile_refl (P : SemProfile) : RefinesProfile P P :=
  And.intro (fun _ h => h) (fun _ _ _ h => h)

theorem refinesProfile_trans {P1 P2 P3 : SemProfile}
    (h12 : RefinesProfile P1 P2) (h23 : RefinesProfile P2 P3) : RefinesProfile P1 P3 :=
  And.intro
    (fun c hc => h12.1 c (h23.1 c hc))
    (fun f args Q hQ => h23.2 f args Q (h12.2 f args Q hQ))

/-- **Normative Profile (`π_normative`):** Quantifies universally over all `ConformingCompiler`s
    and verifies stdlib calls exclusively against their opaque Category-A contracts. -/
def NormativeEnvelope : SemProfile :=
  { admissible := ConformingCompiler
    callContract := fun f args Q =>
      NormativeStdlibPre f args ∧ ∀ ret, NormativeStdlibPost f args ret → Q ret
    callMono := fun _ _ _ _ hImp hPair =>
      And.intro hPair.1 (fun ret hRet => hImp ret (hPair.2 ret hRet)) }

/-- **Pinned Compiler Profile (`π_pinned(c)`):** Restricts verification to a single compiler `c`
    and unfolds `c`'s concrete `.rmeta` stdlib implementation directly. -/
def PinnedCompilerProfile (c : CompilerChoice) : SemProfile :=
  { admissible := fun c' => c' = c
    callContract := fun f args Q => SafeFor (c.coreBody f args) Q
    callMono := fun _ _ _ _ hImp hSafe => safeFor_mono hSafe hImp }

/-- Every conforming compiler's pinned profile refines `NormativeEnvelope`:
    `NormativeEnvelope ⊑ PinnedCompilerProfile c`. -/
theorem normative_refines_pinned (c : CompilerChoice) (hConf : ConformingCompiler c) :
    RefinesProfile NormativeEnvelope (PinnedCompilerProfile c) :=
  And.intro
    (fun _ hEq => Eq.rec (motive := fun x _ => ConformingCompiler x) hConf hEq.symm)
    (fun f args _ hContract =>
      safeFor_mono (hConf.2.2.2.2.2 f args hContract.1) hContract.2)

/-- Refinement is strictly one-way: a pinned compiler profile does not refine `NormativeEnvelope`. -/
theorem pinned_does_not_refine_normative :
    ¬ RefinesProfile (PinnedCompilerProfile rustc_1_96) NormativeEnvelope := by
  intro hRef
  have hEq : rustc_1_100_rand = rustc_1_96 := hRef.1 rustc_1_100_rand rustc_1_100_rand_conforming
  have hField : rustc_1_100_rand.boxUsesBoxRaw = rustc_1_96.boxUsesBoxRaw :=
    congrArg CompilerChoice.boxUsesBoxRaw hEq
  exact nomatch hField

/-!
## Section 3: Executable CFG-MIR Language, Operational Semantics, and Total WP Reducer
-/

abbrev LocalId := Nat
abbrev BlockId := Nat
abbrev Store := LocalId → Nat

def updateStore (s : Store) (dst : LocalId) (val : Nat) : Store :=
  fun l =>
    match Nat.beq l dst with
    | true => val
    | false => s l

/-- MIR pure expressions (covering arithmetic, Category-A constants, and Category-B queries). -/
inductive Expr where
  | constNat : Nat → Expr
  | local : LocalId → Expr
  | add : Expr → Expr → Expr
  | eqNat : Expr → Expr → Expr
  | reprCScalarOff : Expr
  | reprRustFieldAOff : Expr
  | reprRustStructSize : Expr
  | infallibleEqNeverFlag : Expr
  | boxPrivateUsesBoxRawFlag : Expr
  | atomicUsesGenericFlag : Expr
  | deriveDebugConcatFlag : Expr
  deriving DecidableEq

def evalExpr (c : CompilerChoice) (s : Store) : Expr → Nat
  | .constNat n => n
  | .local l => s l
  | .add e1 e2 => evalExpr c s e1 + evalExpr c s e2
  | .eqNat e1 e2 =>
    match Nat.beq (evalExpr c s e1) (evalExpr c s e2) with
    | true => 1
    | false => 0
  | .reprCScalarOff => c.reprCScalarOffset
  | .reprRustFieldAOff => c.reprRustFieldAOff
  | .reprRustStructSize => c.reprRustStructSize
  | .infallibleEqNeverFlag =>
    match c.infallibleEqNever with
    | true => 1
    | false => 0
  | .boxPrivateUsesBoxRawFlag =>
    match c.boxUsesBoxRaw with
    | true => 1
    | false => 0
  | .atomicUsesGenericFlag =>
    match c.atomicUsesGenericWrapper with
    | true => 1
    | false => 0
  | .deriveDebugConcatFlag =>
    match c.deriveDebugConcatStrings with
    | true => 1
    | false => 0

/-- Intra-block MIR statements. -/
inductive Stmt where
  | assign : LocalId → Expr → Stmt
  | nopRetag : Stmt
  | assertNonZero : Expr → Stmt
  deriving DecidableEq

/-- Block terminators (including external stdlib calls). -/
inductive Terminator where
  | returnLocal : LocalId → Terminator
  | goto : BlockId → Terminator
  | switchZero : Expr → BlockId → BlockId → Terminator
  | callStdlib : StdlibFn → List Expr → LocalId → BlockId → Terminator
  deriving DecidableEq

structure BasicBlock where
  stmts : List Stmt
  term : Terminator
  deriving DecidableEq

structure MirBody where
  entry : BlockId
  blocks : List (BlockId × BasicBlock)
  deriving DecidableEq

def lookupBlock : List (BlockId × BasicBlock) → BlockId → Option BasicBlock
  | .nil, _ => none
  | (id, bb) :: rest, bid =>
    match Nat.beq id bid with
    | true => some bb
    | false => lookupBlock rest bid

def execStmts (c : CompilerChoice) (s : Store) : List Stmt → Option Store
  | .nil => some s
  | (.assign dst rhs) :: rest => execStmts c (updateStore s dst (evalExpr c s rhs)) rest
  | .nopRetag :: rest => execStmts c s rest
  | (.assertNonZero cond) :: rest =>
    match Nat.beq (evalExpr c s cond) 0 with
    | true => none
    | false => execStmts c s rest

def evalArgs (c : CompilerChoice) (s : Store) : List Expr → List Nat
  | .nil => .nil
  | e :: es => evalExpr c s e :: evalArgs c s es

/-- Step-indexed operational execution of `MirBody` under concrete compiler `c`. -/
def execBlock : Nat → CompilerChoice → MirBody → BlockId → Store → Outcome Nat
  | 0, _, _, _, _ => .diverge
  | fuel' + 1, c, body, bid, s =>
    match lookupBlock body.blocks bid with
    | none => .ub
    | some bb =>
      match execStmts c s bb.stmts with
      | none => .ub
      | some s' =>
        match bb.term with
        | .returnLocal src => .ok (s' src)
        | .goto next => execBlock fuel' c body next s'
        | .switchZero discr zeroTgt nonZeroTgt =>
          match Nat.beq (evalExpr c s' discr) 0 with
          | true => execBlock fuel' c body zeroTgt s'
          | false => execBlock fuel' c body nonZeroTgt s'
        | .callStdlib callee args dst next =>
          match c.coreBody callee (evalArgs c s' args) with
          | .ok retVal => execBlock fuel' c body next (updateStore s' dst retVal)
          | .ub => .ub
          | .diverge => .diverge

def execMir (fuel : Nat) (c : CompilerChoice) (body : MirBody) (s : Store) : Outcome Nat :=
  execBlock fuel c body body.entry s

/-- Total weakest-precondition transformer for statement lists. -/
def wpStmts (c : CompilerChoice) (s : Store) : List Stmt → (Store → Prop) → Prop
  | .nil, k => k s
  | (.assign dst rhs) :: rest, k => wpStmts c (updateStore s dst (evalExpr c s rhs)) rest k
  | .nopRetag :: rest, k => wpStmts c s rest k
  | (.assertNonZero cond) :: rest, k =>
    evalExpr c s cond ≠ 0 ∧ wpStmts c s rest k

/-- Total weakest-precondition reducer across `MirBody` blocks, using `P.callContract` as the
    opaque seam at every `callStdlib` terminator. -/
def wpBlock : Nat → SemProfile → CompilerChoice → MirBody → BlockId → Store → (Nat → Prop) → Prop
  | 0, _, _, _, _, _, _ => True
  | fuel' + 1, P, c, body, bid, s, post =>
    match lookupBlock body.blocks bid with
    | none => False
    | some bb =>
      wpStmts c s bb.stmts (fun s' =>
        match bb.term with
        | .returnLocal src => post (s' src)
        | .goto next => wpBlock fuel' P c body next s' post
        | .switchZero discr zeroTgt nonZeroTgt =>
          (evalExpr c s' discr = 0 → wpBlock fuel' P c body zeroTgt s' post) ∧
          (evalExpr c s' discr ≠ 0 → wpBlock fuel' P c body nonZeroTgt s' post)
        | .callStdlib callee args dst next =>
          P.callContract callee (evalArgs c s' args) (fun retVal =>
            wpBlock fuel' P c body next (updateStore s' dst retVal) post))

/-- Top-level WP verification condition under profile `P`. -/
def evalWP (fuel : Nat) (P : SemProfile) (body : MirBody) (Q : Store → Nat → Prop) : Prop :=
  ∀ (c : CompilerChoice), P.admissible c →
    ∀ (s : Store), wpBlock fuel P c body body.entry s (Q s)

def OptStoreHolds (res : Option Store) (k : Store → Prop) : Prop :=
  match res with
  | none => False
  | some s' => k s'

theorem wpStmts_sound (c : CompilerChoice) :
    ∀ (stmts : List Stmt) (s : Store) (k : Store → Prop),
      wpStmts c s stmts k → OptStoreHolds (execStmts c s stmts) k
  | .nil, _, _, hWp => hWp
  | (.assign dst rhs) :: rest, s, k, hWp =>
    wpStmts_sound c rest (updateStore s dst (evalExpr c s rhs)) k hWp
  | .nopRetag :: rest, s, k, hWp =>
    wpStmts_sound c rest s k hWp
  | (.assertNonZero cond) :: rest, s, k, hWp => by
    change OptStoreHolds
      (match Nat.beq (evalExpr c s cond) 0 with
       | true => none
       | false => execStmts c s rest) k
    cases hEq : Nat.beq (evalExpr c s cond) 0 with
    | false => exact wpStmts_sound c rest s k hWp.2
    | true => exact False.elim (hWp.1 (nat_eq_of_beq_eq_true hEq))

theorem wpStmts_mono (c : CompilerChoice) :
    ∀ (stmts : List Stmt) (s : Store) (k1 k2 : Store → Prop),
      (∀ s', k1 s' → k2 s') → wpStmts c s stmts k1 → wpStmts c s stmts k2
  | .nil, s, _, _, hImp, hWp => hImp s hWp
  | (.assign dst rhs) :: rest, s, k1, k2, hImp, hWp =>
    wpStmts_mono c rest (updateStore s dst (evalExpr c s rhs)) k1 k2 hImp hWp
  | .nopRetag :: rest, s, k1, k2, hImp, hWp =>
    wpStmts_mono c rest s k1 k2 hImp hWp
  | (.assertNonZero _) :: rest, s, k1, k2, hImp, hWp =>
    And.intro hWp.1 (wpStmts_mono c rest s k1 k2 hImp hWp.2)

theorem wpCallResult_sound (fuel' : Nat) (P : SemProfile) (c : CompilerChoice)
    (body : MirBody) (dst : LocalId) (next : BlockId) (s' : Store) (post : Nat → Prop)
    (ih : ∀ (bid : BlockId) (st : Store),
      wpBlock fuel' P c body bid st post → SafeFor (execBlock fuel' c body bid st) post) :
    ∀ (out : Outcome Nat),
      SafeFor out (fun retVal => wpBlock fuel' P c body next (updateStore s' dst retVal) post) →
      SafeFor
        (match out with
         | .ok retVal => execBlock fuel' c body next (updateStore s' dst retVal)
         | .ub => .ub
         | .diverge => .diverge)
        post
  | .ok retVal, hOk => ih next (updateStore s' dst retVal) hOk
  | .ub, hFalse => False.elim hFalse
  | .diverge, _ => True.intro

theorem wpSwitch_sound (fuel' : Nat) (P : SemProfile) (c : CompilerChoice)
    (body : MirBody) (val : Nat) (zeroTgt nonZeroTgt : BlockId) (s' : Store) (post : Nat → Prop)
    (ih : ∀ (bid : BlockId) (st : Store),
      wpBlock fuel' P c body bid st post → SafeFor (execBlock fuel' c body bid st) post)
    (hSw : (val = 0 → wpBlock fuel' P c body zeroTgt s' post) ∧
           (val ≠ 0 → wpBlock fuel' P c body nonZeroTgt s' post)) :
    SafeFor
      (match Nat.beq val 0 with
       | true => execBlock fuel' c body zeroTgt s'
       | false => execBlock fuel' c body nonZeroTgt s')
      post := by
  cases hBeq : Nat.beq val 0 with
  | true =>
    exact ih zeroTgt s' (hSw.1 (nat_eq_of_beq_eq_true hBeq))
  | false =>
    apply ih nonZeroTgt s'
    apply hSw.2
    intro hZero
    rw [hZero] at hBeq
    exact nomatch hBeq

theorem wpTerm_sound (fuel' : Nat) (P : SemProfile) (c : CompilerChoice)
    (hCalls : ∀ f args post, P.callContract f args post → SafeFor (c.coreBody f args) post)
    (body : MirBody) (s' : Store) (post : Nat → Prop)
    (ih : ∀ (bid : BlockId) (st : Store),
      wpBlock fuel' P c body bid st post → SafeFor (execBlock fuel' c body bid st) post) :
    ∀ (term : Terminator),
      (match term with
       | .returnLocal src => post (s' src)
       | .goto next => wpBlock fuel' P c body next s' post
       | .switchZero discr zeroTgt nonZeroTgt =>
         (evalExpr c s' discr = 0 → wpBlock fuel' P c body zeroTgt s' post) ∧
         (evalExpr c s' discr ≠ 0 → wpBlock fuel' P c body nonZeroTgt s' post)
       | .callStdlib callee args dst next =>
         P.callContract callee (evalArgs c s' args) (fun retVal =>
           wpBlock fuel' P c body next (updateStore s' dst retVal) post)) →
      SafeFor
        (match term with
         | .returnLocal src => .ok (s' src)
         | .goto next => execBlock fuel' c body next s'
         | .switchZero discr zeroTgt nonZeroTgt =>
           match Nat.beq (evalExpr c s' discr) 0 with
           | true => execBlock fuel' c body zeroTgt s'
           | false => execBlock fuel' c body nonZeroTgt s'
         | .callStdlib callee args dst next =>
           match c.coreBody callee (evalArgs c s' args) with
           | .ok retVal => execBlock fuel' c body next (updateStore s' dst retVal)
           | .ub => .ub
           | .diverge => .diverge)
        post
  | .returnLocal _, hRet => hRet
  | .goto next, hNext => ih next s' hNext
  | .switchZero discr zeroTgt nonZeroTgt, hSw =>
    wpSwitch_sound fuel' P c body (evalExpr c s' discr) zeroTgt nonZeroTgt s' post ih hSw
  | .callStdlib callee args dst next, hCallWp =>
    wpCallResult_sound fuel' P c body dst next s' post ih
      (c.coreBody callee (evalArgs c s' args))
      (hCalls callee (evalArgs c s' args) _ hCallWp)

theorem wpOptStore_sound (fuel' : Nat) (P : SemProfile) (c : CompilerChoice)
    (hCalls : ∀ f args post, P.callContract f args post → SafeFor (c.coreBody f args) post)
    (body : MirBody) (term : Terminator) (post : Nat → Prop)
    (ih : ∀ (bid : BlockId) (st : Store),
      wpBlock fuel' P c body bid st post → SafeFor (execBlock fuel' c body bid st) post) :
    ∀ (optS : Option Store),
      OptStoreHolds optS (fun s' =>
        match term with
        | .returnLocal src => post (s' src)
        | .goto next => wpBlock fuel' P c body next s' post
        | .switchZero discr zeroTgt nonZeroTgt =>
          (evalExpr c s' discr = 0 → wpBlock fuel' P c body zeroTgt s' post) ∧
          (evalExpr c s' discr ≠ 0 → wpBlock fuel' P c body nonZeroTgt s' post)
        | .callStdlib callee args dst next =>
          P.callContract callee (evalArgs c s' args) (fun retVal =>
            wpBlock fuel' P c body next (updateStore s' dst retVal) post)) →
      SafeFor
        (match optS with
         | none => .ub
         | some s' =>
           match term with
           | .returnLocal src => .ok (s' src)
           | .goto next => execBlock fuel' c body next s'
           | .switchZero discr zeroTgt nonZeroTgt =>
             match Nat.beq (evalExpr c s' discr) 0 with
             | true => execBlock fuel' c body zeroTgt s'
             | false => execBlock fuel' c body nonZeroTgt s'
           | .callStdlib callee args dst next =>
             match c.coreBody callee (evalArgs c s' args) with
             | .ok retVal => execBlock fuel' c body next (updateStore s' dst retVal)
             | .ub => .ub
             | .diverge => .diverge)
        post
  | none, hFalse => False.elim hFalse
  | some s', hSt => wpTerm_sound fuel' P c hCalls body s' post ih term hSt

theorem wpOptBlock_sound (fuel' : Nat) (P : SemProfile) (c : CompilerChoice)
    (hCalls : ∀ f args post, P.callContract f args post → SafeFor (c.coreBody f args) post)
    (body : MirBody) (s : Store) (post : Nat → Prop)
    (ih : ∀ (bid : BlockId) (st : Store),
      wpBlock fuel' P c body bid st post → SafeFor (execBlock fuel' c body bid st) post) :
    ∀ (optBb : Option BasicBlock),
      (match optBb with
       | none => False
       | some bb =>
         wpStmts c s bb.stmts (fun s' =>
           match bb.term with
           | .returnLocal src => post (s' src)
           | .goto next => wpBlock fuel' P c body next s' post
           | .switchZero discr zeroTgt nonZeroTgt =>
             (evalExpr c s' discr = 0 → wpBlock fuel' P c body zeroTgt s' post) ∧
             (evalExpr c s' discr ≠ 0 → wpBlock fuel' P c body nonZeroTgt s' post)
           | .callStdlib callee args dst next =>
             P.callContract callee (evalArgs c s' args) (fun retVal =>
               wpBlock fuel' P c body next (updateStore s' dst retVal) post))) →
      SafeFor
        (match optBb with
         | none => .ub
         | some bb =>
           match execStmts c s bb.stmts with
           | none => .ub
           | some s' =>
             match bb.term with
             | .returnLocal src => .ok (s' src)
             | .goto next => execBlock fuel' c body next s'
             | .switchZero discr zeroTgt nonZeroTgt =>
               match Nat.beq (evalExpr c s' discr) 0 with
               | true => execBlock fuel' c body zeroTgt s'
               | false => execBlock fuel' c body nonZeroTgt s'
             | .callStdlib callee args dst next =>
               match c.coreBody callee (evalArgs c s' args) with
               | .ok retVal => execBlock fuel' c body next (updateStore s' dst retVal)
               | .ub => .ub
               | .diverge => .diverge)
        post
  | none, hFalse => False.elim hFalse
  | some bb, hWpBb =>
    wpOptStore_sound fuel' P c hCalls body bb.term post ih
      (execStmts c s bb.stmts)
      (wpStmts_sound c bb.stmts s _ hWpBb)

/-- Operational soundness of `wpBlock` relative to `execBlock`. -/
theorem wpBlock_sound :
    ∀ (fuel : Nat) (P : SemProfile) (c : CompilerChoice),
    (∀ f args post, P.callContract f args post → SafeFor (c.coreBody f args) post) →
    ∀ (body : MirBody) (bid : BlockId) (s : Store) (post : Nat → Prop),
    wpBlock fuel P c body bid s post →
    SafeFor (execBlock fuel c body bid s) post
  | 0, _, _, _, _, _, _, _, _ => True.intro
  | fuel' + 1, P, c, hCalls, body, bid, s, post, hWp =>
    wpOptBlock_sound fuel' P c hCalls body s post
      (fun b st h => wpBlock_sound fuel' P c hCalls body b st post h)
      (lookupBlock body.blocks bid)
      hWp

/-- Monotonicity of `wpBlock` along profile refinement `RefinesProfile P_abs P_conc`. -/
theorem wpBlock_mono_profile :
    ∀ (fuel : Nat) (P_abs P_conc : SemProfile),
    RefinesProfile P_abs P_conc → ∀ (c : CompilerChoice) (body : MirBody)
    (bid : BlockId) (s : Store) (post : Nat → Prop),
    wpBlock fuel P_abs c body bid s post →
    wpBlock fuel P_conc c body bid s post
  | 0, _, _, _, _, _, _, _, _, _ => True.intro
  | fuel' + 1, P_abs, P_conc, hRef, c, body, bid, s, post, hWp => by
    unfold wpBlock at hWp
    unfold wpBlock
    cases hBlk : lookupBlock body.blocks bid with
    | none =>
      rw [hBlk] at hWp
      exact False.elim hWp
    | some bb =>
      rw [hBlk] at hWp
      exact wpStmts_mono c bb.stmts s _ _
        (fun s' hTermWp =>
          match bb.term, hTermWp with
          | .returnLocal _, h => h
          | .goto next, h =>
            wpBlock_mono_profile fuel' P_abs P_conc hRef c body next s' post h
          | .switchZero _ zeroTgt nonZeroTgt, h =>
            And.intro
              (fun h0 => wpBlock_mono_profile fuel' P_abs P_conc hRef c body zeroTgt s' post (h.1 h0))
              (fun hN => wpBlock_mono_profile fuel' P_abs P_conc hRef c body nonZeroTgt s' post (h.2 hN))
          | .callStdlib callee args dst next, h =>
            hRef.2 callee (evalArgs c s' args) _
              (P_abs.callMono callee (evalArgs c s' args) _ _
                (fun retVal hNext =>
                  wpBlock_mono_profile fuel' P_abs P_conc hRef c body next
                    (updateStore s' dst retVal) post hNext)
                h))
        hWp

/-- Monotonicity of `evalWP` along profile refinement `RefinesProfile P_abs P_conc`. -/
theorem evalWP_mono_profile (fuel : Nat) {P_abs P_conc : SemProfile}
    (hRef : RefinesProfile P_abs P_conc) (body : MirBody) (Q : Store → Nat → Prop)
    (hWp : evalWP fuel P_abs body Q) :
    evalWP fuel P_conc body Q :=
  fun c hAdm s =>
    wpBlock_mono_profile fuel P_abs P_conc hRef c body body.entry s (Q s) (hWp c (hRef.1 c hAdm) s)

/-!
## Section 4: Theorems 1 & 2 — Envelope Transfer & Non-Normative Layout/Reflection Countersample
-/

/-- Explicit TCB audit-log entry for any non-normative compiler assumption (`zerocopy/POLICIES.md`
    scoped exception or compiler-pinned layout/behavior waiver). -/
structure NonNormativeWaiver where
  label : Nat
  assumedProp : CompilerChoice → Prop

/-- All waivers in `waivers` hold for compiler `c`. -/
def SatisfiesWaivers (c : CompilerChoice) : List NonNormativeWaiver → Prop
  | .nil => True
  | w :: ws => w.assumedProp c ∧ SatisfiesWaivers c ws

/-- Profile induced by augmenting `NormativeEnvelope` with explicit TCB waivers `waivers`. -/
def ProfileWithWaivers (waivers : List NonNormativeWaiver) : SemProfile :=
  { admissible := fun c => ConformingCompiler c ∧ SatisfiesWaivers c waivers
    callContract := NormativeEnvelope.callContract
    callMono := NormativeEnvelope.callMono }

theorem zero_waivers_refines_normative :
    RefinesProfile (ProfileWithWaivers .nil) NormativeEnvelope :=
  And.intro (fun _ hc => And.intro hc True.intro) (fun _ _ _ h => h)

/-- Audited verification judgment carrying explicit `waivers`. -/
def VerifiedWithWaivers (waivers : List NonNormativeWaiver) (fuel : Nat)
    (body : MirBody) (Q : Store → Nat → Prop) : Prop :=
  evalWP fuel (ProfileWithWaivers waivers) body Q

/-- **Theorem 1 (`forwards_compatible_envelope_transfer`):**
    Monotonic envelope refinement (`NormativeEnvelope ⊑ PinnedCompilerProfile c`) transfers any
    zero-waiver proof under `NormativeEnvelope` to `PinnedCompilerProfile c` and guarantees
    UB-free runtime execution satisfying `Q` on every conforming compiler `c`, without claiming
    soundness over non-conforming compilers outside `ConformingCompiler`. -/
theorem forwards_compatible_envelope_transfer
    (fuel : Nat)
    (body : MirBody)
    (Q : Store → Nat → Prop)
    (hVerif : VerifiedWithWaivers .nil fuel body Q)
    (c : CompilerChoice)
    (hConf : ConformingCompiler c) :
    RefinesProfile NormativeEnvelope (PinnedCompilerProfile c) ∧
    evalWP fuel (PinnedCompilerProfile c) body Q ∧
    (∀ s : Store, SafeFor (execMir fuel c body s) (Q s)) :=
  let hNorm : evalWP fuel NormativeEnvelope body Q :=
    evalWP_mono_profile fuel zero_waivers_refines_normative body Q hVerif
  let hRef : RefinesProfile NormativeEnvelope (PinnedCompilerProfile c) :=
    normative_refines_pinned c hConf
  let hPinned : evalWP fuel (PinnedCompilerProfile c) body Q :=
    evalWP_mono_profile fuel hRef body Q hNorm
  And.intro hRef
    (And.intro hPinned (fun s =>
      wpBlock_sound fuel (PinnedCompilerProfile c) c (fun _ _ _ h => h)
        body body.entry s (Q s) (hPinned c rfl s)))

/-- Alias preserving compatibility with downstream proof callers. -/
theorem normative_proof_transfers_to_all_conforming_compilers
    (fuel : Nat)
    (body : MirBody)
    (Q : Store → Nat → Prop)
    (hVerif : VerifiedWithWaivers .nil fuel body Q)
    (c : CompilerChoice)
    (hConf : ConformingCompiler c) :
    evalWP fuel (PinnedCompilerProfile c) body Q ∧
    (∀ s : Store, SafeFor (execMir fuel c body s) (Q s)) :=
  (forwards_compatible_envelope_transfer fuel body Q hVerif c hConf).2

/-- Program inspecting `#[repr(Rust)]` field offset (`reprRustFieldAOff == 0`), `TypeId`
    (`infallibleEqNeverFlag == 0`), and `Box` private field (`boxPrivateUsesBoxRawFlag == 0`). -/
def nonNormativeProbeBody : MirBody :=
  { entry := 0
    blocks :=
      (0, { stmts := .assertNonZero (.eqNat .reprRustFieldAOff (.constNat 0)) ::
                     .assertNonZero (.eqNat .infallibleEqNeverFlag (.constNat 0)) ::
                     .assertNonZero (.eqNat .boxPrivateUsesBoxRawFlag (.constNat 0)) ::
                     .assign 0 (.constNat 1) :: .nil
            term := .returnLocal 0 }) :: .nil }

/-- **Theorem 2 (`non_normative_layout_countersample`):**
    When a program or specification relies on `#[repr(Rust)]` field offsets, `TypeId`/`type_name`
    of `Infallible` vs. `!`, or stdlib private fields (`Unique<T>` vs. `BoxRaw<T>`), verification
    under `PinnedCompilerProfile rustc_1_96` succeeds (`SafeFor ... = .ok 1`), yet execution on
    conforming compiler `rustc_1_100_rand` triggers `.ub` and `VerifiedWithWaivers .nil` is
    provably refutable. -/
theorem non_normative_layout_countersample (s0 : Store) :
    evalWP 2 (PinnedCompilerProfile rustc_1_96) nonNormativeProbeBody (fun _ ret => ret = 1) ∧
    SafeFor (execMir 2 rustc_1_96 nonNormativeProbeBody s0) (fun ret => ret = 1) ∧
    execMir 2 rustc_1_100_rand nonNormativeProbeBody s0 = .ub ∧
    ¬ VerifiedWithWaivers .nil 2 nonNormativeProbeBody (fun _ ret => ret = 1) :=
  And.intro
    (by
      intro c hEq s
      change c = rustc_1_96 at hEq
      subst hEq
      exact And.intro (fun h => nomatch h)
        (And.intro (fun h => nomatch h)
          (And.intro (fun h => nomatch h) rfl)))
    (And.intro rfl
      (And.intro rfl
        (fun hVerif =>
          let hSafe := (forwards_compatible_envelope_transfer
            2 nonNormativeProbeBody (fun _ ret => ret = 1)
            hVerif rustc_1_100_rand rustc_1_100_rand_conforming).2.2 s0
          hSafe)))

/-!
## Section 5: Theorems 3 & 4 — Trunk Constructor Addition & Orthogonal `SemProfile` Flag Invariance
-/

/-- Superset trunk statement IR extending `Stmt` with arbitrary future compiler statement
    constructors `evalExt (ext : Ext)` (e.g., new borrow-checker hints or intrinsics). -/
inductive TrunkStmt (Ext : Type) where
  | assign : LocalId → Expr → TrunkStmt Ext
  | nopRetag : TrunkStmt Ext
  | assertNonZero : Expr → TrunkStmt Ext
  | evalExt : Ext → TrunkStmt Ext
  deriving DecidableEq

/-- Canonical injection of existing `Stmt` programs into the extended `TrunkStmt Ext` AST. -/
def liftStmtToTrunk {Ext : Type} : Stmt → TrunkStmt Ext
  | .assign dst rhs => .assign dst rhs
  | .nopRetag => .nopRetag
  | .assertNonZero cond => .assertNonZero cond

def liftStmtsToTrunk {Ext : Type} : List Stmt → List (TrunkStmt Ext)
  | .nil => .nil
  | st :: rest => liftStmtToTrunk st :: liftStmtsToTrunk rest

/-- Extended WP transformer parameterized by any future semantics `wpExt` for `.evalExt`. -/
def wpTrunkStmts {Ext : Type}
    (wpExt : CompilerChoice → Store → Ext → (Store → Prop) → Prop)
    (c : CompilerChoice) (s : Store) : List (TrunkStmt Ext) → (Store → Prop) → Prop
  | .nil, k => k s
  | (.assign dst rhs) :: rest, k =>
    wpTrunkStmts wpExt c (updateStore s dst (evalExpr c s rhs)) rest k
  | .nopRetag :: rest, k =>
    wpTrunkStmts wpExt c s rest k
  | (.assertNonZero cond) :: rest, k =>
    evalExpr c s cond ≠ 0 ∧ wpTrunkStmts wpExt c s rest k
  | (.evalExt ext) :: rest, k =>
    wpExt c s ext (fun s' => wpTrunkStmts wpExt c s' rest k)

/-- **Theorem 3 (`trunk_addition_preserves_existing_wp`):**
    Adding new `TrunkStmt.evalExt` constructors (with arbitrary semantics `wpExt`) preserves
    `wpStmts` identically across all existing `List Stmt` programs—and on concrete statement
    lists reduces definitionally by Lean 4 kernel β/ι reduction without touching `wpExt`. -/
theorem trunk_addition_preserves_existing_wp {Ext : Type}
    (wpExt : CompilerChoice → Store → Ext → (Store → Prop) → Prop)
    (c : CompilerChoice) :
    ∀ (stmts : List Stmt) (s : Store) (k : Store → Prop),
      wpTrunkStmts wpExt c s (liftStmtsToTrunk stmts) k ↔ wpStmts c s stmts k
  | .nil, _, _ => Iff.intro (fun h => h) (fun h => h)
  | (.assign dst rhs) :: rest, s, k =>
    trunk_addition_preserves_existing_wp wpExt c rest (updateStore s dst (evalExpr c s rhs)) k
  | .nopRetag :: rest, s, k =>
    trunk_addition_preserves_existing_wp wpExt c rest s k
  | (.assertNonZero _) :: rest, s, k =>
    let ih := trunk_addition_preserves_existing_wp wpExt c rest s k
    Iff.intro
      (fun h => And.intro h.1 (ih.mp h.2))
      (fun h => And.intro h.1 (ih.mpr h.2))

/-- Extended semantic profile carrying an orthogonal capability flag `extraFlag : Bool`
    (e.g., modeling a newly introduced MIR capability such as union padding reset or
    `Call` destination-before-args order) that restricts or splits `ExtendedCompilerChoice`
    without altering `MirBody` constructs that do not read `extraFlag`. -/
structure ExtendedCompilerChoice where
  base : CompilerChoice
  extraCapFlag : Bool

def evalWPWithOrthogonalFlag (flagRequirement : Option Bool)
    (fuel : Nat) (body : MirBody) (Q : Store → Nat → Prop) : Prop :=
  ∀ (ec : ExtendedCompilerChoice),
    ConformingCompiler ec.base →
    (match flagRequirement with
     | none => True
     | some req => ec.extraCapFlag = req) →
    ∀ (s : Store), wpBlock fuel NormativeEnvelope ec.base body body.entry s (Q s)

/-- **Theorem 4 (`profile_flag_preserves_unaffected_wp`):**
    Adding an orthogonal `SemProfile` capability flag (`extraCapFlag : Bool`) preserves all
    existing normative `evalWP` proofs: any proof `hBase : evalWP fuel NormativeEnvelope body Q`
    validates every flag specialization (`none`, `some false`, `some true`), and conversely an
    unconstrained flag envelope (`none`) is logically equivalent to `evalWP fuel NormativeEnvelope`. -/
theorem profile_flag_preserves_unaffected_wp
    (fuel : Nat) (body : MirBody) (Q : Store → Nat → Prop) :
    (evalWP fuel NormativeEnvelope body Q ↔ evalWPWithOrthogonalFlag none fuel body Q) ∧
    (evalWP fuel NormativeEnvelope body Q →
      evalWPWithOrthogonalFlag (some false) fuel body Q ∧
      evalWPWithOrthogonalFlag (some true) fuel body Q) :=
  And.intro
    (Iff.intro
      (fun hBase ec hConf _ s => hBase ec.base hConf s)
      (fun hExt c hConf s =>
        hExt { base := c, extraCapFlag := false } hConf True.intro s))
    (fun hBase =>
      And.intro
        (fun ec hConf _ s => hBase ec.base hConf s)
        (fun ec hConf _ s => hBase ec.base hConf s))

/-!
## Section 6: Theorems 5 & 6 — Stdlib Internal Drift vs. Opaque Normative Contracts
-/

/-- Caller invoking `Box::new`+`Deref`, `AtomicUsize::load`, and `slice::get_unchecked` purely
    through opaque normative contracts (`CallsSatisfyNormativeSpec`). -/
def opaqueStdlibSuiteCaller : MirBody :=
  { entry := 0
    blocks :=
      (0, { stmts := .nil
            term := .callStdlib .boxNewAndDeref (.local 1 :: .nil) 2 1 }) ::
      (1, { stmts := .nil
            term := .callStdlib .atomicLoadUsize (.local 2 :: .constNat 1 :: .nil) 3 2 }) ::
      (2, { stmts := .nil
            term := .callStdlib .sliceGetUnchecked
                      (.local 3 :: .constNat 4 :: .constNat 0 :: .nil) 0 3 }) ::
      (3, { stmts := .nil
            term := .returnLocal 0 }) :: .nil }

/-- Caller inlining `rustc 1.94`-era stdlib private representations directly (`Box.0: Unique<T>`,
    nominal `AtomicUsize`, legacy `#[derive(Debug)]` string layout). -/
def inlinedStdlibPrivateCaller : MirBody :=
  { entry := 0
    blocks :=
      (0, { stmts := .assertNonZero (.eqNat .boxPrivateUsesBoxRawFlag (.constNat 0)) ::
                     .assertNonZero (.eqNat .atomicUsesGenericFlag (.constNat 0)) ::
                     .assertNonZero (.eqNat .deriveDebugConcatFlag (.constNat 0)) ::
                     .assign 0 (.local 1) :: .nil
            term := .returnLocal 0 }) :: .nil }

/-- Single-call `Box` contrast witnesses. -/
def opaqueBoxCaller : MirBody :=
  { entry := 0
    blocks :=
      (0, { stmts := .nil
            term := .callStdlib .boxNewAndDeref (.local 1 :: .nil) 0 1 }) ::
      (1, { stmts := .nil
            term := .returnLocal 0 }) :: .nil }

def inlinedUniqueBoxCaller : MirBody :=
  { entry := 0
    blocks :=
      (0, { stmts := .assertNonZero (.eqNat .boxPrivateUsesBoxRawFlag (.constNat 0)) ::
                     .assign 0 (.local 1) :: .nil
            term := .returnLocal 0 }) :: .nil }

theorem opaque_box_caller_verified_normatively :
    VerifiedWithWaivers .nil 3 opaqueBoxCaller (fun s ret => ret = s 1) :=
  fun _ _ _ => And.intro True.intro (fun _ hPost => hPost)

/-- **Theorem 5 (`callee_impl_drift_breaks_inlined_body`):**
    Unfolding `core`/`alloc` `.rmeta` MIR bodies (`Unique<T> -> BoxRaw<T>`,
    `AtomicU* -> Atomic<T>`, `#[derive(Debug)]` field-string concatenation) couples caller
    verification to compiler-internal private representations: `inlinedStdlibPrivateCaller`
    succeeds on `rustc_1_96` yet fails with `.ub` (and breaks `PinnedCompilerProfile`) on
    `rustc_1_100_rand`. -/
theorem callee_impl_drift_breaks_inlined_body (s : Store) :
    SafeFor (execMir 2 rustc_1_96 inlinedStdlibPrivateCaller s) (fun ret => ret = s 1) ∧
    execMir 2 rustc_1_100_rand inlinedStdlibPrivateCaller s = .ub ∧
    ¬ evalWP 2 (PinnedCompilerProfile rustc_1_100_rand)
        inlinedStdlibPrivateCaller (fun st ret => ret = st 1) :=
  And.intro rfl
    (And.intro rfl
      (fun hWp =>
        let hSafe := wpBlock_sound 2 (PinnedCompilerProfile rustc_1_100_rand) rustc_1_100_rand
          (fun _ _ _ h => h) inlinedStdlibPrivateCaller 0 s (fun ret => ret = s 1)
          (hWp rustc_1_100_rand rfl s)
        hSafe))

/-- **Theorem 6 (`opaque_normative_contract_absorbs_stdlib_drift`):**
    Verifying external calls against opaque Category-A contracts (`CallsSatisfyNormativeSpec`)
    completely insulates user proofs from `Unique<T> -> BoxRaw<T>`, `AtomicU* -> Atomic<T>`, and
    `#[derive(Debug)]` internal MIR refactors: one proof discharges `opaqueStdlibSuiteCaller` once
    and transfers to every `ConformingCompiler` (including both `rustc_1_96` and `rustc_1_100_rand`). -/
theorem opaque_normative_contract_absorbs_stdlib_drift :
    VerifiedWithWaivers .nil 5 opaqueStdlibSuiteCaller (fun s ret => ret = s 1) ∧
    ∀ (c : CompilerChoice), ConformingCompiler c →
      ∀ (s : Store), SafeFor (execMir 5 c opaqueStdlibSuiteCaller s) (fun ret => ret = s 1) :=
  let hVerif : VerifiedWithWaivers .nil 5 opaqueStdlibSuiteCaller (fun s ret => ret = s 1) :=
    fun _ _ s =>
      And.intro True.intro (fun r1 hr1 =>
        And.intro rfl (fun r2 hr2 =>
          And.intro rfl (fun r3 hr3 => by
            rw [hr3, hr2, hr1]
            exact Nat.add_zero (s 1))))
  And.intro hVerif
    (fun c hConf s =>
      (forwards_compatible_envelope_transfer
        5 opaqueStdlibSuiteCaller (fun st ret => ret = st 1) hVerif c hConf).2.2 s)

theorem inlined_stdlib_mir_breaks_across_boxraw_refactor (s : Store) :
    SafeFor (execMir 3 rustc_1_96 opaqueBoxCaller s) (fun ret => ret = s 1) ∧
    SafeFor (execMir 3 rustc_1_100_rand opaqueBoxCaller s) (fun ret => ret = s 1) ∧
    SafeFor (execMir 2 rustc_1_96 inlinedUniqueBoxCaller s) (fun ret => ret = s 1) ∧
    execMir 2 rustc_1_100_rand inlinedUniqueBoxCaller s = .ub :=
  let h1 := (normative_proof_transfers_to_all_conforming_compilers
    3 opaqueBoxCaller (fun st ret => ret = st 1)
    opaque_box_caller_verified_normatively rustc_1_96 rustc_1_96_conforming).2 s
  let h2 := (normative_proof_transfers_to_all_conforming_compilers
    3 opaqueBoxCaller (fun st ret => ret = st 1)
    opaque_box_caller_verified_normatively rustc_1_100_rand rustc_1_100_rand_conforming).2 s
  And.intro h1 (And.intro h2 (And.intro rfl rfl))

/-!
## Section 7: Proof-Compilation Survival Under Temp Renumbering & CFG Block Splitting
-/

/-- Frontend `c_1` (`rustc 1.96`-style) MIR for `fn add_one_boxed(x: u64) -> u64`:
    Uses 2 blocks (`0 → 1`), dead unit temporary `_17`, intermediate temporary `_18`,
    and return destination `_2`. -/
def mir_c1 : MirBody :=
  { entry := 0
    blocks :=
      (0, { stmts := .assign 17 (.constNat 0) ::
                     .assign 18 (.add (.local 1) .reprCScalarOff) :: .nil
            term := .callStdlib .boxNewAndDeref (.local 18 :: .nil) 2 1 }) ::
      (1, { stmts := .assign 0 (.add (.local 2) (.constNat 1)) :: .nil
            term := .returnLocal 0 }) :: .nil }

/-- Frontend `c_2` (`rustc 1.100`-style) MIR for the exact same Rust source function:
    Elides dead unit local `_17` (never-type `!` fallback cleanup), inserts `nopRetag`
    (`WithRetag::No`), renumbers temporaries (`_18 → _9`, `_2 → _4`), and splits control flow
    across 3 blocks (`0 → 5 → 9`). -/
def mir_c2 : MirBody :=
  { entry := 0
    blocks :=
      (0, { stmts := .nopRetag ::
                     .assign 9 (.add (.local 1) .reprCScalarOff) :: .nil
            term := .goto 5 }) ::
      (5, { stmts := .nopRetag :: .nil
            term := .callStdlib .boxNewAndDeref (.local 9 :: .nil) 4 9 }) ::
      (9, { stmts := .assign 0 (.add (.local 4) (.constNat 1)) :: .nil
            term := .returnLocal 0 }) :: .nil }

theorem mir_c1_ne_mir_c2 : mir_c1 ≠ mir_c2 := by
  intro hEq
  have hBlocks : mir_c1.blocks.length = mir_c2.blocks.length :=
    congrArg (fun m => m.blocks.length) hEq
  exact nomatch hBlocks

def addOneSpec (s : Store) (ret : Nat) : Prop :=
  ret = s 1 + 1

def ReducedAddOneVC : Prop :=
  ∀ (c : CompilerChoice), ConformingCompiler c →
    ∀ (s : Store), True ∧ ∀ (ret : Nat), ret = s 1 + c.reprCScalarOffset → ret + 1 = s 1 + 1

theorem sharedUserProof : ReducedAddOneVC :=
  fun c hConf s =>
    And.intro True.intro (fun ret hRet => by
      rw [hRet, hConf.1])

theorem wp_invariant_under_temp_and_cfg_refactoring :
    mir_c1 ≠ mir_c2 ∧
    (evalWP 4 NormativeEnvelope mir_c1 addOneSpec ↔
     evalWP 4 NormativeEnvelope mir_c2 addOneSpec) ∧
    evalWP 4 NormativeEnvelope mir_c1 addOneSpec ∧
    evalWP 4 NormativeEnvelope mir_c2 addOneSpec :=
  And.intro mir_c1_ne_mir_c2
    (And.intro (Iff.intro (fun h => h) (fun h => h))
      (And.intro sharedUserProof sharedUserProof))

structure RawCfgCert where
  expectedBlocks : List BlockId
  pinnedTempLocal : LocalId
  expectedTempAfterEntry : CompilerChoice → Store → Nat

def memNat (x : Nat) : List Nat → Bool
  | .nil => false
  | y :: ys =>
    match Nat.beq x y with
    | true => true
    | false => memNat x ys

def allBodyBlocksCovered (certBlocks : List BlockId) : List (BlockId × BasicBlock) → Bool
  | .nil => true
  | (bid, _) :: rest =>
    match memNat bid certBlocks with
    | true => allBodyBlocksCovered certBlocks rest
    | false => false

def ValidRawCfgCert (cert : RawCfgCert) (body : MirBody) : Prop :=
  allBodyBlocksCovered cert.expectedBlocks body.blocks = true ∧
  ∀ (c : CompilerChoice) (s : Store),
    ConformingCompiler c →
    OptStoreHolds
      (match lookupBlock body.blocks body.entry with
       | none => none
       | some bb0 => execStmts c s bb0.stmts)
      (fun s' => s' cert.pinnedTempLocal = cert.expectedTempAfterEntry c s)

def certForMirC1 : RawCfgCert :=
  { expectedBlocks := 0 :: 1 :: .nil
    pinnedTempLocal := 18
    expectedTempAfterEntry := fun c s => s 1 + c.reprCScalarOffset }

theorem raw_cfg_cert_breaks_on_block_split :
    ValidRawCfgCert certForMirC1 mir_c1 ∧
    ¬ ValidRawCfgCert certForMirC1 mir_c2 :=
  And.intro
    (And.intro rfl (fun _ _ _ => rfl))
    (fun hValid => nomatch hValid.1)

/-!
## Section 8: Mandatory Two-Route Governance for Non-Normative Dependencies (`zerocopy` Model)
-/

inductive CompileAndExecResult (Val : Type) where
  | compileRejected : CompileAndExecResult Val
  | compiled : Outcome Val → CompileAndExecResult Val
  deriving DecidableEq

def CompileSafeFor {Val : Type} (res : CompileAndExecResult Val) (Q : Val → Prop) : Prop :=
  match res with
  | .compileRejected => True
  | .compiled out => SafeFor out Q

def compileAndExec (constGuard : Option (CompilerChoice → Bool))
    (fuel : Nat) (c : CompilerChoice) (body : MirBody) (s : Store) :
    CompileAndExecResult Nat :=
  match constGuard with
  | some g =>
    match g c with
    | true => .compiled (execMir fuel c body s)
    | false => .compileRejected
  | none =>
    .compiled (execMir fuel c body s)

def GenuinelyDependsOn (P_ext : CompilerChoice → Prop) (fuel : Nat) (body : MirBody) : Prop :=
  Exists (fun c_bad : CompilerChoice =>
    Exists (fun s_bad : Store =>
      ConformingCompiler c_bad ∧
      ¬ P_ext c_bad ∧
      execMir fuel c_bad body s_bad = .ub))

structure AuditedCrateClaim (fuel : Nat) (body : MirBody) (Q : Store → Nat → Prop) where
  constGuard : Option (CompilerChoice → Bool)
  waivers : List NonNormativeWaiver
  soundOnScopedCompilers :
    ∀ (c : CompilerChoice),
      ConformingCompiler c →
      SatisfiesWaivers c waivers →
      ∀ (s : Store), CompileSafeFor (compileAndExec constGuard fuel c body s) (Q s)

theorem non_normative_assumption_logged_or_compile_guarded
    {P_ext : CompilerChoice → Prop}
    {fuel : Nat}
    {body : MirBody}
    {Q : Store → Nat → Prop}
    (hDep : GenuinelyDependsOn P_ext fuel body)
    (claim : AuditedCrateClaim fuel body Q) :
    Exists (fun g : CompilerChoice → Bool =>
      claim.constGuard = some g ∧
      Exists (fun c_bad : CompilerChoice =>
        ConformingCompiler c_bad ∧ ¬ P_ext c_bad ∧ g c_bad = false)) ∨
    (claim.waivers ≠ .nil ∧
      Exists (fun c_bad : CompilerChoice =>
        ConformingCompiler c_bad ∧ ¬ P_ext c_bad ∧ ¬ SatisfiesWaivers c_bad claim.waivers)) := by
  cases hDep with
  | intro c_bad hRest =>
    cases hRest with
    | intro s_bad hProps =>
      have hConfBad := hProps.1
      have hNotP := hProps.2.1
      have hUb := hProps.2.2
      cases hGuard : claim.constGuard with
      | none =>
        apply Or.inr
        have hNotSat : ¬ SatisfiesWaivers c_bad claim.waivers := by
          intro hSat
          have hSafe := claim.soundOnScopedCompilers c_bad hConfBad hSat s_bad
          rw [hGuard] at hSafe
          change SafeFor (execMir fuel c_bad body s_bad) (Q s_bad) at hSafe
          rw [hUb] at hSafe
          exact hSafe
        have hNonEmpty : claim.waivers ≠ .nil := by
          intro hNil
          apply hNotSat
          rw [hNil]
          exact True.intro
        exact And.intro hNonEmpty
          (Exists.intro c_bad (And.intro hConfBad (And.intro hNotP hNotSat)))
      | some g =>
        cases hG : g c_bad with
        | false =>
          exact Or.inl
            (Exists.intro g
              (And.intro rfl
                (Exists.intro c_bad (And.intro hConfBad (And.intro hNotP hG)))))
        | true =>
          apply Or.inr
          have hNotSat : ¬ SatisfiesWaivers c_bad claim.waivers := by
            intro hSat
            have hSafe := claim.soundOnScopedCompilers c_bad hConfBad hSat s_bad
            rw [hGuard] at hSafe
            change CompileSafeFor
              (match g c_bad with
               | true => CompileAndExecResult.compiled (execMir fuel c_bad body s_bad)
               | false => CompileAndExecResult.compileRejected)
              (Q s_bad) at hSafe
            rw [hG, hUb] at hSafe
            exact hSafe
          have hNonEmpty : claim.waivers ≠ .nil := by
            intro hNil
            apply hNotSat
            rw [hNil]
            exact True.intro
          exact And.intro hNonEmpty
            (Exists.intro c_bad (And.intro hConfBad (And.intro hNotP hNotSat)))

def intoBytesReprRustBody : MirBody :=
  { entry := 0
    blocks :=
      (0, { stmts := .assertNonZero (.eqNat .reprRustStructSize (.constNat 16)) ::
                     .assign 0 (.local 1) :: .nil
            term := .returnLocal 0 }) :: .nil }

def zerocopyPaddingFreeGuard (c : CompilerChoice) : Bool :=
  Nat.beq c.reprRustStructSize 16

theorem intoBytes_exec_when_size_16 (c : CompilerChoice) (s : Store)
    (hSz : Nat.beq c.reprRustStructSize 16 = true) :
    execMir 2 c intoBytesReprRustBody s = .ok (s 1) := by
  have h16 : c.reprRustStructSize = 16 := nat_eq_of_beq_eq_true hSz
  cases c with
  | mk _ _ _ _ sz _ _ _ _ _ =>
    change sz = 16 at h16
    cases h16
    exact rfl

theorem intoBytes_guard_sound (c : CompilerChoice) (s : Store) :
    ∀ (b : Bool),
      Nat.beq c.reprRustStructSize 16 = b →
      CompileSafeFor
        (match b with
         | true => .compiled (execMir 2 c intoBytesReprRustBody s)
         | false => .compileRejected)
        (fun ret => ret = s 1)
  | false, _ => True.intro
  | true, hSz => by
    change SafeFor (execMir 2 c intoBytesReprRustBody s) (fun ret => ret = s 1)
    rw [intoBytes_exec_when_size_16 c s hSz]
    exact rfl

def zerocopyRouteAClaim : AuditedCrateClaim 2 intoBytesReprRustBody (fun s ret => ret = s 1) :=
  { constGuard := some zerocopyPaddingFreeGuard
    waivers := .nil
    soundOnScopedCompilers := fun c _ _ s =>
      intoBytes_guard_sound c s (Nat.beq c.reprRustStructSize 16) rfl }

theorem zerocopy_route_a_padding_free_witness (s : Store) :
    zerocopyRouteAClaim.waivers = .nil ∧
    GenuinelyDependsOn (fun c => c.reprRustStructSize = 16) 2 intoBytesReprRustBody ∧
    compileAndExec (some zerocopyPaddingFreeGuard) 2 rustc_1_96 intoBytesReprRustBody s =
      .compiled (.ok (s 1)) ∧
    compileAndExec (some zerocopyPaddingFreeGuard) 2 rustc_1_100_rand intoBytesReprRustBody s =
      .compileRejected :=
  And.intro rfl
    (And.intro
      (Exists.intro rustc_1_100_rand
        (Exists.intro s
          (And.intro rustc_1_100_rand_conforming
            (And.intro (fun h => nomatch h) rfl))))
      (And.intro rfl rfl))

end NormativeForwardsCompatibility

#print axioms NormativeForwardsCompatibility.forwards_compatible_envelope_transfer
#print axioms NormativeForwardsCompatibility.normative_proof_transfers_to_all_conforming_compilers
#print axioms NormativeForwardsCompatibility.non_normative_layout_countersample
#print axioms NormativeForwardsCompatibility.trunk_addition_preserves_existing_wp
#print axioms NormativeForwardsCompatibility.profile_flag_preserves_unaffected_wp
#print axioms NormativeForwardsCompatibility.callee_impl_drift_breaks_inlined_body
#print axioms NormativeForwardsCompatibility.opaque_normative_contract_absorbs_stdlib_drift
#print axioms NormativeForwardsCompatibility.inlined_stdlib_mir_breaks_across_boxraw_refactor
#print axioms NormativeForwardsCompatibility.wp_invariant_under_temp_and_cfg_refactoring
#print axioms NormativeForwardsCompatibility.raw_cfg_cert_breaks_on_block_split
#print axioms NormativeForwardsCompatibility.non_normative_assumption_logged_or_compile_guarded
#print axioms NormativeForwardsCompatibility.zerocopy_route_a_padding_free_witness
