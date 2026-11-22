/-
  Core syntax and semantics for `Toy.SubstStable`:
  open vs. closed types, const-index expressions with partial operations,
  parameter bounds, instantiation (substitution + projection/const normalization),
  substitution stability, packed/align well-formedness, post-monomorphization
  collection with used vs. mentioned items, and generic vs. monomorphic IR capture.
-/

namespace Toy.SubstStable

/-! ## 1. Canonical const values and const-index expressions -/

/-- Canonical compile-time values: natural scalars and finite acyclic constructor trees. -/
inductive CVal where
  | nat (n : Nat)
  | ctor (tag : Nat) (args : List CVal)

mutual
  private def decEqCVal : (a b : CVal) → Decidable (a = b)
    | .nat n, .nat m =>
        if h : n = m then isTrue (by rw [h])
        else isFalse (fun hc => by injection hc; exact h ‹_›)
    | .ctor t1 as1, .ctor t2 as2 =>
        if ht : t1 = t2 then
          match decEqCValList as1 as2 with
          | isTrue ha => isTrue (by rw [ht, ha])
          | isFalse ha => isFalse (fun hc => by injection hc; exact ha ‹_›)
        else isFalse (fun hc => by injection hc; exact ht ‹_›)
    | .nat _, .ctor _ _ => isFalse CVal.noConfusion
    | .ctor _ _, .nat _ => isFalse CVal.noConfusion

  private def decEqCValList : (as1 as2 : List CVal) → Decidable (as1 = as2)
    | [], [] => isTrue rfl
    | x :: xs, y :: ys =>
        match decEqCVal x y, decEqCValList xs ys with
        | isTrue hx, isTrue hxs => isTrue (by rw [hx, hxs])
        | isFalse hx, _ => isFalse (fun hc => by injection hc; exact hx ‹_›)
        | _, isFalse hxs => isFalse (fun hc => by injection hc; exact hxs ‹_›)
    | [], _ :: _ => isFalse (by intro hc; cases hc)
    | _ :: _, [] => isFalse (by intro hc; cases hc)
end

instance : DecidableEq CVal := decEqCVal

/-- Const-index expressions over natural-valued const parameters (`cparam`),
    constructor trees (`ctor`), total addition (`add`), and partial checked
    subtraction (`sub`) and floor division (`div`). -/
inductive IdxTerm where
  | lit (n : Nat)
  | cparam (i : Nat)
  | ctor (tag : Nat) (args : List IdxTerm)
  | add (a b : IdxTerm)
  | sub (a b : IdxTerm)
  | div (a b : IdxTerm)

mutual
  private def decEqIdxTerm : (a b : IdxTerm) → Decidable (a = b)
    | .lit n, .lit m =>
        if h : n = m then isTrue (by rw [h])
        else isFalse (fun hc => by injection hc; exact h ‹_›)
    | .cparam i, .cparam j =>
        if h : i = j then isTrue (by rw [h])
        else isFalse (fun hc => by injection hc; exact h ‹_›)
    | .ctor t1 as1, .ctor t2 as2 =>
        if ht : t1 = t2 then
          match decEqIdxTermList as1 as2 with
          | isTrue ha => isTrue (by rw [ht, ha])
          | isFalse ha => isFalse (fun hc => by injection hc; exact ha ‹_›)
        else isFalse (fun hc => by injection hc; exact ht ‹_›)
    | .add a1 b1, .add a2 b2 =>
        match decEqIdxTerm a1 a2, decEqIdxTerm b1 b2 with
        | isTrue ha, isTrue hb => isTrue (by rw [ha, hb])
        | isFalse ha, _ => isFalse (fun hc => by injection hc; exact ha ‹_›)
        | _, isFalse hb => isFalse (fun hc => by injection hc; exact hb ‹_›)
    | .sub a1 b1, .sub a2 b2 =>
        match decEqIdxTerm a1 a2, decEqIdxTerm b1 b2 with
        | isTrue ha, isTrue hb => isTrue (by rw [ha, hb])
        | isFalse ha, _ => isFalse (fun hc => by injection hc; exact ha ‹_›)
        | _, isFalse hb => isFalse (fun hc => by injection hc; exact hb ‹_›)
    | .div a1 b1, .div a2 b2 =>
        match decEqIdxTerm a1 a2, decEqIdxTerm b1 b2 with
        | isTrue ha, isTrue hb => isTrue (by rw [ha, hb])
        | isFalse ha, _ => isFalse (fun hc => by injection hc; exact ha ‹_›)
        | _, isFalse hb => isFalse (fun hc => by injection hc; exact hb ‹_›)
    | .lit _, .cparam _ | .lit _, .ctor _ _ | .lit _, .add _ _ | .lit _, .sub _ _ | .lit _, .div _ _
    | .cparam _, .lit _ | .cparam _, .ctor _ _ | .cparam _, .add _ _ | .cparam _, .sub _ _ | .cparam _, .div _ _
    | .ctor _ _, .lit _ | .ctor _ _, .cparam _ | .ctor _ _, .add _ _ | .ctor _ _, .sub _ _ | .ctor _ _, .div _ _
    | .add _ _, .lit _ | .add _ _, .cparam _ | .add _ _, .ctor _ _ | .add _ _, .sub _ _ | .add _ _, .div _ _
    | .sub _ _, .lit _ | .sub _ _, .cparam _ | .sub _ _, .ctor _ _ | .sub _ _, .add _ _ | .sub _ _, .div _ _
    | .div _ _, .lit _ | .div _ _, .cparam _ | .div _ _, .ctor _ _ | .div _ _, .add _ _ | .div _ _, .sub _ _ =>
        isFalse IdxTerm.noConfusion

  private def decEqIdxTermList : (as1 as2 : List IdxTerm) → Decidable (as1 = as2)
    | [], [] => isTrue rfl
    | x :: xs, y :: ys =>
        match decEqIdxTerm x y, decEqIdxTermList xs ys with
        | isTrue hx, isTrue hxs => isTrue (by rw [hx, hxs])
        | isFalse hx, _ => isFalse (fun hc => by injection hc; exact hx ‹_›)
        | _, isFalse hxs => isFalse (fun hc => by injection hc; exact hxs ‹_›)
    | [], _ :: _ => isFalse (by intro hc; cases hc)
    | _ :: _, [] => isFalse (by intro hc; cases hc)
end

instance : DecidableEq IdxTerm := decEqIdxTerm

mutual
/-- Predicate selecting acyclic constructor-and-parameter index terms over canonical
    scalars, excluding unevaluated arithmetic (`add`, `sub`, `div`). -/
def isCtorIdx : IdxTerm → Bool
  | .lit _ => true
  | .cparam _ => true
  | .ctor _ args => isCtorIdxList args
  | .add _ _ => false
  | .sub _ _ => false
  | .div _ _ => false

/-- Pointwise `isCtorIdx` over argument lists. -/
def isCtorIdxList : List IdxTerm → Bool
  | [] => true
  | e :: es => isCtorIdx e && isCtorIdxList es
end

mutual
/-- Evaluate an index expression under const-parameter valuation `γ : Nat → Nat`.
    `sub` fails (`none`) on underflow (`x < y`, checked natural subtraction rather than
    truncating subtraction); `div` fails (`none`) on divisor `0` (checked floor division);
    arithmetic on `ctor` values fails (`none`). -/
def evalIdx (γ : Nat → Nat) : IdxTerm → Option CVal
  | .lit n => some (.nat n)
  | .cparam i => some (.nat (γ i))
  | .ctor tag args => (evalIdxList γ args).map (.ctor tag)
  | .add a b =>
      match evalIdx γ a, evalIdx γ b with
      | some (.nat x), some (.nat y) => some (.nat (x + y))
      | _, _ => none
  | .sub a b =>
      match evalIdx γ a, evalIdx γ b with
      | some (.nat x), some (.nat y) => if y ≤ x then some (.nat (x - y)) else none
      | _, _ => none
  | .div a b =>
      match evalIdx γ a, evalIdx γ b with
      | some (.nat x), some (.nat y) => if 0 < y then some (.nat (x / y)) else none
      | _, _ => none

/-- Evaluate a list of index expressions left to right, failing if any element fails. -/
def evalIdxList (γ : Nat → Nat) : List IdxTerm → Option (List CVal)
  | [] => some []
  | e :: es =>
      match evalIdx γ e, evalIdxList γ es with
      | some v, some vs => some (v :: vs)
      | _, _ => none
end

/-- Semantic (definitional) equality of two open index expressions across all const valuations:
    every valuation evaluates both to the same `Option CVal` outcome. -/
def IdxSemEq (e1 e2 : IdxTerm) : Prop :=
  ∀ γ : Nat → Nat, evalIdx γ e1 = evalIdx γ e2

/-- Total evaluability of an open index expression: no const valuation fails (`none`). -/
def IdxTotal (e : IdxTerm) : Prop :=
  ∀ γ : Nat → Nat, (evalIdx γ e).isSome = true

/-! ## 2. Closed and open types, layout queries, and packed/align well-formedness -/

/-- Closed, fully normalized types: base scalars (`sz`, `al`), binary products,
    `packed(k)` and `align(n)` representation wrappers, and const-indexed types `arr`. -/
inductive ClosedTy where
  | base (sz al : Nat)
  | prod (a b : ClosedTy)
  | packed (k : Nat) (inner : ClosedTy)
  | align (n : Nat) (inner : ClosedTy)
  | arr (elem : ClosedTy) (idx : CVal)
  deriving DecidableEq

/-- Open types: closed forms together with type parameters (`tparam`) and associated-type
    projections (`proj tr arg`, modeling `<arg as Trait_tr>::Assoc`). -/
inductive OpenTy where
  | base (sz al : Nat)
  | tparam (i : Nat)
  | prod (a b : OpenTy)
  | packed (k : Nat) (inner : OpenTy)
  | align (n : Nat) (inner : OpenTy)
  | arr (elem : OpenTy) (idx : IdxTerm)
  | proj (tr : Nat) (arg : OpenTy)
  deriving DecidableEq

/-- Unpadded payload byte size of a closed type: `prod` sums component sizes without
    inter-field alignment padding, `align` leaves `byteSize` unchanged without alignment
    rounding, `arr elem (.nat n)` repeats `elem` `n` times, and non-scalar constructor
    indices `arr elem (.ctor _ _)` carry unit count `1` (ignoring constructor arguments). -/
def ClosedTy.byteSize : ClosedTy → Nat
  | .base sz _ => sz
  | .prod a b => a.byteSize + b.byteSize
  | .packed _ inner => inner.byteSize
  | .align _ inner => inner.byteSize
  | .arr elem (.nat n) => elem.byteSize * n
  | .arr elem (.ctor _ _) => elem.byteSize

/-- Effective alignment of a closed type (`packed(k)` lowers alignment to `min k inner.effAlign`;
    `align(n)` raises alignment to `max n inner.effAlign`). -/
def ClosedTy.effAlign : ClosedTy → Nat
  | .base _ al => al
  | .prod a b => max a.effAlign b.effAlign
  | .packed k inner => min k inner.effAlign
  | .align n inner => max n inner.effAlign
  | .arr elem _ => elem.effAlign

/-- Closed-type property `byteSize ≤ k`. -/
def sizeLe (k : Nat) (τ : ClosedTy) : Bool :=
  decide (τ.byteSize ≤ k)

/-- Closed-type property checking that a pair `(Src, Dst)` has equal byte sizes. -/
def eqProdByteSize : ClosedTy → Bool
  | .prod a b => decide (a.byteSize = b.byteSize)
  | _ => false

/-- Whether a closed type transitively contains an explicit `align(n)` wrapper. -/
def hasAlignWrapper : ClosedTy → Bool
  | .base _ _ => false
  | .prod a b => hasAlignWrapper a || hasAlignWrapper b
  | .packed _ inner => hasAlignWrapper inner
  | .align _ _ => true
  | .arr elem _ => hasAlignWrapper elem

/-- Closed packed/align containment well-formedness: no `packed` wrapper transitively
    contains an `align`-wrapped type. -/
def packedNoAlignWf : ClosedTy → Bool
  | .base _ _ => true
  | .prod a b => packedNoAlignWf a && packedNoAlignWf b
  | .packed _ inner => (!hasAlignWrapper inner) && packedNoAlignWf inner
  | .align _ inner => packedNoAlignWf inner
  | .arr elem _ => packedNoAlignWf elem

/-! ## 3. Substitutions, associated-type environments, instantiation, and bounds -/

/-- Associated-type normalization environment mapping `(traitId, normalizedSelfTy)` to its
    normalized closed associated type, or `none` if no impl applies. -/
abbrev AssocEnv : Type := Nat → ClosedTy → Option ClosedTy

/-- Concrete instantiation arguments for type and const parameters. -/
structure Subst where
  ty : Nat → ClosedTy
  cnst : Nat → Nat

/-- Instantiate an open type by substituting parameters (`σ`), evaluating const-index
    expressions (`evalIdx σ.cnst`), and normalizing associated-type projections (`A`).
    Returns `none` if any const expression fails evaluation or any projection fails lookup. -/
def instTy (A : AssocEnv) (σ : Subst) : OpenTy → Option ClosedTy
  | .base sz al => some (.base sz al)
  | .tparam i => some (σ.ty i)
  | .prod a b =>
      match instTy A σ a, instTy A σ b with
      | some a', some b' => some (.prod a' b')
      | _, _ => none
  | .packed k inner => (instTy A σ inner).map (.packed k)
  | .align n inner => (instTy A σ inner).map (.align n)
  | .arr elem idx =>
      match instTy A σ elem, evalIdx σ.cnst idx with
      | some elem', some v => some (.arr elem' v)
      | _, _ => none
  | .proj tr arg =>
      match instTy A σ arg with
      | some arg' => A tr arg'
      | none => none

/-- General semantic bound predicate on `(AssocEnv, Subst)` environments. -/
abbrev BoundPred : Type := AssocEnv → Subst → Prop

/-- Vacuous bound predicate imposing no constraints on `A` or `σ`. -/
def unbounded : BoundPred := fun _ _ => True

/-- Semantic entailment between bound predicates (`B1` is at least as strong as `B2`). -/
def BoundEntails (B1 B2 : BoundPred) : Prop :=
  ∀ A σ, B1 A σ → B2 A σ

/-- A definition-site check `C` is sound relative to bound `B` for closed-type property `Φ`
    when `C t = true` implies `Φ τ = true` for every `B`-conforming closed instance `τ` of `t`. -/
def DefCheckSound (B : BoundPred) (Φ : ClosedTy → Bool) (C : OpenTy → Bool) : Prop :=
  ∀ t A σ τ, C t = true → B A σ → instTy A σ t = some τ → Φ τ = true

/-- A definition-site check `C` is instance-complete relative to bound `B` for `Φ`
    when `C` accepts every open type `t` admitting at least one `B`-conforming closed
    type instance satisfying `Φ`. -/
def DefCheckComplete (B : BoundPred) (Φ : ClosedTy → Bool) (C : OpenTy → Bool) : Prop :=
  ∀ t A σ τ, B A σ → instTy A σ t = some τ → Φ τ = true → C t = true

/-- Every `B`-conforming closed instance of `t` satisfies `Φ`. -/
def AllInstSat (B : BoundPred) (Φ : ClosedTy → Bool) (t : OpenTy) : Prop :=
  ∀ A σ τ, B A σ → instTy A σ t = some τ → Φ τ = true

/-- Property `Φ` is substitution-stable relative to bound `B` when on every open type `t`,
    all `B`-conforming closed instances of `t` agree on `Φ` (`Φ` is determined by `t` up to `B`). -/
def SubstStable (B : BoundPred) (Φ : ClosedTy → Bool) : Prop :=
  ∀ t A1 σ1 τ1 A2 σ2 τ2,
    B A1 σ1 → instTy A1 σ1 t = some τ1 →
    B A2 σ2 → instTy A2 σ2 t = some τ2 →
    Φ τ1 = Φ τ2

/-- Witness map supplying, for each open type `t`, a `B`-conforming environment `(A, σ)`
    at which `t` instantiates whenever `t` admits at least one `B`-conforming closed instance. -/
def HasInstWitness (B : BoundPred) (w : OpenTy → AssocEnv × Subst) : Prop :=
  ∀ t, (∃ A σ τ, B A σ ∧ instTy A σ t = some τ) →
    B (w t).1 (w t).2 ∧ (instTy (w t).1 (w t).2 t).isSome = true

/-- Canonical definition-site check derived from an instantiation witness `w`:
    instantiate `t` at `w t` and evaluate `Φ` (accepting vacuous uninstantiable terms). -/
def witnessDefCheck (Φ : ClosedTy → Bool) (w : OpenTy → AssocEnv × Subst) (t : OpenTy) : Bool :=
  match instTy (w t).1 (w t).2 t with
  | some τ => Φ τ
  | none => true

/-! ## 4. Declared syntactic bounds for packed/align checking -/

/-- Declared parameter and associated-type bounds for packed/align checking:
    `paramNoAlign` lists type parameters forbidden from carrying `align(n)` wrappers;
    `projNoAlign` lists associated-type trait ids forbidden from normalizing to `align(n)` types. -/
structure DeclBounds where
  paramNoAlign : List Nat
  projNoAlign : List Nat
  deriving DecidableEq

/-- Empty syntactic bounds: no parameter or associated-type `noAlign` restrictions beyond
    closed-argument well-formedness. -/
def emptyBounds : DeclBounds := ⟨[], []⟩

/-- Semantic meaning of `DeclBounds` on `(A, σ)`: every parameter type and normalized
    associated type is itself `packedNoAlignWf`, listed `paramNoAlign` parameters carry no
    transitive `align(n)` wrapper, and listed `projNoAlign` trait ids carry no transitive
    `align(n)` wrapper across any `AssocEnv` entry `A tr τ` (global trait-level bound). -/
def DeclBounds.sat (d : DeclBounds) (A : AssocEnv) (σ : Subst) : Prop :=
  (∀ i, packedNoAlignWf (σ.ty i) = true) ∧
  (∀ tr src rhs, A tr src = some rhs → packedNoAlignWf rhs = true) ∧
  (∀ i, i ∈ d.paramNoAlign → hasAlignWrapper (σ.ty i) = false) ∧
  (∀ tr, tr ∈ d.projNoAlign → ∀ τ rhs, A tr τ = some rhs → hasAlignWrapper rhs = false)

/-- Global semantic bound forbidding `align(n)` wrappers in all type arguments and all
    normalized associated-type outputs (used as positive-control / stability bound). -/
def FullNoAlignBound (A : AssocEnv) (σ : Subst) : Prop :=
  (∀ i, packedNoAlignWf (σ.ty i) = true ∧ hasAlignWrapper (σ.ty i) = false) ∧
  (∀ tr src rhs, A tr src = some rhs → packedNoAlignWf rhs = true ∧ hasAlignWrapper rhs = false)

/-- Refinement of `FullNoAlignBound` pinning const parameters to `0`, admitting a uniform
    total instantiation-witness map across all open types. -/
def FixedConstNoAlignBound (A : AssocEnv) (σ : Subst) : Prop :=
  FullNoAlignBound A σ ∧ σ.cnst = fun _ => 0

/-- Canonical total witness map for `FixedConstNoAlignBound`. -/
def constZeroNoAlignWitness (_ : OpenTy) : AssocEnv × Subst :=
  (fun _ _ => some (.base 1 1), ⟨fun _ => .base 1 1, fun _ => 0⟩)

/-- Naive syntactic check on open types that inspects only literal `.align` wrappers visible in
    the open AST, optimistically treating parameters and projections as `align`-free. -/
def naiveOpenHasAlign : OpenTy → Bool
  | .base _ _ => false
  | .tparam _ => false
  | .prod a b => naiveOpenHasAlign a || naiveOpenHasAlign b
  | .packed _ inner => naiveOpenHasAlign inner
  | .align _ _ => true
  | .arr elem _ => naiveOpenHasAlign elem
  | .proj _ _ => false

/-- Naive definition-site `packed`/`align` check on normalized output structure: rejects only
    syntactically visible `align` wrappers inside `packed` (`Packed<T>` and `Packed<T::Assoc>`
    are accepted; `.proj tr arg` returns `true` without inspecting `arg` at any position). -/
def naiveDefPackedCheck : OpenTy → Bool
  | .base _ _ => true
  | .tparam _ => true
  | .prod a b => naiveDefPackedCheck a && naiveDefPackedCheck b
  | .packed _ inner => (!naiveOpenHasAlign inner) && naiveDefPackedCheck inner
  | .align _ inner => naiveDefPackedCheck inner
  | .arr elem _ => naiveDefPackedCheck elem
  | .proj _ _ => true

/-- Bound-aware conservative check for whether an open type *may* normalize to a closed type
    containing an `align` wrapper under `DeclBounds`: parameters and projections may carry
    `align` unless excluded by `d.paramNoAlign` or `d.projNoAlign` (does not inspect `arg` of
    `.proj tr arg`, which `instTy` erases after `AssocEnv` lookup). -/
def mayHaveAlignUnder (d : DeclBounds) : OpenTy → Bool
  | .base _ _ => false
  | .tparam i => !decide (i ∈ d.paramNoAlign)
  | .prod a b => mayHaveAlignUnder d a || mayHaveAlignUnder d b
  | .packed _ inner => mayHaveAlignUnder d inner
  | .align _ _ => true
  | .arr elem _ => mayHaveAlignUnder d elem
  | .proj tr _ => !decide (tr ∈ d.projNoAlign)

/-- Bound-aware definition-site `packed`/`align` check: every `.packed k inner` requires
    `mayHaveAlignUnder d inner = false` (neither `mayHaveAlignUnder` nor `boundedDefPackedCheck`
    inspects `arg` of `.proj tr arg` inside or outside `.packed`, since `instTy` normalizes
    `.proj tr arg` to `A tr arg'` whose `packedNoAlignWf` is guaranteed by `DeclBounds.sat`). -/
def boundedDefPackedCheck (d : DeclBounds) : OpenTy → Bool
  | .base _ _ => true
  | .tparam _ => true
  | .prod a b => boundedDefPackedCheck d a && boundedDefPackedCheck d b
  | .packed _ inner => (!mayHaveAlignUnder d inner) && boundedDefPackedCheck d inner
  | .align _ inner => boundedDefPackedCheck d inner
  | .arr elem _ => boundedDefPackedCheck d elem
  | .proj _ _ => true

/-! ## 5. Post-monomorphization assertions and used vs. mentioned collection -/

/-- Closed monomorphic instance key: function id, closed type arguments, and const arguments. -/
structure MonoKey where
  fnId : Nat
  tyArgs : List ClosedTy
  cnstArgs : List Nat
  deriving DecidableEq

/-- Post-monomorphization assertion kinds attached to generic functions. -/
inductive PmeCheck where
  | packedWf (target : OpenTy)
  | sizeEq (lhs rhs : OpenTy)
  | alignLe (lhs rhs : OpenTy)
  | idxValid (idx : IdxTerm)
  deriving DecidableEq

/-- Evaluate one `PmeCheck` on a monomorphic call environment `(A, σ)`. -/
def evalPmeCheck (A : AssocEnv) (σ : Subst) : PmeCheck → Bool
  | .packedWf t =>
      match instTy A σ t with
      | some τ => packedNoAlignWf τ
      | none => false
  | .sizeEq l r =>
      match instTy A σ l, instTy A σ r with
      | some τ1, some τ2 => decide (τ1.byteSize = τ2.byteSize)
      | _, _ => false
  | .alignLe l r =>
      match instTy A σ l, instTy A σ r with
      | some τ1, some τ2 => decide (τ1.effAlign ≤ τ2.effAlign)
      | _, _ => false
  | .idxValid idx => (evalIdx σ.cnst idx).isSome

/-- Generic function body statements distinguishing live `call` sites from dead-branch
    (`if false { ... }`) statements erased from `used` items but retained in `mentioned` items. -/
inductive GenStmt where
  | skip
  | seq (a b : GenStmt)
  | call (callee : Nat) (tyArgs : List OpenTy) (cnstArgs : List IdxTerm)
  | deadBranch (body : GenStmt)
  deriving DecidableEq

/-- Generic function declaration with declared bounds, PME assertions, MIR availability flag
    (`localMir`), and generic body. -/
structure GenFn where
  bounds : DeclBounds
  pmeAsserts : List PmeCheck
  localMir : Bool
  body : GenStmt
  deriving DecidableEq

/-- Program environment for collection and IR capture: generic function table and assoc impls. -/
structure CrateProg where
  fns : List GenFn
  assoc : AssocEnv

/-- Build a `Subst` from explicit type and const argument lists (defaulting out-of-range
    indices to `base 1 1` and `0`). -/
def substOfKey (k : MonoKey) : Subst where
  ty i := k.tyArgs.getD i (.base 1 1)
  cnst i := k.cnstArgs.getD i 0

/-- Whether `k.fnId` resolves in `P` to a function with locally available MIR (`localMir = true`). -/
def isLocalFn (P : CrateProg) (k : MonoKey) : Bool :=
  match P.fns[k.fnId]? with
  | some fn => fn.localMir
  | none => false

/-- Every key in `T` resolves to a function with locally available MIR (`isLocalFn P k = true`). -/
def AllLocalMir (P : CrateProg) (T : List MonoKey) : Prop :=
  ∀ k ∈ T, isLocalFn P k = true

/-- Whether a monomorphic instance `k` passes local PME checks during per-crate collection.
    Undefined functions return `false`; unavailable external MIR (`localMir = false`) has no
    local PME body to evaluate and returns `true`. -/
def passesLocalPme (P : CrateProg) (k : MonoKey) : Bool :=
  match P.fns[k.fnId]? with
  | none => false
  | some fn =>
      if fn.localMir then
        fn.pmeAsserts.all (evalPmeCheck P.assoc (substOfKey k))
      else
        true

/-- Intrinsic validity of an instance's PME assertions regardless of whether its MIR is local
    to the current crate (returns `false` for undefined `fnId`). -/
def passesIntrinsicPme (P : CrateProg) (k : MonoKey) : Bool :=
  match P.fns[k.fnId]? with
  | none => false
  | some fn => fn.pmeAsserts.all (evalPmeCheck P.assoc (substOfKey k))

/-- Instantiate a list of open type arguments, failing (`none`) if any argument fails. -/
def instTyList (A : AssocEnv) (σ : Subst) : List OpenTy → Option (List ClosedTy)
  | [] => some []
  | t :: ts =>
      match instTy A σ t, instTyList A σ ts with
      | some τ, some τs => some (τ :: τs)
      | _, _ => none

/-- Evaluate a list of `Nat` const arguments (`evalIdx` must yield `CVal.nat`). -/
def evalNatArgs (γ : Nat → Nat) : List IdxTerm → Option (List Nat)
  | [] => some []
  | e :: es =>
      match evalIdx γ e, evalNatArgs γ es with
      | some (.nat n), some ns => some (n :: ns)
      | _, _ => none

/-- Extract post-optimization `used` callee instances (`deadBranch` is erased).
    Returns `none` if an instantiated call's type or const argument fails evaluation. -/
def usedStmtRefs (A : AssocEnv) (σ : Subst) : GenStmt → Option (List MonoKey)
  | .skip => some []
  | .seq a b =>
      match usedStmtRefs A σ a, usedStmtRefs A σ b with
      | some r1, some r2 => some (r1 ++ r2)
      | _, _ => none
  | .call callee tys cnsts =>
      match instTyList A σ tys, evalNatArgs σ.cnst cnsts with
      | some τs, some ns => some [⟨callee, τs, ns⟩]
      | _, _ => none
  | .deadBranch _ => some []

/-- Extract pre-optimization `mentioned` callee instances (`deadBranch` is traversed). -/
def mentionedStmtRefs (A : AssocEnv) (σ : Subst) : GenStmt → Option (List MonoKey)
  | .skip => some []
  | .seq a b =>
      match mentionedStmtRefs A σ a, mentionedStmtRefs A σ b with
      | some r1, some r2 => some (r1 ++ r2)
      | _, _ => none
  | .call callee tys cnsts =>
      match instTyList A σ tys, evalNatArgs σ.cnst cnsts with
      | some τs, some ns => some [⟨callee, τs, ns⟩]
      | _, _ => none
  | .deadBranch body => mentionedStmtRefs A σ body

/-- Outgoing edges of `k` in used-only mode (`false`) vs. used+mentioned mode (`true`). -/
def monoEdges (includeMentioned : Bool) (P : CrateProg) (k : MonoKey) : Option (List MonoKey) :=
  match P.fns[k.fnId]? with
  | none => none
  | some fn =>
      if fn.localMir then
        if includeMentioned then
          mentionedStmtRefs P.assoc (substOfKey k) fn.body
        else
          usedStmtRefs P.assoc (substOfKey k) fn.body
      else
        some []

/-- Collection outcome: `ok items` when collection closes and every visited item passes its
    post-monomorphization checks; `pmeError culprit` on PME or argument-evaluation failure;
    `outOfFuel` when fuel is exhausted before worklist closure. -/
inductive CollectRes where
  | ok (items : List MonoKey)
  | pmeError (culprit : MonoKey)
  | outOfFuel
  deriving DecidableEq

/-- Fuel-bounded worklist collector checking `passesLocalPme` and `monoEdges` on visited keys. -/
def collectLoop (includeMentioned : Bool) (P : CrateProg) :
    Nat → List MonoKey → List MonoKey → CollectRes
  | 0, [], done => .ok done
  | 0, _ :: _, _ => .outOfFuel
  | _ + 1, [], done => .ok done
  | fuel + 1, k :: rest, done =>
      if k ∈ done then
        collectLoop includeMentioned P fuel rest done
      else if !passesLocalPme P k then
        .pmeError k
      else
        match monoEdges includeMentioned P k with
        | none => .pmeError k
        | some nexts =>
            let fresh := nexts.filter (fun k' => !decide (k' ∈ done))
            collectLoop includeMentioned P fuel (rest ++ fresh) (done ++ [k])

/-- Run monomorphization collection with PME checking from `roots`. -/
def collectAndCheck (includeMentioned : Bool) (P : CrateProg) (roots : List MonoKey)
    (fuel : Nat) : CollectRes :=
  collectLoop includeMentioned P fuel roots []

/-- Inductive collector-visible reachability along successful `monoEdges` steps from `roots`
    (truncating outgoing call edges at items with `localMir = false`). -/
inductive Reachable (includeMentioned : Bool) (P : CrateProg) (roots : List MonoKey) :
    MonoKey → Prop where
  | root {k} : k ∈ roots → Reachable includeMentioned P roots k
  | step {k k' ks} :
      Reachable includeMentioned P roots k →
      monoEdges includeMentioned P k = some ks →
      k' ∈ ks →
      Reachable includeMentioned P roots k'

/-- Intrinsic outgoing call edges of `k`, traversing `fn.body` regardless of `fn.localMir`. -/
def intrinsicEdges (includeMentioned : Bool) (P : CrateProg) (k : MonoKey) :
    Option (List MonoKey) :=
  match P.fns[k.fnId]? with
  | none => none
  | some fn =>
      if includeMentioned then
        mentionedStmtRefs P.assoc (substOfKey k) fn.body
      else
        usedStmtRefs P.assoc (substOfKey k) fn.body

/-- Intrinsic call-graph reachability from `roots` through `fn.body` (not truncated at
    `localMir = false`). -/
inductive IntrinsicReachable (includeMentioned : Bool) (P : CrateProg) (roots : List MonoKey) :
    MonoKey → Prop where
  | root {k} : k ∈ roots → IntrinsicReachable includeMentioned P roots k
  | step {k k' ks} :
      IntrinsicReachable includeMentioned P roots k →
      intrinsicEdges includeMentioned P k = some ks →
      k' ∈ ks →
      IntrinsicReachable includeMentioned P roots k'

/-! ## 6. Capturing generic IR versus monomorphic IR -/

/-- Unconditional generic-IR safety of `(fn, openTarget)` for `Φ`: every instantiation satisfying
    only the source-declared `fn.bounds` (without assuming `fn.pmeAsserts` ran) satisfies `Φ`. -/
def GenericBodySafeUnconditional (fn : GenFn) (openTarget : OpenTy) (Φ : ClosedTy → Bool) : Prop :=
  ∀ A σ τ, DeclBounds.sat fn.bounds A σ → instTy A σ openTarget = some τ → Φ τ = true

/-- PME-conditional generic-IR safety of `(fn, openTarget)` for `Φ`: every instantiation
    satisfying both `fn.bounds` and `fn.pmeAsserts` satisfies `Φ`. -/
def GenericBodySafeUnderPme (fn : GenFn) (openTarget : OpenTy) (Φ : ClosedTy → Bool) : Prop :=
  ∀ A σ τ,
    DeclBounds.sat fn.bounds A σ →
    fn.pmeAsserts.all (evalPmeCheck A σ) = true →
    instTy A σ openTarget = some τ →
    Φ τ = true

/-- Post-monomorphization check of a captured monomorphic target `T` for closed property `Φ`
    applied to each captured instance's instantiated target type `targetOf k.fnId`. -/
def checkMonoTarget (A : AssocEnv) (Φ : ClosedTy → Bool) (targetOf : Nat → Option OpenTy)
    (T : List MonoKey) : Bool :=
  T.all fun k =>
    match targetOf k.fnId with
    | none => false
    | some openTarget =>
        match instTy A (substOfKey k) openTarget with
        | some τ => Φ τ
        | none => false

/-- Soundness of monomorphic capture on the captured instance set `T`: every `k ∈ T`
    instantiates its target type to a closed type satisfying `Φ`. -/
def MonoCaptureCertifiedOn (A : AssocEnv) (Φ : ClosedTy → Bool)
    (targetOf : Nat → Option OpenTy) (T : List MonoKey) : Prop :=
  ∀ k ∈ T, ∃ openTarget τ,
    targetOf k.fnId = some openTarget ∧
    instTy A (substOfKey k) openTarget = some τ ∧
    Φ τ = true

/-- Whether function `k.fnId` declares `targetOf k.fnId = some openTarget` and guards it
    with `PmeCheck.packedWf openTarget` in `fn.pmeAsserts`. -/
def keyHasPackedGuard (P : CrateProg) (targetOf : Nat → Option OpenTy) (k : MonoKey) : Bool :=
  match P.fns[k.fnId]?, targetOf k.fnId with
  | some fn, some openTarget => decide (PmeCheck.packedWf openTarget ∈ fn.pmeAsserts)
  | _, _ => false

/-- Every instance `k ∈ T` carries a `PmeCheck.packedWf` assertion for `targetOf k.fnId`. -/
def HasPackedPmeGuard (P : CrateProg) (targetOf : Nat → Option OpenTy) (T : List MonoKey) : Prop :=
  ∀ k ∈ T, keyHasPackedGuard P targetOf k = true

end Toy.SubstStable
