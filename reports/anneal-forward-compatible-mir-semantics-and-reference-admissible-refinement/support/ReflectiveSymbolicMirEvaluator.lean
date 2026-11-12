-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:refinement
import Init.NotationExtra
import Init.Core
import Init

/-!
# Refinement Core and Verification Judgments

Defines the language-independent vocabulary in which `Trusted.CrateTheorem`
(`Trusted/MirSemantics.lean`) is stated:

1. A constructive refinement order (`Preorder`, `Partial`, `Behavior`), where a
   behavior maps each query to a partial predicate over outcomes and undefined
   behavior (UB) is the top element.
2. Program-indexed languages (`Language`), pairing static program
   well-formedness (`wf : Prog → Prop`) with demonic behavioral semantics
   (`sem : Prog → Behavior Query Out`).
3. The verification judgment `Language.Verified`, which bundles static program
   well-formedness (`L.wf prog`), miracle-freedom (`L.ProductiveOn pre prog`),
   and demonic refinement (`L.sem prog ≤ L.SpecOn pre post`). Because `Behavior`
   forms a refinement lattice, multi-guarantee specifications—such as
   unconditional UB-freedom on `SafetyPre` paired with conditional functional
   correctness on `ContractPre := SafetyPre ∧ RequiresAdmits`—are expressed by a
   single `Language.Verified` judgment over `(SafetyPre, EffectivePost)` where
   `EffectivePost q out :=`
   `SafetyPost q out ∧ (RequiresAdmits q → ContractPost q out)`.
4. Named obligations (`Obligation`) and the waiver-aware `VerificationResult`.

Derived combinators (`wellFormedOn`), lattice-meet equivalences, cross-language
compilation codecs (`BehaviorCodec`, `Compiles`, `ProductiveCompiles`), and
their meta-theory live in `theory/` (`Anneal/Refinement.lean`), outside the
trusted computing base.
-/

namespace Trusted

/-- Reflexive and transitive refinement relation (`b₁ ≤ b₂`). -/
class Preorder (B : Type u) extends LE B where
  le_refl  : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

/-- Implication (`P → Q`) equips `Prop` with a refinement preorder. -/
instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

/-- Pointwise lifting equips `A → B` with a refinement preorder. -/
instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

/-- Constructive partiality carrier representing `B ∪ {UB}`: `defined` is
`False` exactly when the computation exhibits undefined behavior. -/
structure Partial (B : Type u) where
  defined : Prop
  val     : defined → B

/-- Demonic refinement on `Partial B`: `p₁ ≤ p₂` holds when, wherever `p₂` is
defined, `p₁` is also defined and refines it. UB (`defined := False`) is
therefore the top element: it refines only itself, and everything refines it.
-/
instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

/-- Query-indexed partial behaviors: for each query, either UB or a predicate
describing the set of permitted outcomes. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- A semantic language.

`wf prog` states static program well-formedness (for example, that all signature
and local types are modeled and within target size bounds, even when a runtime
precondition `pre` is uninhabited). -/
structure Language where
  Prog  : Type
  Query : Type
  Out   : Type
  wf    : Prog → Prop
  sem   : Prog → Behavior Query Out

/-- Behavior domain of `L`. -/
abbrev Language.Behavior (L : Language) : Type :=
  Trusted.Behavior L.Query L.Out

/-- The specification "on queries satisfying `pre`, every outcome satisfies
`post`"; it is UB (undefined, hence unconstrained) outside `pre`. -/
def Language.SpecOn (L : Language)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => ⟨pre q, fun _ => post q⟩

/-- Unconditional specification on `L` (`pre := fun _ => True`). -/
abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

/-- Dijkstra's Law of the Excluded Miracle: every admitted query has at least
one defined outcome. -/
def Language.ProductiveOn (L : Language)
    (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o

/-- Complete behavioral verification of `prog` against `(pre, post)`: static
program well-formedness (`L.wf prog`), miracle-freedom
(`L.ProductiveOn pre prog`), and demonic behavioral refinement
(`L.sem prog ≤ L.SpecOn pre post`). -/
def Language.Verified (L : Language)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  L.wf prog ∧
  L.ProductiveOn pre prog ∧
  L.sem prog ≤ L.SpecOn pre post

/-- Right-nested conjunction of a list of propositions. -/
def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

/-- A named proof obligation pairing its canonical identifier `id` with its
proposition `prop`. -/
structure Obligation (Id : Type) where
  id   : Id
  prop : Prop

/-- Pairwise distinctness of the identifiers in `ids`. -/
def NoDupIds {Id : Type} (ids : List Id) : Prop :=
  (ids.foldr
    (fun id (acc : Prop × List Id) =>
      (AllHold (acc.2.map (fun id' => id ≠ id')) ∧ acc.1, id :: acc.2))
    (True, [])).1

/-- Every obligation in `obligations` either holds by proof (`ob.prop`) or is
explicitly waived in `waived` (`ob.id ∈ waived`), with pairwise-distinct
obligation and waiver identifiers so one waiver cannot cover two obligations. -/
def VerificationResult {Id : Type}
    (waived : List Id)
    (obligations : List (Obligation Id)) : Prop :=
  obligations ≠ [] ∧
  NoDupIds (obligations.map Obligation.id) ∧
  NoDupIds waived ∧
  AllHold (obligations.map (fun ob => ob.prop ∨ ob.id ∈ waived))

end Trusted

-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:step_result

/-!
# Small-Step Operational Machines & Eventual Behaviors (`Trusted/StepResult.lean`)

Instantiates `Trusted.Language` for small-step operational transition systems
(`SmallStepMachine`) without coinduction or `Classical.choice`:

1. `StepResult` (`step`, `choice`, `terminated`, `failed`) plus the smart
   constructor `StepResult.silent`.
2. `ReachesPrefix` enforcing all-prefix safety (`.failed` and `.stuck` are
   unsafe at every finite step budget `n : Nat`).
3. `EventualBehaviorOf` with 3-phase `EventualOut` (`.terminated`, `.diverges`,
   `.reacts`), using constructive infinite trajectory witnesses (`traj`) for
   both silent divergence (`.diverges`) and productive reactivity (`.reacts`),
   and static machine well-formedness `wf := M.wf`.
-/

namespace Trusted

/-- Distinguishes normal return from panic/unwind completion, defined process
abort, and compile-time rejection (`Stmt.evalConst` or `CastKind.transmute`
size mismatch). -/
inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind
  | abort
  | compileTimeError

/-- Single-step transition outcome in a small-step operational machine. -/
inductive StepResult (State : Type) (Obs : Type := Empty) (Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed

/-- Deterministic silent (`τ`) internal step to `next` (emits no `Obs`). -/
def StepResult.silent {State Obs Val : Type}
    (next : State) : StepResult State Obs Val :=
  .choice (· = next)

/-- First-order deterministic small-step outcome without observation events.

Unlike `StepResult.silent` (which wraps `next` inside `StepResult.choice
(· = next)`), `RawStep.silent` carries `next : State` as first-order data so
bounded inner evaluators (such as `evalConstLoop` in `Trusted/MirSemantics.lean`)
can pattern-match on successor states directly before lifting to `StepResult`
via `RawStep.toStepResult`. -/
inductive RawStep (State Val : Type) where
  | silent (next : State)
  | terminated (term : TerminationKind Val)
  | failed

/-- Lift a deterministic `RawStep` into `StepResult`. -/
def RawStep.toStepResult {State Obs Val : Type} :
    RawStep State Val → StepResult State Obs Val
  | .silent s => .silent s
  | .terminated t => .terminated t
  | .failed => .failed

/-- Outcome recorded at the end of an `n`-step execution prefix. -/
inductive PrefixOutcome (State Val : Type) where
  | running (cur : State)
  | terminated (term : TerminationKind Val)
  | failed
  | stuck

/-- A prefix outcome is safe when it neither fails (`.failed`) nor gets stuck
in an unmodeled state or empty choice (`.stuck`). -/
def PrefixOutcome.isSafe {State Val : Type} : PrefixOutcome State Val → Prop
  | .running _ => True
  | .terminated _ => True
  | .failed => False
  | .stuck => False

/-- Step-decoupled observable outcome of an operational execution. -/
inductive EventualOut (Obs : Type := Empty) (Val : Type) where
  | terminated (trace : List Obs) (term : TerminationKind Val)
  | diverges   (trace : List Obs)
  | reacts     (trace : List Obs)

/-- Small-step operational machine parameterized by programs `Prog`, states
`State`, external observations `Obs` (defaulting to `Empty`), and return values
`Val`. -/
structure SmallStepMachine (Prog State : Type) (Obs : Type := Empty)
    (Val : Type) where
  wf        : Prog → Prop := fun _ => True
  initState : Prog → State → Prop
  step      : Prog → State → StepResult State Obs Val → Prop

/-- Inductive reachability of an `n`-step execution prefix from `s`. -/
inductive ReachesPrefix
    {Prog State Obs Val : Type}
    (step : Prog → State → StepResult State Obs Val → Prop) (p : Prog) :
    Nat → State → List Obs → PrefixOutcome State Val → Prop where
  | zero (s : State) :
      ReachesPrefix step p 0 s [] (.running s)
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs)
      (out : PrefixOutcome State Val) :
      step p s (.step obs s') →
      ReachesPrefix step p n s' tr out →
      ReachesPrefix step p (n + 1) s (obs :: tr) out
  | choice (n : Nat) (s s' : State) (branches : State → Prop)
      (tr : List Obs) (out : PrefixOutcome State Val) :
      step p s (.choice branches) →
      branches s' →
      ReachesPrefix step p n s' tr out →
      ReachesPrefix step p (n + 1) s tr out
  | emptyChoice (n : Nat) (s : State) (branches : State → Prop) :
      step p s (.choice branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefix step p (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : TerminationKind Val) :
      step p s (.terminated term) →
      ReachesPrefix step p (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) :
      step p s .failed →
      ReachesPrefix step p (n + 1) s [] .failed
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, step p s r) →
      ReachesPrefix step p (n + 1) s [] .stuck

/-- Step-decoupled eventual behavior of program `p` in machine `M`, using
constructive infinite trajectory witnesses `traj : Nat → State` for both
`.diverges` and `.reacts`. -/
def EventualBehaviorOf {Prog State Obs Val : Type}
    (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    State → Partial (EventualOut Obs Val → Prop) :=
  fun init => {
    defined :=
      M.initState p init →
        ∀ n tr out,
          ReachesPrefix M.step p n init tr out →
          out.isSafe
    val := fun _ out =>
      M.initState p init ∧
      match out with
      | .terminated tr term =>
          ∃ n, ReachesPrefix M.step p n init tr (.terminated term)
      | .diverges tr =>
          ∃ n s, ReachesPrefix M.step p n init tr (.running s) ∧
            ∃ traj : Nat → State, traj 0 = s ∧
              ∀ k, ∃ m, ReachesPrefix M.step p (m + 1) (traj k) []
                (.running (traj (k + 1)))
      | .reacts tr =>
          tr ≠ [] ∧ ∃ n s, ReachesPrefix M.step p n init tr (.running s) ∧
            ∃ (traj : Nat → State) (segTrace : Nat → List Obs),
              traj 0 = s ∧
              ∀ k, segTrace k ≠ [] ∧
                ∃ m, ReachesPrefix M.step p (m + 1) (traj k) (segTrace k)
                  (.running (traj (k + 1)))
  }

/-- Package a `SmallStepMachine` as a `Trusted.Language` with static program
well-formedness `wf := M.wf`. -/
abbrev SmallStepMachine.toLanguage {Prog State Obs Val : Type}
    (M : SmallStepMachine Prog State Obs Val) :
    Language where
  Prog  := Prog
  Query := State
  Out   := EventualOut Obs Val
  wf    := M.wf
  sem   := EventualBehaviorOf M

end Trusted
-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_ast

/-!
# Trusted MIR Abstract Syntax Tree (`Trusted/MirAst.lean`)

Defines the first-order representation of `rustc`'s
`MirPhase::Runtime(RuntimePhase::PostCleanup)` Mid-level Intermediate
Representation (MIR) for scalar, aggregate (ADT), and polymorphic functions,
including `Stmt.evalConst` and `Body::required_consts` for compile-time constant
evaluation, `AdtRepr` and `LayoutQuery` for representation-aware type layout,
and the first-order specification and crate descriptors (`InvariantSpec`,
`RequiresSpec`, `PostSpec`, `ObligationId`, `TCBItem`, `BodyDecl`, `CapturedFn`,
`Crate`)
(`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` and
`rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b`).

This file fixes the complete first-order syntax vocabulary that
`anneal-rustc-capture` emits into `Mir.lean`. It assigns no semantic meaning;
`Trusted/MirSemantics.lean` does.
-/

namespace Trusted

/-- Index of a MIR local variable or temporary (`_0`, `_1`, ...), corresponding
to `rustc_middle::mir::Local`
(`compiler/rustc_middle/src/mir/mod.rs#L235-L240`):
> "The first local is the return value pointer, followed by `arg_count` locals
> for the function arguments, followed by any user-declared variables and
> temporaries." -/
structure LocalId where
  index : Nat

/-- Index of a basic block (`bb0`, `bb1`, ...) in `Body::basic_blocks`
(`compiler/rustc_middle/src/mir/mod.rs#L207-L209`):
> "A list of basic blocks. References to basic block use a newtyped index type
> [`BasicBlock`] that indexes into this vector." -/
structure BlockId where
  index : Nat

/-- Crate-local identifier of a captured `MirBody` in `Crate.bodies`.
Referencing callees and required constants by `BodyId` rather than embedding
`MirBody` inline keeps the AST non-mutually-inductive and lets body lookups
operate over a flat table. -/
structure BodyId where
  index : Nat

/-- Target C ABI primitive layout parameters captured from `tcx.data_layout()`
(`compiler/rustc_abi/src/layout.rs#L65-L95`, `src/type-layout.md#L58-L94`).

Because Anneal verifies a fixed configured compilation $C$, the compilation
target's pointer width and primitive integer ABI alignments (`i64Align`,
`i128Align`) are crate-level syntax constants fixed for $C$. -/
structure TargetLayout where
  ptrByteWidth : Nat := 8
  i64Align : Nat := 8
  i128Align : Nat := 16

/-- Default 64-bit target layout (`ptrByteWidth = 8`, `i64Align = 8`,
`i128Align = 16`). -/
def defaultTargetLayout : TargetLayout := ⟨8, 8, 16⟩

/-- MIR type grammar for scalar, aggregate (ADT), polymorphic, reference, and
pointer types (`src/types/numeric.md#L37-L38`, `src/types/boolean.md#L6-L7`,
`compiler/rustc_type_ir/src/ty_kind.rs#L106-L165`):
> "The `usize` type is an unsigned integer type with the same number of bits as
> the platform's pointer type."

`.param idx` is the `idx`-th generic type parameter of the *root* function
being verified. Callee bodies are instantiated by substitution
(`MirBody.subst`), so a `.param` that the semantics reads always refers to the
root function's parameters. `.adt id` names the `AdtDecl` with that `id`; the
capture monomorphizes generic ADTs into distinct declarations, so `.adt` has
no type arguments. `.arraySizeOf elem sizedTy` represents
`[elem; size_of::<sizedTy>()]` whose length is evaluated symbolically against
`sizedTy`'s layout. `.unmodeled` is the bounded leaf fallback for `rustc`
type-checker internal types (`Dynamic`, `Alias`, `Coroutine`, `Closure`, `Pat`,
`UnsafeBinder`, `Bound`, `Placeholder`, `Foreign`) and has no size or valid
values in `Trusted/MirSemantics.lean`. -/
inductive MirTy where
  | usize
  | isize
  | uint (bits : Nat)
  | int (bits : Nat)
  | float (bits : Nat)
  | bool
  | char
  | str
  | unit
  | never
  | adt (id : Nat)
  | param (idx : Nat)
  | ref (inner : MirTy)
  | refMut (inner : MirTy)
  | rawPtr (inner : MirTy) (mutable : Bool)
  | array (elem : MirTy) (len : Nat)
  | arraySizeOf (elem : MirTy) (sizedTy : MirTy)
  | slice (elem : MirTy)
  | tuple (elems : List MirTy)
  | fnDef (name : String)
  | fnPtr
  | unmodeled

/-- Single projection step along a `Place` path
(`rustc_middle::mir::ProjectionElem`,
`compiler/rustc_middle/src/mir/syntax.rs#L1192-L1283`):
- `.deref`: dereference a reference or pointer (`*p`).
- `.field idx`: project field `idx` (`p.idx`).
- `.index loc`: index into an array or slice by local `loc` (`p[loc]`).
- `.constantIndex`: endpoint-relative slice/array pattern index.
- `.subslice`: slice pattern subrange.
- `.downcast variantIdx`: narrow an enum or coroutine place to `variantIdx`.
- `.opaqueCast ty`: cast an opaque type in place.
- `.unwrapUnsafeBinder ty`: project out of an unsafe binder. -/
inductive PlaceElem where
  | deref
  | field (idx : Nat)
  | index (loc : LocalId)
  | constantIndex (offset : Nat) (minLength : Nat) (fromEnd : Bool)
  | subslice (fromIdx : Nat) (toIdx : Nat) (fromEnd : Bool)
  | downcast (variantIdx : Nat)
  | opaqueCast (ty : MirTy)
  | unwrapUnsafeBinder (ty : MirTy)

/-- Memory location path rooted at a `LocalId` followed by a sequence of
projections (`rustc_middle::mir::Place`,
`compiler/rustc_middle/src/mir/syntax.rs#L1168-L1187`):
> "A `Place` represents a memory location: a local variable together with a
> list of projections (field accesses, dereferences, indexing, etc.)." -/
structure Place where
  loc : LocalId
  projection : List PlaceElem := []

/-- Whether safe code outside the defining module may name a struct field in a
struct expression (`compiler/rustc_middle/src/ty/adt.rs#L114-L120`):
> "Visibility of the field (mostly matters for structs)."

The only question the semantics asks of a field is whether downstream safe
code can construct the struct from arbitrary field values
(`AdtDecl.allFieldsPubSafe`). A field that is not public, and a field declared
`unsafe` under the unstable `feature(unsafe_fields)`, both prevent that, so
the capture emits `.priv` for both. -/
inductive FieldAccess where
  | pubSafe
  | priv

/-- Single field declaration inside an ADT (`rustc_middle::ty::FieldDef`,
`compiler/rustc_middle/src/ty/adt.rs#L108-L121`). -/
structure FieldDecl where
  ty : MirTy
  access : FieldAccess

/-- First-order representation invariant of a single-`usize`-field struct
(`/// anneal:invariant <field> != <ne>`): the field is not equal to `ne`. -/
structure InvariantSpec where
  ne : Nat

/-- Layout representation attribute on an `AdtDecl`
(`src/type-layout.md#L180-L530`, `compiler/rustc_abi/src/repr.rs#L535-L600`):
- `.rust`: default `#[repr(Rust)]` layout (`r[layout.repr.rust]`), whose field
  order and non-negative inter-field/trailing padding (`MirState.adtPad`) are
  unspecified across compiler versions except that fieldless/all-ZST structs
  have size `0` (`r[layout.repr.rust.struct-zst]`) and non-ZST structs have size
  at least `alignUp sumFieldSizes maxKnownAlign`.
- `.transparent`: `#[repr(transparent)]` (`r[layout.repr.transparent]`),
  guaranteed to have the exact size, alignment, and valid bit patterns of its
  sole non-zero-sized field alongside any 1-ZST fields.
- `.c`: `#[repr(C)]` (`r[layout.repr.c.struct]`), using the deterministic C ABI
  declaration-order offset algorithm when all field alignments are known.
- `.unmodeled`: structs carrying `#[repr(align(N))]`, `#[repr(packed(N))]`, or
  other unmodeled layout modifiers, which fail closed on layout and validity
  queries. -/
inductive AdtRepr where
  | rust
  | transparent
  | c
  | unmodeled

/-- Captured ADT (struct) declaration (`rustc_middle::ty::AdtDefData`,
`compiler/rustc_middle/src/ty/adt.rs#L140-L176`). -/
structure AdtDecl where
  id : Nat
  fields : List FieldDecl
  repr : AdtRepr := .rust
  invariant : Option InvariantSpec := none

/-- Whether safe downstream code can construct the struct directly with a
struct expression (`r[expr.struct.safety]`,
`src/expressions/struct-expr.md#L58-L65`):
> "A struct expression can only be used if all fields are visible in the current
> scope, and the struct is not marked `#[non_exhaustive]` in another crate."

`#[non_exhaustive]` is not recorded. Ignoring it can only make this function
return `true` where Rust would forbid construction, which makes
`AdmissibleAdtInv` demand more of the invariant, never less. -/
def AdtDecl.allFieldsPubSafe (decl : AdtDecl) : Bool :=
  decl.fields.all (fun f =>
    match f.access with
    | .pubSafe => true
    | .priv => false)

/-- The type of the single value that a 1-field `MirVal.adt` of this struct
carries. -/
def AdtDecl.payloadTy (decl : AdtDecl) : Option MirTy :=
  match decl.fields with
  | [f] => some f.ty
  | _ => none

/-- Runtime value (`src/behavior-considered-undefined.md#L114-L132`):
> "The Rust compiler assumes that all values produced during program execution
> are 'valid', and producing an invalid value is hence immediate UB."

- `.uninit`: an uninitialized sub-value written by a partial move out of a
  projected place (`Operand.move`); reading any value containing `.uninit` is
  undefined behavior (`MirVal.isFullyInit`).
- `.adt id inner`: a struct value carrying `.unit` for a fieldless struct, the
  single field value for a 1-field struct, or a right-nested `.fieldCons` spine
  for a multi-field struct.
- `.fieldCons head tail`: right-nested field spine for multi-field structs and
  tuples.
- `.bytes sz bits`: an `sz`-byte value for a generic parameter type or byte
  array (`[u8; sz]`).
- `.ref frameId gen loc fieldDepth`: a shared reference to `fieldDepth` nested
  `.field 0` projections of local `loc` of the activation with identifier
  `frameId`, valid only while that local's storage generation is still `gen`
  (see `resolveRef`). -/
inductive MirVal where
  | uninit
  | usize (bits : Nat)
  | bool (b : Bool)
  | unit
  | adt (id : Nat) (inner : MirVal)
  | fieldCons (head : MirVal) (tail : MirVal)
  | bytes (sz : Nat) (bits : Nat)
  | ref (frameId : Nat) (gen : Nat) (loc : LocalId) (fieldDepth : Nat := 0)

/-- Session runtime-check flag queried by `Operand.runtimeChecks`
(`rustc_middle::mir::RuntimeChecks`,
`compiler/rustc_middle/src/mir/syntax.rs#L1579-L1589`). -/
inductive RuntimeChecks where
  | ubChecks
  | contractChecks
  | overflowChecks

/-- MIR operand (`rustc_middle::mir::Operand`,
`compiler/rustc_middle/src/mir/syntax.rs#L1303-L1335`):
> "Creates a value by loading the given place."
> "This *may* additionally overwrite the place with `uninit` bytes..."

`constVal` accepts any `MirVal` syntactically, but evaluation admits only
reference-free scalars (see `evalOperand`). -/
inductive Operand where
  | copy (src : Place)
  | move (src : Place)
  | constVal (val : MirVal)
  | runtimeChecks (chk : RuntimeChecks)

/-- Raw pointer mutability flavor on `Rvalue.rawPtr`
(`rustc_middle::mir::RawPtrKind`,
`compiler/rustc_middle/src/mir/syntax.rs#L180-L192`). -/
inductive RawPtrKind where
  | mut_
  | const_
  | fakeForPtrMetadata

/-- Cast kind on `Rvalue.cast` (`rustc_middle::mir::CastKind`,
`compiler/rustc_middle/src/mir/syntax.rs#L1491-L1532`). -/
inductive CastKind where
  | pointerExposeProvenance
  | pointerWithExposedProvenance
  | pointerCoercion
  | intToInt
  | floatToInt
  | floatToFloat
  | intToFloat
  | ptrToPtr
  | fnPtrToPtr
  | transmute (srcTy : MirTy := .unmodeled)
  | subtype

/-- Unary operator on `Rvalue.unaryOp` (`rustc_middle::mir::UnOp`,
`compiler/rustc_middle/src/mir/syntax.rs#L1603-L1617`). -/
inductive UnOp where
  | not
  | neg
  | ptrMetadata

/-- Binary operator on `Rvalue.binaryOp` (`rustc_middle::mir::BinOp`,
`compiler/rustc_middle/src/mir/syntax.rs#L1621-L1709`). -/
inductive BinOp where
  | add
  | addUnchecked
  | addWithOverflow
  | sub
  | subUnchecked
  | subWithOverflow
  | mul
  | mulUnchecked
  | mulWithOverflow
  | div
  | rem
  | bitXor
  | bitAnd
  | bitOr
  | shl
  | shlUnchecked
  | shr
  | shrUnchecked
  | eq
  | lt
  | le
  | ne
  | ge
  | gt
  | cmp
  | offset

/-- Right-hand side value computation (`rustc_middle::mir::Rvalue`,
`compiler/rustc_middle/src/mir/syntax.rs#L1363-L1488`):
> "Yields the operand unchanged, except for a potential retag."
> "Creates a reference of the indicated kind to the place." -/
inductive Rvalue where
  | use (op : Operand)
  | repeat (op : Operand) (len : Nat)
  | repeatSizeOf (op : Operand) (sizedTy : MirTy)
  | ref (src : Place)
  | refMut (src : Place)
  | refFake (src : Place)
  | threadLocalRef (defId : Nat)
  | rawPtr (kind : RawPtrKind) (src : Place)
  | cast (kind : CastKind) (op : Operand) (ty : MirTy)
  | binaryOp (op : BinOp) (lhs : Operand) (rhs : Operand)
  | unaryOp (op : UnOp) (opnd : Operand)
  | discriminant (src : Place)
  | aggregate (adtId : Nat) (op : Operand)
  | aggregateFields (ops : List Operand) (adtId : Option Nat := none)
  | copyForDeref (src : Place)
  | wrapUnsafeBinder (op : Operand) (ty : MirTy)
  | reborrow (ty : MirTy) (mutable : Bool) (src : Place)

/-- Non-diverging intrinsic statement payload
(`rustc_middle::mir::NonDivergingIntrinsic`,
`compiler/rustc_middle/src/mir/syntax.rs#L469-L492`). -/
inductive NonDivergingIntrinsic where
  | assume (op : Operand)
  | copyNonOverlapping (src : Operand) (dst : Operand) (count : Operand)

/-- Sequential statement inside a MIR basic block
(`rustc_middle::mir::StatementKind`,
`compiler/rustc_middle/src/mir/syntax.rs#L305-L456`):
> "`StorageLive` and `StorageDead` statements mark the live range of a local."
> "`PlaceMention` evaluates the `Place` without reading its value." -/
inductive Stmt where
  | assign (dst : Place) (rv : Rvalue)
  | evalConst (dst : Place) (constId : BodyId) (typeArgs : List MirTy := [])
  | fakeRead (place : Place)
  | setDiscriminant (place : Place) (variantIdx : Nat)
  | storageLive (loc : LocalId)
  | storageDead (loc : LocalId)
  | placeMention (place : Place)
  | ascribeUserType (place : Place)
  | coverage
  | intrinsic (intr : NonDivergingIntrinsic)
  | constEvalCounter
  | nop
  | backwardIncompatibleDropHint (place : Place)

/-- Failure action of a `Terminator.assert` check
(`rustc_middle::mir::TerminatorKind::Assert`,
`compiler/rustc_middle/src/mir/syntax.rs#L735-L751`):
- `.unwind`: normal unwinding assertion (`UnwindAction::Continue` or
  `UnwindAction::Cleanup`).
- `.abort`: process-aborting assertion without unwinding
  (`UnwindAction::Terminate`).
- `.ub`: compiler-inserted undefined-behavior check
  (`MisalignedPointerDereference`, `NullPointerDereference`,
  `InvalidEnumConstruction`, or `UnwindAction::Unreachable` from
  `core::ub_checks` `panic_nounwind`). -/
inductive AssertFailKind where
  | unwind
  | abort
  | ub

/-- Compile-time or runtime layout query lowered from `TerminatorKind::Call`
(`core::mem::size_of`, `core::mem::align_of`, `core::intrinsics::offset_of`,
`library/core/src/mem/mod.rs#L308-L355`,
`library/core/src/intrinsics/mod.rs#L2985-L2995`). -/
inductive LayoutQuery where
  | sizeOf (ty : MirTy)
  | alignOf (ty : MirTy)
  | offsetOf (containerTy : MirTy) (variantIdx : Nat) (fieldIdx : Nat)

/-- Control-flow transfer at the end of a MIR basic block
(`rustc_middle::mir::TerminatorKind`,
`compiler/rustc_middle/src/mir/syntax.rs#L692-L981`):
> "Block has one successor; we continue execution there."
> "Returns from the function."
> "Indicates a terminator that can never be reached. Executing this terminator
> is UB."
> "Jumps to `target` if `cond` equals `expected`, otherwise panics."

In `call1`, `callee` is the `BodyId` of the callee's generic body in
`Crate.bodies` and `typeArgs` are its type arguments, written in the caller's
own parameter space. -/
inductive Terminator where
  | return_
  | goto (target : BlockId)
  | unreachable
  | panic (hasCleanup : Bool := false)
  | unwindResume
  | unwindTerminate
  | drop (place : Place) (target : BlockId)
  | assert (cond : Operand) (expected : Bool) (target : BlockId)
      (onFail : AssertFailKind := .unwind) (hasCleanup : Bool := false)
  | switchInt (discr : Operand) (falseTarget : BlockId) (trueTarget : BlockId)
  | switchIntGeneral (discr : Operand) (targets : List (Nat × BlockId))
      (otherwise : BlockId)
  | callLayout (dst : Place) (query : LayoutQuery) (target : BlockId)
  | callTransmuteCopy (dst : Place) (srcTy dstTy : MirTy) (op : Operand)
      (target : BlockId)
  | call1 (dst : Place) (callee : BodyId) (arg : Operand)
      (target : BlockId) (typeArgs : List MirTy := [])
  | call (dst : Place) (args : List Operand) (target : Option BlockId)
  | tailCall (args : List Operand)
  | yield (val : Operand) (resume : BlockId) (resumeArg : Place)
  | coroutineDrop
  | falseEdge (realTarget : BlockId) (imaginaryTarget : BlockId)
  | falseUnwind (realTarget : BlockId)
  | inlineAsm

/-- Shorthand for `Terminator.callLayout dst (.sizeOf ty) target`. -/
abbrev Terminator.callSizeOf (dst : Place) (ty : MirTy)
    (target : BlockId) : Terminator :=
  .callLayout dst (.sizeOf ty) target

/-- Basic block (`rustc_middle::mir::BasicBlockData`,
`compiler/rustc_middle/src/mir/mod.rs#L207-L209`). -/
structure BasicBlock where
  stmts : List Stmt
  terminator : Terminator

/-- Lowered `Runtime(PostCleanup)` MIR body (`rustc_middle::mir::Body`,
`compiler/rustc_middle/src/mir/mod.rs#L204-L285`,
`compiler/rustc_monomorphize/src/collector.rs#L1185-L1207`):
> "Constants that are required to evaluate successfully for this `Body` to be
> well-formed. Wait until monomorphization to evaluate them."

Each required constant in `requiredConsts` names a zero-argument generic body in
`Crate.bodies` by its `BodyId`, paired with its type arguments in this body's
parameter space. Each entry in `requiredLayouts` records a local or signature
type whose layout (`evalTyByteSize` ≤ `isize::MAX`) must be admitted at
monomorphization time. -/
structure MirBody where
  argTys : List MirTy
  retTy : MirTy
  localCount : Nat
  blocks : List BasicBlock
  requiredConsts : List (BodyId × List MirTy) := []
  requiredLayouts : List MirTy := []

/-- Entry in `Crate.bodies` associating a `BodyId` with its `MirBody`.
When `isTransparentDep = true`, `body` is a cross-crate dependency body whose
MIR implementation is transparently inlined, generating a
`TCBItem.transparentDepBody` ledger entry in `CapturedFn.obligations`. -/
structure BodyDecl where
  id : BodyId
  body : MirBody
  isTransparentDep : Bool := false

/-- First-order precondition clause (`/// anneal:requires <arg> != <ne>`):
argument local `argLocal` (`usize`) is not equal to `ne`.

On an `unsafe fn` (`CapturedFn.isUnsafe = true`), `requires` states the
function's `# Safety` precondition, which callers must establish and which both
baseline safety (`SafetyPre`) and functional specifications (`ContractPost`) may
assume. On a safe function (`CapturedFn.isUnsafe = false`), `requires` narrows
only the domain of `/// anneal:spec` postconditions (`ContractPost`); baseline
safety (`SafetyPre`) does not assume `requires`, because safe callers are not
obligated to establish Anneal preconditions at call sites. -/
structure RequiresSpec where
  argLocal : Nat
  ne : Nat

/-- First-order user specification (`/// anneal:spec ensures(ret == <arg>)`) on
a captured function. -/
inductive PostSpec where
  | ensuresEqArg (argLocal : Nat)

/-- Identifier of a function-body behavioral verification obligation in
`CrateTheorem`.

An obligation `ObligationId.fnBody fnName` is waived only if it appears in
`Crate.tcbWaivedIds` (populated from `/// anneal:trusted` waivers and verified
by `cargo-anneal` to match `anneal-tcb.lock` in a 1-to-1 bijection). Unwaivable
structural and contract well-formedness obligations (`AdmissibleAdtInv` and
`FnContractWellFormed`) sit outside `VerificationResult` so they can never be
waived. -/
inductive ObligationId where
  | fnBody (fnName : String)

/-- Identifier of an obligation or coupling entry in a crate's verification
ledger (`Crate.tcb`):

- `rustcLowering fnName bodyId`: `rustc` correctly compiles the body at
  `bodyId` (Tier S0 baseline lowering assumption).
- `fnVerified fnName bodyId`: the body at `bodyId` satisfies its specifications
  on all admitted layouts and execution environments. Never waivable in
  `defaultTrustPolicy`.
- `compileTimeGuard fnName bodyId`: Tier S1 compilation-stability coupling for a
  function whose soundness relies on a dominating `const` assertion or static
  `transmute` size check rejecting non-zero `#[repr(Rust)]` struct padding on a
  future compiler (`NoCompileTimeError`).
- `transparentDepBody fnName calleeId`: Tier S1 SemVer compilation-stability
  coupling when `fnName` transparently verifies against cross-crate dependency
  body `calleeId`.
- `documentedIntent fnName bodyId rationale`: Tier S2 reliance on documented
  pre-normative upstream intent.
- `pinnedCompilerCoupled fnName bodyId reason`: Tier S3 soundness coupling
  restricting verification of `fnName` to the pinned compiler's zero-padding
  layout (`s.adtPad = fun _ => 0`). -/
inductive TCBItem where
  | rustcLowering (fnName : String) (bodyId : BodyId)
  | fnVerified (fnName : String) (bodyId : BodyId)
  | compileTimeGuard (fnName : String) (bodyId : BodyId)
  | transparentDepBody (fnName : String) (calleeId : BodyId)
  | documentedIntent (fnName : String) (bodyId : BodyId) (rationale : String)
  | pinnedCompilerCoupled (fnName : String) (bodyId : BodyId) (reason : String)

/-- Captured MIR function descriptor.

- `bodyId`: crate-local `BodyId` of the primary (`--release`) lowered MIR body.
- `debugBodyId`: optional `BodyId` of the `--debug` lowered MIR body when the
  debug compilation profile produces a distinct MIR body from `--release`.
- `isUnsafe`: whether the function is declared `unsafe fn`, determining whether
  `requires` enters `SafetyPre` or only qualifies `ContractPost`.
- `requires`: optional `/// anneal:requires` precondition clause.
- `specs`: list of `/// anneal:spec` postcondition clauses. -/
structure CapturedFn where
  name : String
  bodyId : BodyId
  debugBodyId : Option BodyId := none
  isUnsafe : Bool := false
  requires : Option RequiresSpec := none
  specs : List PostSpec := []

/-- Captured Rust crate. Every field is first-order syntax data;
`Trusted/MirSemantics.lean` denotes `adts`, `bodies`, `functions`, `tcb`,
`tcbWaivedIds`, and `target` to state `Trusted.CrateTheorem`. -/
structure Crate where
  adts : List AdtDecl := []
  bodies : List BodyDecl := []
  functions : List CapturedFn
  tcb : List TCBItem := []
  tcbWaivedIds : List ObligationId := []
  target : TargetLayout := defaultTargetLayout

end Trusted
-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_semantics

/-!
# Trusted MIR Semantics and Crate Theorem (`Trusted/MirSemantics.lean`)

Defines the small-step operational semantics `MirSem` for `Trusted/MirAst.lean`,
in-order compile-time constant evaluation (`Stmt.evalConst`), target-aware and
forward-compatible type layout (`tyLayoutStep`, `evalTyByteSize`, `evalTyAlign`,
`evalLayoutQuery`), static body well-formedness (`LocalLayoutsAdmitted`,
`StaticBodyWf`), Post-Monomorphization Error (PME) admission (`RequiresConst`,
`ConstSucceeds`, `ConstUnwinds`, `ConstsTotal`, `MonoAdmitted`, `MonoConstsWf`,
`ContractWellFormed`), the library representation invariant and API boundary
contract (`AdtInv`, `denoteAdtInv`, `MirVal.valid`, `AdmissibleAdtInv`,
`SafetyPre`, `SafetyPost`, `ContractPost`, `EffectivePost`, `FnBodyVerified`),
and the top-level crate verification obligation `Trusted.CrateTheorem`
(`rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b` and
`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`; citations marked
`rustc@f8a08b68` are to
`rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, the commit of the
pinned `rustc 1.98.0-nightly (f8a08b688 2026-05-30)`).

## Reading guide

The semantics has two notions of "well-typed", and only two:

- **Type well-formedness** (`evalTyByteSize`, `MirTy.wfInAdts`,
  `LocalLayoutsAdmitted`): the model can measure the type within target bounds
  (`≤ isizeMaxBytes`). Every unmodeled shape (`MirTy.unmodeled`, unmodeled
  primitive/pointer/composite types, an undeclared ADT, an ADT with
  `AdtRepr.unmodeled`, a cycle of struct declarations, or an overflowing array
  layout) is ill formed.
- **Value validity** (`MirVal.valid`): a value is valid at a type in a given
  state. It is the only validity relation; function entry, function return,
  and `AdmissibleAdtInv` all use it.

Every model limit fails closed. During execution a limit makes the step
`.failed` (undefined behavior, so the function cannot be verified). At the
static boundary, `StaticBodyWf` (`MirLang.wf`) and `ContractWellFormed`
reject ill-formed bodies, unmodeled or overflowing layouts, and dead-on-arrival
post-monomorphization errors before any behavioral obligation is discharged.

## Forward-compatible layout and compile-time guards

Rust's default `#[repr(Rust)]` representation makes no stability guarantee on
field ordering or padding (`src/type-layout.md#L47-L56`):
> "The default representation of nominal types is called the `Rust`
> representation... In other words, the data layout is undefined."

By contrast, `#[repr(C)]` (`src/type-layout.md#L127-L162`) and
`#[repr(transparent)]` (`src/type-layout.md#L211-L234`) have language-specified
layouts. Each execution state `MirState` therefore carries `adtPad : Nat → Nat`:
for `AdtRepr.c` and `AdtRepr.transparent`, layout is deterministic across all
`adtPad` worlds, whereas for `AdtRepr.rust`, `adtPad id` adds an arbitrary
non-negative byte count of compiler-chosen padding to struct `id`. A proof that
holds for all initial states therefore holds across all valid `#[repr(Rust)]`
padding choices unless the code either uses `#[repr(C)]`/`#[repr(transparent)]`,
executes an in-order `Stmt.evalConst` layout guard (which terminates with
`.compileTimeError` on rejected layout worlds and surfaces
`TCBItem.compileTimeGuard`), or carries an explicit
`TCBItem.pinnedCompilerCoupled` waiver.

Generic code is verified once for all instantiations. A generic function's
type parameters stay abstract: values of parameter type are opaque bytes
(`MirVal.bytes`) that are never reinterpreted as integers, so `transmute_copy`
into or out of a bare type parameter is undefined behavior in the model. A call
to a generic callee looks up its `BodyId` in `Crate.bodies` and substitutes its
type arguments into the callee body (`MirBody.subst`), so every `.param` the
semantics reads refers to the root function's parameters, whose sizes are
`MirState.tySizes`.
-/

namespace Trusted

/-- Saved caller activation frame pushed onto `MirState.stack` by a static
`Terminator.call1` and popped by the callee's `Terminator.return_`.

`tySizes` and `adtPad` are not saved: instantiation by substitution keeps every
frame in the root function's parameter and layout space, so `MirState.tySizes`
and `MirState.adtPad` never change during an execution. -/
structure StackFrame where
  callerBody : MirBody
  callerLocals : Nat → Option MirVal
  callerLocalGens : Nat → Nat
  retDst : Place
  retBlock : Nat
  callerFrameId : Nat

/-- Instantaneous execution state of a `MirBody`.

- `locals`/`localGens`: the active frame's locals and, for each local, a
  storage generation that `StorageLive`/`StorageDead` increment. A reference
  records the generation it was created at, so a reference that outlives its
  referent's storage no longer resolves (`resolveRef`).
- `tySizes`: the byte size of each type parameter of the root function.
- `curBody`/`stack`: the active callee body (`none` at the root) and the saved
  caller frames.
- `frameId`/`nextFrameId`: monotonic activation identifiers. Every
  `Terminator.call1` takes a fresh identifier, so a reference into a returned
  activation can never resolve against a later sibling activation. The root
  activation is frame `0`; a caller-owned referent of the root function is a
  frame-`0` local at an index at or above the root's `localCount`.
- `adtPad`: non-negative compiler-chosen extra padding bytes for each
  `AdtRepr.rust` struct declaration `id`.
- `ubChecks`: nondeterministic boolean value yielded by
  `Operand.runtimeChecks .ubChecks` (`core::intrinsics::ub_checks()`).

The defaults exist for writing concrete states; `initEntryState` pins every
structural control field while leaving `tySizes`, `adtPad`, and `ubChecks`
universally quantified across initial states. -/
structure MirState where
  locals : Nat → Option MirVal
  localGens : Nat → Nat := fun _ => 0
  block : Nat
  stmtIdx : Nat
  tySizes : Nat → Nat := fun _ => 0
  curBody : Option MirBody := none
  stack : List StackFrame := []
  frameId : Nat := 0
  nextFrameId : Nat := 1
  adtPad : Nat → Nat := fun _ => 0
  ubChecks : Bool := true

/-- Result of a normal return from the root function: the returned value and
the terminal state at `Terminator.return_`.

The terminal state is part of the outcome so that postconditions about
returned references (`SafetyPost`) read the referents as they are when
the function returns, not as they were when it was called. -/
structure MirReturn where
  value : MirVal
  state : MirState

/-- Update local slot `target` in `locals`. -/
def updateLocal (locals : Nat → Option MirVal) (target : Nat)
    (val : Option MirVal) : Nat → Option MirVal :=
  fun i => if i == target then val else locals i

/-- Increment the storage-liveness generation counter of local `target`. -/
def bumpGen (gens : Nat → Nat) (target : Nat) : Nat → Nat :=
  fun i => if i == target then gens i + 1 else gens i

/-- Look up element `idx` in `xs`. -/
def lookupAt {α : Type} (xs : List α) (idx : Nat) : Option α :=
  xs.foldr
    (fun x ih n =>
      match n with
      | 0 => some x
      | i + 1 => ih i)
    (fun _ => none)
    idx

/-- Apply `f` to every element of `xs`, succeeding only if every application
succeeds. -/
def mapAll {α β : Type} (f : α → Option β) (xs : List α) : Option (List β) :=
  xs.foldr (fun x acc => (f x).bind fun y => acc.map (y :: ·)) (some [])

/-- Look up an `AdtDecl` by its crate-local identifier `id`. -/
def findAdtDecl (adts : List AdtDecl) (id : Nat) : Option AdtDecl :=
  adts.find? (fun d => d.id == id)

/-- Look up a `MirBody` by its crate-local `BodyId` in `bodies`. -/
def findBody (bodies : List BodyDecl) (id : BodyId) : Option MirBody :=
  (bodies.find? (fun d => d.id.index == id.index)).map BodyDecl.body

/-! ## Instantiating generic bodies -/

/-- Substitute type arguments for type parameters: `.param idx` becomes
`typeArgs[idx]`.

The type arguments are written in the caller's parameter space, so the result
is in the caller's parameter space too; nothing is left in the callee's. A
parameter with no corresponding argument or an unmodeled type constructor makes
substitution fail (`none`), and every user of `subst` treats failure as
undefined behavior, so an arity mismatch or unmodeled type can never leave a
callee parameter to be misread as a caller parameter. -/
def MirTy.subst (typeArgs : List MirTy) : MirTy → Option MirTy
  | .usize => some .usize
  | .isize => some .isize
  | .uint w => some (.uint w)
  | .int w => some (.int w)
  | .bool => some .bool
  | .char => some .char
  | .unit => some .unit
  | .adt id => some (.adt id)
  | .param idx => lookupAt typeArgs idx
  | .ref inner => (inner.subst typeArgs).map .ref
  | .rawPtr inner m => (inner.subst typeArgs).map (MirTy.rawPtr · m)
  | .array elem len => (elem.subst typeArgs).map (MirTy.array · len)
  | .arraySizeOf elem sizedTy =>
    (elem.subst typeArgs).bind fun elem' =>
      (sizedTy.subst typeArgs).map (MirTy.arraySizeOf elem')
  | .float _ | .str | .never | .refMut _ | .slice _ | .tuple _
  | .fnDef _ | .fnPtr | .unmodeled => none

/-- Substitute type arguments into a `LayoutQuery`. -/
def LayoutQuery.subst (typeArgs : List MirTy) :
    LayoutQuery → Option LayoutQuery
  | .sizeOf ty => (ty.subst typeArgs).map .sizeOf
  | .alignOf ty => (ty.subst typeArgs).map .alignOf
  | .offsetOf ty varIdx fieldIdx =>
    (ty.subst typeArgs).map (LayoutQuery.offsetOf · varIdx fieldIdx)

/-- Substitute type arguments into every type in an `Rvalue`, failing (`none`)
on unmodeled rvalues. -/
def Rvalue.subst (typeArgs : List MirTy) : Rvalue → Option Rvalue
  | .use op => some (.use op)
  | .repeat op len => some (.repeat op len)
  | .repeatSizeOf op sizedTy =>
    (sizedTy.subst typeArgs).map (.repeatSizeOf op)
  | .ref src => some (.ref src)
  | .rawPtr m src => some (.rawPtr m src)
  | .cast (.transmute srcTy) op dstTy =>
    (srcTy.subst typeArgs).bind fun srcTy' =>
      (dstTy.subst typeArgs).map fun dstTy' =>
        .cast (.transmute srcTy') op dstTy'
  | .cast kind op dstTy =>
    (dstTy.subst typeArgs).map (.cast kind op)
  | .binaryOp op lhs rhs => some (.binaryOp op lhs rhs)
  | .unaryOp op src => some (.unaryOp op src)
  | .aggregate adtId op => some (.aggregate adtId op)
  | .aggregateFields ops adtId => some (.aggregateFields ops adtId)
  | .refMut _ | .refFake _ | .threadLocalRef _ | .discriminant _
  | .copyForDeref _ | .wrapUnsafeBinder _ _ | .reborrow _ _ _ => none

/-- Substitute type arguments into a `Stmt`, failing (`none`) on unmodeled
statements. -/
def Stmt.subst (typeArgs : List MirTy) : Stmt → Option Stmt
  | .assign dst rv => (rv.subst typeArgs).map (.assign dst)
  | .evalConst dst constId calleeTypeArgs =>
    (mapAll (MirTy.subst typeArgs) calleeTypeArgs).map
      (fun tys => .evalConst dst constId tys)
  | .placeMention p => some (.placeMention p)
  | .storageLive loc => some (.storageLive loc)
  | .storageDead loc => some (.storageDead loc)
  | .nop => some .nop
  | .constEvalCounter => some .constEvalCounter
  | .setDiscriminant _ _ | .fakeRead _ | .ascribeUserType _
  | .intrinsic _ | .coverage | .backwardIncompatibleDropHint _ => none

/-- Substitute type arguments into every type in a `Terminator`, failing
(`none`) on unmodeled terminators.

The `callee` of a nested `call1` is a `BodyId` referencing a closed generic
body in `Crate.bodies`, whose own parameters are bound by that call's
`typeArgs`; only those `typeArgs` are substituted here. -/
def Terminator.subst (typeArgs : List MirTy) :
    Terminator → Option Terminator
  | .return_ => some .return_
  | .goto target => some (.goto target)
  | .unreachable => some .unreachable
  | .panic hasCleanup => some (.panic hasCleanup)
  | .assert cond expected target onFail hasCleanup =>
    some (.assert cond expected target onFail hasCleanup)
  | .switchInt discr f t => some (.switchInt discr f t)
  | .callLayout dst query target =>
    (query.subst typeArgs).map fun q' => .callLayout dst q' target
  | .callTransmuteCopy dst srcTy dstTy op target =>
    (srcTy.subst typeArgs).bind fun srcTy' =>
      (dstTy.subst typeArgs).map fun dstTy' =>
        .callTransmuteCopy dst srcTy' dstTy' op target
  | .call1 dst callee arg target calleeTypeArgs =>
    (mapAll (MirTy.subst typeArgs) calleeTypeArgs).map fun calleeTypeArgs' =>
      .call1 dst callee arg target calleeTypeArgs'
  | .unwindResume | .unwindTerminate | .drop _ _
  | .switchIntGeneral _ _ _ | .call _ _ _ | .tailCall _
  | .yield _ _ _ | .coroutineDrop | .falseEdge _ _
  | .falseUnwind _ | .inlineAsm => none

/-- Substitute type arguments into a `BasicBlock`. -/
def BasicBlock.subst (typeArgs : List MirTy)
    (bb : BasicBlock) : Option BasicBlock :=
  (mapAll (Stmt.subst typeArgs) bb.stmts).bind fun stmts =>
    (bb.terminator.subst typeArgs).map fun term =>
      { stmts := stmts, terminator := term }

/-- Instantiate a generic body with `typeArgs`, written in the caller's
parameter space. This is the only way the semantics instantiates generics.

As in `Terminator.subst`, required constants are referenced by `BodyId`; only
their type-argument lists and `requiredLayouts` are substituted. -/
def MirBody.subst (typeArgs : List MirTy)
    (b : MirBody) : Option MirBody :=
  (mapAll (MirTy.subst typeArgs) b.argTys).bind fun argTys =>
  (b.retTy.subst typeArgs).bind fun retTy =>
  (mapAll (BasicBlock.subst typeArgs) b.blocks).bind fun blocks =>
  (mapAll (fun (rc : BodyId × List MirTy) =>
      (mapAll (MirTy.subst typeArgs) rc.2).map fun rcArgs => (rc.1, rcArgs))
    b.requiredConsts).bind fun requiredConsts =>
  (mapAll (MirTy.subst typeArgs) b.requiredLayouts).map fun requiredLayouts =>
  { argTys := argTys
    retTy := retTy
    localCount := b.localCount
    blocks := blocks
    requiredConsts := requiredConsts
    requiredLayouts := requiredLayouts }

/-! ## Type well-formedness, size, alignment, and field offsets -/

/-- Maximum byte size of a Rust type on a 64-bit target (`isize::MAX`,
`2^63 - 1`, `compiler/rustc_abi/src/layout.rs#L50-L60`). -/
def isizeMaxBytes : Nat := 9223372036854775807

/-- Whether every type-parameter byte size in `tySizes` fits within the
target's maximum object size (`≤ isizeMaxBytes`). -/
def ValidTySizes (tySizes : Nat → Nat) : Prop :=
  ∀ idx, tySizes idx ≤ isizeMaxBytes

/-- Round `offset` up to the next multiple of `align` (`align ≥ 1`,
`compiler/rustc_abi/src/layout.rs#L1283-L1320`). -/
def alignUp (offset align : Nat) : Nat :=
  let rem := Nat.mod offset align
  if rem == 0 then offset else offset + (align - rem)

/-- Sequential `#[repr(C)]` field layout fold (`src/type-layout.md#L127-L162`):
> "The alignment of the struct is the alignment of the most-aligned field in
> it... For each field in declaration order in the struct, first determine the
> size and alignment of the field. If the current offset is not a multiple of
> the field's alignment, then add padding bytes to the current offset until it
> is a multiple of the field's alignment. The offset for the field is what the
> current offset is now. Then increase the current offset by the size of the
> field. Finally, the size of the struct is the current offset rounded up to the
> nearest multiple of the struct's alignment." -/
def foldReprCFields (unfold : MirTy → Option (Nat × Nat)) :
    List FieldDecl → Nat → Nat → Option (Nat × Nat)
  | [], offset, maxAlign =>
    some (alignUp offset maxAlign, maxAlign)
  | f :: rest, offset, maxAlign =>
    (unfold f.ty).bind fun (fSz, fAlign) =>
      let alignedOffset := alignUp offset fAlign
      foldReprCFields unfold rest (alignedOffset + fSz)
        (Nat.max maxAlign fAlign)

/-- Byte offset of field `targetIdx` inside a `#[repr(C)]` field list, failing
(`none`) if `targetIdx` is out of bounds or any field type is ill formed. -/
def reprCFieldOffset (unfold : MirTy → Option (Nat × Nat)) :
    List FieldDecl → Nat → Nat → Option Nat
  | [], _, _ => none
  | f :: rest, 0, offset =>
    (unfold f.ty).bind fun (fSz, fAlign) =>
      let alignedOffset := alignUp offset fAlign
      (foldReprCFields unfold rest (alignedOffset + fSz) fAlign).map
        fun _ => alignedOffset
  | f :: rest, idx + 1, offset =>
    (unfold f.ty).bind fun (fSz, fAlign) =>
      let alignedOffset := alignUp offset fAlign
      reprCFieldOffset unfold rest idx (alignedOffset + fSz)

/-- Boolean equality on `AdtRepr`. -/
def AdtRepr.beq : AdtRepr → AdtRepr → Bool
  | .rust, .rust => true
  | .transparent, .transparent => true
  | .c, .c => true
  | .unmodeled, .unmodeled => true
  | _, _ => false

instance : BEq AdtRepr := ⟨AdtRepr.beq⟩

/-- Whether `decl` has zero compiler-added padding in the current `adtPad`
world (either `#[repr(transparent)]`, or `#[repr(Rust)]` when
`adtPad decl.id == 0`). -/
def AdtDecl.isZeroPaddedWrapper (decl : AdtDecl)
    (adtPad : Nat → Nat) : Bool :=
  decl.repr == .transparent || (decl.repr == .rust && adtPad decl.id == 0)

/-- Byte width and alignment of an `n`-bit integer type (`u8`/`i8` through
`u128`/`i128`) under `target`. -/
def intBitWidthLayout (target : TargetLayout) (w : Nat) : Option (Nat × Nat) :=
  if w == 8 then some (1, 1)
  else if w == 16 then some (2, 2)
  else if w == 32 then some (4, 4)
  else if w == 64 then some (8, target.i64Align)
  else if w == 128 then some (16, target.i128Align)
  else none

/-- Byte size and alignment `(size, align)` of `ty`, allowing at most `fuel`
nested struct unfoldings:

- Primitive scalars follow `src/type-layout.md` ("Primitive Data Layout") and
  the captured `TargetLayout` (`ptrByteWidth`, `i64Align`, `i128Align`).
- Shared references and raw pointers to well-formed pointees have size and
  alignment `target.ptrByteWidth`.
- Fixed-length arrays `[T; N]` and `[T; size_of::<U>()]` have size
  `size(T) * N` (bounded by `isizeMaxBytes` for `[T; N]`) and alignment
  `align(T)` (`src/type-layout.md`, "Array Layout").
- `AdtRepr.c` and `AdtRepr.transparent` structs have deterministic layout;
  `AdtRepr.rust` structs add `adtPad id` non-negative compiler-chosen padding
  bytes (`src/type-layout.md`, "The `Rust` Representation"). -/
def tyLayoutStep (adts : List AdtDecl) (tySizes : Nat → Nat)
  (adtPad : Nat → Nat) (target : TargetLayout)
  (unfold : MirTy → Option (Nat × Nat)) : MirTy → Option (Nat × Nat)
  | .usize | .isize => some (target.ptrByteWidth, target.ptrByteWidth)
  | .uint w | .int w => intBitWidthLayout target w
  | .bool => some (1, 1)
  | .char => some (4, 4)
  | .unit => some (0, 1)
  | .param idx => some (tySizes idx, 1)
  | .ref inner | .rawPtr inner _ =>
    (tyLayoutStep adts tySizes adtPad target unfold inner).map
      fun _ => (target.ptrByteWidth, target.ptrByteWidth)
  | .array elem len =>
    (tyLayoutStep adts tySizes adtPad target unfold elem).bind
      fun (elemSz, elemAlign) =>
        let sz := elemSz * len
        if decide (sz ≤ isizeMaxBytes) then some (sz, elemAlign) else none
  | .arraySizeOf elem sizedTy =>
    (tyLayoutStep adts tySizes adtPad target unfold elem).bind
      fun (elemSz, elemAlign) =>
        (tyLayoutStep adts tySizes adtPad target unfold sizedTy).map
          fun (n, _) => (elemSz * n, elemAlign)
  | .adt id =>
    (findAdtDecl adts id).bind fun decl =>
      let baseLayout :=
        match decl.fields with
        | [f] => unfold f.ty
        | fields => foldReprCFields unfold fields 0 1
      match decl.repr with
      | .unmodeled => none
      | .transparent | .c => baseLayout
      | .rust => baseLayout.map fun (sz, al) => (adtPad id + sz, al)
  | _ => none

def tyLayoutFuel (adts : List AdtDecl) (tySizes : Nat → Nat)
    (adtPad : Nat → Nat := fun _ => 0)
    (target : TargetLayout := defaultTargetLayout) :
    Nat → MirTy → Option (Nat × Nat)
  | 0, _ => none
  | fuel + 1, ty =>
    tyLayoutStep adts tySizes adtPad target
      (tyLayoutFuel adts tySizes adtPad target fuel) ty

/-- Byte size of a `MirTy` under `adts`, `tySizes`, `adtPad`, and `target`
(`core::mem::size_of`, `src/type-layout.md#L16-L18`):
> "The size of a value is the offset in bytes between successive elements in an
> array with that item type including alignment padding."

The fuel `adts.length + 1` suffices for every acyclic set of declarations: a
chain of nested unfoldings visits distinct declarations, and there are at most
`adts.length` of them. A struct that contains itself (possible in Rust only
behind a reference, such as `struct Node { next: &'static Node }`) exhausts
the fuel, so its size is `none` and it is ill formed. -/
def evalTyByteSize (adts : List AdtDecl) (tySizes : Nat → Nat)
    (ty : MirTy) (adtPad : Nat → Nat := fun _ => 0)
    (target : TargetLayout := defaultTargetLayout) : Option Nat :=
  (tyLayoutFuel adts tySizes adtPad target (adts.length + 1) ty).map Prod.fst

/-- Byte alignment of a `MirTy` under `adts`, `tySizes`, `adtPad`, and `target`
(`core::mem::align_of`, `src/type-layout.md#L20-L24`). -/
def evalTyAlign (adts : List AdtDecl) (tySizes : Nat → Nat)
    (ty : MirTy) (adtPad : Nat → Nat := fun _ => 0)
    (target : TargetLayout := defaultTargetLayout) : Option Nat :=
  (tyLayoutFuel adts tySizes adtPad target (adts.length + 1) ty).map Prod.snd

/-- Evaluate a compile-time or runtime `LayoutQuery` (`size_of`, `align_of`,
or `offset_of!`). -/
def evalLayoutQuery (adts : List AdtDecl) (tySizes : Nat → Nat)
    (query : LayoutQuery) (adtPad : Nat → Nat := fun _ => 0)
    (target : TargetLayout := defaultTargetLayout) : Option Nat :=
  match query with
  | .sizeOf ty => evalTyByteSize adts tySizes ty adtPad target
  | .alignOf ty => evalTyAlign adts tySizes ty adtPad target
  | .offsetOf (.adt id) variantIdx fieldIdx =>
    if variantIdx == 0 then
      (findAdtDecl adts id).bind fun decl =>
        let unfold := tyLayoutFuel adts tySizes adtPad target (adts.length + 1)
        if decl.repr == .c then
          reprCFieldOffset unfold decl.fields fieldIdx 0
        else if decl.isZeroPaddedWrapper adtPad &&
            fieldIdx == 0 && decl.fields.length == 1 then
          (evalTyByteSize adts tySizes (.adt id) adtPad target).map fun _ => 0
        else
          none
    else
      none
  | .offsetOf _ _ _ => none

/-- Type well-formedness: the model can measure `ty` in `adts` under zero
parameter sizes. -/
def MirTy.wfInAdts (adts : List AdtDecl) (ty : MirTy) : Bool :=
  (evalTyByteSize adts (fun _ => 0) ty).isSome

/-- Whether every signature and local type (`argTys`, `retTy`, and
`requiredLayouts`) of `body` has a valid byte size under `adts` and `tySizes`
(`compiler/rustc_monomorphize/src/collector.rs#L1185-L1207`). -/
def LocalLayoutsAdmitted (adts : List AdtDecl) (body : MirBody)
    (tySizes : Nat → Nat) : Bool :=
  body.argTys.all (fun ty => (evalTyByteSize adts tySizes ty).isSome) &&
  (evalTyByteSize adts tySizes body.retTy).isSome &&
  body.requiredLayouts.all
    (fun ty => (evalTyByteSize adts tySizes ty).isSome)

/-- Static structural well-formedness of a `MirBody` (`MirLang.wf`):
the body declares a return local and all argument locals
(`1 + body.argTys.length ≤ body.localCount`), at least an entry basic block
(`0 < body.blocks.length`), and well-formed layouts at both zero and unit
type-parameter sizes (`LocalLayoutsAdmitted adts body (fun _ => 0) = true` and
`LocalLayoutsAdmitted adts body (fun _ => 1) = true`). -/
def StaticBodyWf (adts : List AdtDecl) (body : MirBody) : Prop :=
  1 + body.argTys.length ≤ body.localCount ∧
  0 < body.blocks.length ∧
  LocalLayoutsAdmitted adts body (fun _ => 0) = true ∧
  LocalLayoutsAdmitted adts body (fun _ => 1) = true

/-! ## Initialization and references -/

/-- Whether `v` and all struct or field payloads inside `v` are initialized
(contain no `.uninit` sub-value). -/
def MirVal.isFullyInit : MirVal → Bool
  | .uninit => false
  | .usize _ | .bool _ | .unit | .bytes _ _ | .ref _ _ _ _ => true
  | .adt _ inner => inner.isFullyInit
  | .fieldCons h t => h.isFullyInit && t.isFullyInit

/-- Pack a list of field values into a `MirVal` payload. A single field `[v]`
is stored directly as `v` so single-field structs are `.adt id v`; two or more
fields are right-nested with `.fieldCons`. -/
def packFields : List MirVal → MirVal
  | [] => .unit
  | [v] => v
  | v :: rest => .fieldCons v (packFields rest)

/-- Extract field `0` from a struct or tuple payload `MirVal`. -/
def firstFieldVal : MirVal → MirVal
  | .fieldCons h _ => h
  | v => v

/-- Extract field `idx` from a struct or tuple payload `MirVal`. -/
def getFieldVal : Nat → MirVal → Option MirVal
  | 0, v => some (firstFieldVal v)
  | i + 1, .fieldCons _ t => getFieldVal i t
  | _ + 1, _ => none

/-- Replace field `idx` in a struct or tuple payload `MirVal` with
`newField`. -/
def setFieldVal (newField : MirVal) : Nat → MirVal → Option MirVal
  | 0, .fieldCons _ t => some (.fieldCons newField t)
  | 0, _ => some newField
  | i + 1, .fieldCons h t => (setFieldVal newField i t).map (.fieldCons h)
  | _ + 1, _ => none

/-- Peel `d` `.field 0` projections off `.adt` wrappers in `v` (`d > 0`
corresponds to `d` nested `.field 0` projections from a borrowed local). -/
def peelFields : Nat → MirVal → Option MirVal
  | 0, v => some v
  | d + 1, .adt _ inner => peelFields d (firstFieldVal inner)
  | _ + 1, _ => none

/-- Resolve a shared reference `.ref targetFrameId gen loc fieldDepth` in state
`s` using monotonic frame IDs (`s.frameId` and `frame.callerFrameId`),
generation counters, and nested `.field 0` projection depth
(`r[undefined.validity.reference]`,
`src/behavior-considered-undefined.md#L120-L125`):
> "A reference or `Box<T>` must be aligned and non-null, it cannot be dangling
> (it must point to a valid allocation of at least the size of the pointee type
> `T`), and it must point to a valid value of type `T`." -/
def resolveRef (s : MirState) (targetFrameId gen : Nat) (loc : LocalId)
    (fieldDepth : Nat := 0) : Option MirVal :=
  let raw :=
    if targetFrameId == s.frameId then
      if s.localGens loc.index == gen then
        s.locals loc.index
      else
        none
    else
      match s.stack.find? (fun f => f.callerFrameId == targetFrameId) with
      | some frame =>
        if frame.callerLocalGens loc.index == gen then
          frame.callerLocals loc.index
        else
          none
      | none => none
  match fieldDepth with
  | 0 => raw
  | d + 1 => raw.bind (peelFields (d + 1))

/-- Whether every reference reachable from `v` (through struct payloads and up
to four reference hops) survives `Terminator.return_` from the active frame of
`s`, whose body has `localCount` locals.

A reference survives if it resolves in `s` and does not point into storage
that the return deallocates:

- When the root (frame `0`) returns, only caller-owned referents survive:
  frame-`0` locals at or above `localCount`.
- When a callee returns, references into its own frame, or into any frame
  newer than it, die; references into older (caller) frames survive.

An uninitialized value or a chain longer than four hops is rejected; this
limit fails closed. -/
def returnRefsStep (s : MirState) (localCount : Nat)
    (follow : MirVal → Bool) : MirVal → Bool
  | .uninit => false
  | .usize _ | .bool _ | .unit | .bytes _ _ => true
  | .adt _ inner => returnRefsStep s localCount follow inner
  | .fieldCons h t =>
    returnRefsStep s localCount follow h &&
    returnRefsStep s localCount follow t
  | .ref frameId gen loc fieldDepth =>
    !(if s.frameId == 0 then
        decide (0 < frameId) || decide (loc.index < localCount)
      else
        decide (s.frameId ≤ frameId)) &&
    (resolveRef s frameId gen loc fieldDepth).any follow

def returnRefsFuel (s : MirState) (localCount : Nat) :
    Nat → MirVal → Bool
  | 0 => fun _ => false
  | fuel + 1 =>
    returnRefsStep s localCount (returnRefsFuel s localCount fuel)

def MirVal.returnRefsOk (s : MirState) (localCount : Nat)
    (v : MirVal) : Bool :=
  returnRefsFuel s localCount 5 v

/-! ## Value validity and first-order invariant denotation -/

/-- Library-level representation invariant on user-defined ADT values
(`src/unsafety.md#L1-L35`):
> "`unsafe` code may trust that *safe* code cannot violate library-level
> invariants when interacting only through the public safe API."

`adtInv id inner` constrains the payload `inner` of a struct value
`.adt id inner`. -/
abbrev AdtInv := Nat → MirVal → Prop

/-- Default ADT representation invariant (`fun _ _ => True`). -/
def defaultAdtInv : AdtInv :=
  fun _ _ => True

/-- Denote a first-order `InvariantSpec` as a predicate on a struct's single
field payload `MirVal`. -/
def denoteInvariant (inv : InvariantSpec) (v : MirVal) : Prop :=
  match v with
  | .usize n => n ≠ inv.ne
  | _ => False

/-- Derive the crate's `AdtInv` from the first-order `AdtDecl` table:
if no declared ADT carries an `invariant`, every payload is accepted
(`defaultAdtInv`); otherwise a payload `v` of struct `id` must satisfy the
`invariant` (if any) of the `AdtDecl` with `decl.id == id`. -/
def denoteAdtInv (adts : List AdtDecl) : AdtInv :=
  if adts.all (·.invariant.isNone) then
    defaultAdtInv
  else
    fun id v =>
      match findAdtDecl adts id with
      | some { invariant := some inv, .. } => denoteInvariant inv v
      | _ => True

/-- Field-by-field validity of a struct payload `MirVal` against a list of
declared fields. Single-field structs `[f]` reduce directly to `unfold f.ty v`;
multi-field structs match `.fieldCons h t` against `f :: rest`. -/
def validFields (unfold : MirTy → MirVal → Prop) :
    List FieldDecl → MirVal → Prop
  | [], .unit => True
  | [], _ => False
  | [f], v => unfold f.ty v
  | f :: rest, .fieldCons h t => unfold f.ty h ∧ validFields unfold rest t
  | _ :: _, _ => False

/-- Validity of `inner` as the payload of `decl` under `unfold`. Structs with
`AdtRepr.unmodeled` have no valid value. -/
def validAdtDecl (unfold : MirTy → MirVal → Prop) (decl : AdtDecl)
    (inner : MirVal) : Prop :=
  match decl.repr with
  | .unmodeled => False
  | .rust | .transparent | .c => validFields unfold decl.fields inner

/-- Value validity with at most `fuel` nested struct unfoldings; see
`MirVal.valid`, which fixes the fuel. `MirVal.usize` models non-negative
integers (`Nat`), while arithmetic overflow checks in `evalBinOp` guard
operation boundaries. -/
def validStep (adts : List AdtDecl) (adtInv : AdtInv)
    (s : MirState) (callerBase : Nat)
    (unfold : MirTy → MirVal → Prop) : MirTy → MirVal → Prop
  | .usize, .usize _ => True
  | .usize, _ => False
  | .isize, .usize _ => True
  | .isize, _ => False
  | .uint _, .usize _ => True
  | .uint _, _ => False
  | .int _, .usize _ => True
  | .int _, _ => False
  | .char, .usize _ => True
  | .char, _ => False
  | .bool, .bool _ => True
  | .bool, _ => False
  | .unit, .unit => True
  | .unit, _ => False
  | .adt id, .adt vId inner =>
    vId = id ∧
    adtInv id inner ∧
    match findAdtDecl adts id with
    | some decl => validAdtDecl unfold decl inner
    | none => False
  | .adt _, _ => False
  | .param idx, .bytes sz _ => sz = s.tySizes idx
  | .param _, _ => False
  | .array elem len, .bytes sz _ =>
    match evalTyByteSize adts s.tySizes (.array elem len) s.adtPad with
    | some arrSz => sz = arrSz
    | none => False
  | .array _ _, _ => False
  | .arraySizeOf elem sizedTy, .bytes sz _ =>
    match evalTyByteSize adts s.tySizes (.arraySizeOf elem sizedTy) s.adtPad with
    | some arrSz => sz = arrSz
    | none => False
  | .arraySizeOf _ _, _ => False
  | .ref inner, .ref frameId gen loc fieldDepth =>
    frameId = 0 ∧
    callerBase ≤ loc.index ∧
    match resolveRef s frameId gen loc fieldDepth with
    | some pointee =>
      validStep adts adtInv s callerBase unfold inner pointee
    | none => False
  | .ref _, _ => False
  | .rawPtr inner _, .ref frameId gen loc fieldDepth =>
    frameId = 0 ∧
    callerBase ≤ loc.index ∧
    match resolveRef s frameId gen loc fieldDepth with
    | some pointee =>
      validStep adts adtInv s callerBase unfold inner pointee
    | none => False
  | .rawPtr _ _, _ => False
  | _, _ => False

def MirVal.validFuel (adts : List AdtDecl) (adtInv : AdtInv)
    (s : MirState) (callerBase : Nat) : Nat → MirTy → MirVal → Prop
  | 0, _, _ => False
  | fuel + 1, ty, v =>
    validStep adts adtInv s callerBase
      (MirVal.validFuel adts adtInv s callerBase fuel) ty v

/-- Value validity: `v` is a valid value of type `ty` in state `s`, for the
root function whose caller-owned referents start at local `callerBase`
(`src/behavior-considered-undefined.md#L114-L132`):
> "The Rust compiler assumes that all values produced during program execution
> are 'valid', and producing an invalid value is hence immediate UB."

This is the only value-validity relation. It is used at function entry (each
argument), at function return (the returned value, in the terminal state),
and by `AdmissibleAdtInv`. -/
def MirVal.valid (adts : List AdtDecl) (adtInv : AdtInv)
    (s : MirState) (callerBase : Nat) (ty : MirTy) (v : MirVal) : Prop :=
  MirVal.validFuel adts adtInv s callerBase (adts.length + 1) ty v

/-! ## Function entry -/

/-- Entry condition on the locals: argument `k` (local `k`, for `k ≥ 1`) holds
a valid value of the `k`-th argument type, and every other local except `_0`
is uninitialized (`compiler/rustc_middle/src/mir/mod.rs#L245-L249`,
`compiler/rustc_middle/src/mir/syntax.rs#L366-L368`):
> "Starting at local 1, `arg_count` locals will be provided by the caller and
> can be assumed to be initialized."

Caller-owned referents live at local indices at or above `localCount`. -/
def argsMatchInv (adts : List AdtDecl) (adtInv : AdtInv)
    (localCount : Nat) (s : MirState) (argTys : List MirTy) : Prop :=
  argTys.foldr
    (fun ty rest k =>
      (∃ v, s.locals k = some v ∧ v.valid adts adtInv s localCount ty) ∧
      rest (k + 1))
    (fun k => ∀ j, k ≤ j → j < localCount → s.locals j = none)
    1

/-- Structural entry state of `body` (`src/items/functions.md#L114-L116`):
control at the first statement of the root frame, no saved frames, fresh
storage generations, an uninitialized return place, well-formed signature and
local layouts (`LocalLayoutsAdmitted`), and structurally valid arguments
(validity without any library invariant, `defaultAdtInv`). -/
def initEntryState (adts : List AdtDecl) (body : MirBody)
    (s : MirState) : Prop :=
  s.block = 0 ∧
  s.stmtIdx = 0 ∧
  s.curBody = none ∧
  s.stack = [] ∧
  s.frameId = 0 ∧
  s.nextFrameId = 1 ∧
  s.localGens = (fun _ => 0) ∧
  s.locals 0 = none ∧
  1 + body.argTys.length ≤ body.localCount ∧
  body.argTys.all (MirTy.wfInAdts adts) = true ∧
  LocalLayoutsAdmitted adts body s.tySizes = true ∧
  argsMatchInv adts defaultAdtInv body.localCount s body.argTys

/-! ## Place lenses and small-step evaluation -/

/-- Whether `v` may appear as a MIR constant operand: only reference-free
scalars (`usize`, `bool`, `()`) are admitted.

A constant's value comes from compile-time evaluation, not from any stack
frame. `rustc` represents it as a `ConstValue` (`rustc@f8a08b68`,
`compiler/rustc_middle/src/mir/consts.rs#L33-L71`), whose pointer-carrying
forms point into global allocations named by an `AllocId`:
> "A value not representable by the other variants; needs to be stored
> in-memory."
> `Indirect { alloc_id: AllocId, offset: Size }`

The model's references (`MirVal.ref`) can only name locals of an activation,
so a constant reference would forge provenance to some frame's local.
Constant struct values are rejected too: they would bypass the constructor
checks that `Rvalue.aggregate` and `Rvalue.aggregateFields` perform. Opaque
generic bytes cannot be MIR literals. Rejecting a constant makes the step
undefined behavior, which fails closed. -/
def MirVal.isConstScalar : MirVal → Bool
  | .usize _ | .bool _ | .unit => true
  | .uninit | .adt _ _ | .fieldCons _ _ | .bytes _ _ | .ref _ _ _ _ => false

/-- Follow a projection list from `v` in state `s`, requiring the resulting
value to be fully initialized (`MirVal.isFullyInit`). -/
def evalProj (s : MirState) :
    List PlaceElem → MirVal → Option MirVal
  | [], v => if v.isFullyInit then some v else none
  | .field idx :: rest, .adt _ inner =>
    (getFieldVal idx inner).bind (evalProj s rest)
  | .field idx :: rest, .fieldCons h t =>
    (getFieldVal idx (.fieldCons h t)).bind (evalProj s rest)
  | .deref :: rest, .ref frameId gen loc fieldDepth =>
    match resolveRef s frameId gen loc fieldDepth with
    | some pointee => evalProj s rest pointee
    | none => none
  | _, _ => none

/-- Read the value at `p` within a frame of `localCount` locals. -/
def evalPlace (localCount : Nat) (s : MirState)
    (p : Place) : Option MirVal :=
  if p.loc.index < localCount then
    match s.locals p.loc.index with
    | some v => evalProj s p.projection v
    | none => none
  else
    none

/-- Replace the sub-value at `proj` inside a local's value with `newVal`.
Writing through `.deref` is rejected because shared references (`&T`) are
immutable. -/
def updateProj (newVal : MirVal) :
    List PlaceElem → Option MirVal → Option MirVal
  | [], _ => some newVal
  | .field idx :: rest, some (.adt id inner) =>
    (getFieldVal idx inner).bind fun curField =>
      (updateProj newVal rest (some curField)).bind fun updatedField =>
        (setFieldVal updatedField idx inner).map (.adt id)
  | .field idx :: rest, some (.fieldCons h t) =>
    (getFieldVal idx (.fieldCons h t)).bind fun curField =>
      (updateProj newVal rest (some curField)).bind fun updatedField =>
        setFieldVal updatedField idx (.fieldCons h t)
  | _, _ => none

/-- Write `val` to `dst` within a frame of `localCount` locals. -/
def assignPlace (localCount : Nat) (locals : Nat → Option MirVal)
    (dst : Place) (val : MirVal) : Option (Nat → Option MirVal) :=
  if dst.loc.index < localCount then
    (updateProj val dst.projection (locals dst.loc.index)).map fun v' =>
      updateLocal locals dst.loc.index (some v')
  else
    none

/-- Deinitialize `p` after `Operand.move p`: clears the local slot to `none`
when `p` is a bare local, or writes `MirVal.uninit` at `p.projection` so any
subsequent read of the moved field or its enclosing struct fails closed. -/
def deinitPlace (localCount : Nat) (locals : Nat → Option MirVal)
    (p : Place) : Option (Nat → Option MirVal) :=
  if p.loc.index < localCount then
    match p.projection with
    | [] => some (updateLocal locals p.loc.index none)
    | proj =>
      (updateProj .uninit proj (locals p.loc.index)).map fun v' =>
        updateLocal locals p.loc.index (some v')
  else
    none

/-- Follow `.field 0` and `.deref` projections to evaluate a shared borrow `&p`
(`Rvalue.ref`), verifying that the final pointee is live and initialized. -/
def evalRefProj (s : MirState) (frameId gen : Nat) (loc : LocalId)
    (fieldDepth : Nat := 0) : List PlaceElem → MirVal → Option MirVal
  | [], v =>
    if v.isFullyInit then some (.ref frameId gen loc fieldDepth) else none
  | .field 0 :: rest, .adt _ inner =>
    evalRefProj s frameId gen loc (fieldDepth + 1) rest (firstFieldVal inner)
  | .deref :: rest, .ref frameId' gen' loc' fieldDepth' =>
    match resolveRef s frameId' gen' loc' fieldDepth' with
    | some pointee =>
      evalRefProj s frameId' gen' loc' fieldDepth' rest pointee
    | none => none
  | _, _ => none

/-- Evaluate a shared borrow `&p` (`Rvalue.ref p`) within a frame of
`localCount` locals. -/
def evalRefPlace (localCount : Nat) (s : MirState) (p : Place) :
    Option MirVal :=
  if p.loc.index < localCount then
    match s.locals p.loc.index with
    | some v =>
      evalRefProj s s.frameId (s.localGens p.loc.index) p.loc 0 p.projection v
    | none => none
  else
    none

/-- Evaluate a MIR `Operand` within a frame of `localCount` locals. -/
def evalOperand (localCount : Nat) (s : MirState)
    (op : Operand) : Option (MirVal × (Nat → Option MirVal)) :=
  match op with
  | .copy src =>
    (evalPlace localCount s src).map fun v => (v, s.locals)
  | .move src =>
    (evalPlace localCount s src).bind fun v =>
      (deinitPlace localCount s.locals src).map fun locals' => (v, locals')
  | .constVal v =>
    if v.isConstScalar then some (v, s.locals) else none
  | .runtimeChecks .ubChecks =>
    some (.bool s.ubChecks, s.locals)
  | .runtimeChecks _ => none

/-- Evaluate a list of operands left-to-right, threading `locals` updates
across moves. -/
def evalOperandList (localCount : Nat) (s : MirState) :
    List Operand → Option (List MirVal × (Nat → Option MirVal))
  | [] => some ([], s.locals)
  | op :: rest =>
    (evalOperand localCount s op).bind fun (v, locals1) =>
      (evalOperandList localCount { s with locals := locals1 } rest).map
        fun (vs, locals2) => (v :: vs, locals2)

/-- Evaluate a binary operation `BinOp` on two initialized `MirVal`
operands. -/
def evalBinOp (op : BinOp) (lhs rhs : MirVal) : Option MirVal :=
  match op, lhs, rhs with
  | .eq, .usize a, .usize b => some (.bool (decide (a = b)))
  | .eq, .bool a, .bool b => some (.bool (decide (a = b)))
  | .eq, .unit, .unit => some (.bool true)
  | .ne, .usize a, .usize b => some (.bool (decide (a ≠ b)))
  | .ne, .bool a, .bool b => some (.bool (decide (a ≠ b)))
  | .ne, .unit, .unit => some (.bool false)
  | .lt, .usize a, .usize b => some (.bool (decide (a < b)))
  | .le, .usize a, .usize b => some (.bool (decide (a ≤ b)))
  | .gt, .usize a, .usize b => some (.bool (decide (b < a)))
  | .ge, .usize a, .usize b => some (.bool (decide (b ≤ a)))
  | .add, .usize a, .usize b => some (.usize (a + b))
  | .sub, .usize a, .usize b =>
    if decide (b ≤ a) then some (.usize (a - b)) else none
  | .mul, .usize a, .usize b => some (.usize (a * b))
  | .bitAnd, .bool a, .bool b => some (.bool (a && b))
  | .bitOr, .bool a, .bool b => some (.bool (a || b))
  | .bitXor, .bool a, .bool b => some (.bool (bne a b))
  | _, _, _ => none

/-- Evaluate a unary operation `UnOp` on an initialized `MirVal` operand. -/
def evalUnOp (op : UnOp) (v : MirVal) : Option MirVal :=
  match op, v with
  | .not, .bool b => some (.bool (!b))
  | _, _ => none

/-! ## Transmutation and transparent wrapper peeling -/

/-- Structural boolean equality on `MirTy`. -/
def MirTy.beq : MirTy → MirTy → Bool
  | .usize, .usize | .isize, .isize | .bool, .bool
  | .char, .char | .unit, .unit => true
  | .uint a, .uint b => a == b
  | .int a, .int b => a == b
  | .adt a, .adt b => a == b
  | .param a, .param b => a == b
  | .ref a, .ref b => MirTy.beq a b
  | .rawPtr a m1, .rawPtr b m2 => m1 == m2 && MirTy.beq a b
  | .array a n1, .array b n2 => n1 == n2 && MirTy.beq a b
  | .arraySizeOf a1 s1, .arraySizeOf a2 s2 =>
    MirTy.beq a1 a2 && MirTy.beq s1 s2
  | _, _ => false

/-- Peel single-field `#[repr(transparent)]` (or zero-padded `#[repr(Rust)]`)
struct wrappers off `(ty, v)` down to the underlying payload type and value. -/
def peelTransparent (adts : List AdtDecl) (adtPad : Nat → Nat) :
    Nat → MirTy → MirVal → Option (MirTy × MirVal)
  | 0, ty, v => some (ty, v)
  | fuel + 1, .adt id, .adt vId inner =>
    if vId == id then
      match findAdtDecl adts id with
      | some decl =>
        if decl.isZeroPaddedWrapper adtPad then
          match decl.payloadTy with
          | some payload => peelTransparent adts adtPad fuel payload inner
          | none => some (.adt id, .adt vId inner)
        else
          some (.adt id, .adt vId inner)
      | none => none
    else
      none
  | _ + 1, ty, v => some (ty, v)

/-- Wrap `baseVal` of type `baseTy` into `dstTy` through `allFieldsPubSafe`
single-field `#[repr(transparent)]` (or zero-padded `#[repr(Rust)]`) struct
wrappers. -/
def wrapTransparent (adts : List AdtDecl) (adtPad : Nat → Nat) :
    Nat → MirTy → MirTy → MirVal → Option MirVal
  | 0, _, _, _ => none
  | fuel + 1, baseTy, dstTy, baseVal =>
    if MirTy.beq baseTy dstTy then
      some baseVal
    else
      match dstTy with
      | .adt id =>
        (findAdtDecl adts id).bind fun decl =>
          if decl.allFieldsPubSafe && decl.isZeroPaddedWrapper adtPad then
            decl.payloadTy.bind fun payload =>
              (wrapTransparent adts adtPad fuel baseTy payload baseVal).map
                (MirVal.adt id)
          else
            none
      | _ => none

/-- Byte width of a primitive scalar `MirTy` on `target`. -/
def primitiveByteSize (target : TargetLayout := defaultTargetLayout) :
    MirTy → Option Nat
  | .usize | .isize => some target.ptrByteWidth
  | .uint w | .int w => (intBitWidthLayout target w).map Prod.fst
  | .bool => some 1
  | .char => some 4
  | .unit => some 0
  | _ => none

/-- Extract the total initialized byte count and little-endian bit pattern from
a struct's field values. -/
def extractFieldBits (extract : MirVal → MirTy → Option (Nat × Nat)) :
    List FieldDecl → MirVal → Option (Nat × Nat)
  | [], .unit => some (0, 0)
  | [f], v =>
    match v with
    | .fieldCons _ _ => none
    | _ => extract v f.ty
  | f :: rest, .fieldCons h t =>
    (extract h f.ty).bind fun (sz1, bits1) =>
      (extractFieldBits extract rest t).map fun (sz2, bits2) =>
        (sz1 + sz2, bits1 + bits2 * Nat.pow 2 (8 * sz1))
  | _, _ => none

/-- Extract the initialized byte size and bit pattern of a `transmute` source
value with at most `fuel` nested struct unfoldings.

Opaque generic type-parameter bytes (`.param _`) and uninitialized values
(`MirVal.uninit`) are rejected: a value of parameter type may contain padding
or uninitialized bytes, and reading those bytes as an integer is undefined
behavior (`src/behavior-considered-undefined.md`, "invalid values"):
> "An integer (`i*`/`u*`), floating point value (`f*`), or raw pointer must be
> initialized, i.e., must not be obtained from uninitialized memory."

Byte arrays (`[u8; N]` and `[u8; size_of::<T>()]`) have every byte initialized
as a `u8`. References are rejected because the model gives them no integer bit
pattern. -/
def extractTransmuteBitsFuel (adts : List AdtDecl) :
    Nat → MirVal → MirTy → Option (Nat × Nat)
  | 0, _, _ => none
  | _ + 1, .usize bits, ty =>
    match primitiveByteSize defaultTargetLayout ty with
    | some sz => some (sz, bits)
    | none => some (8, bits)
  | _ + 1, .bool b, _ => some (1, if b then 1 else 0)
  | _ + 1, .unit, _ => some (0, 0)
  | _ + 1, .bytes sz bits, .array (.uint w) _ =>
    if w == 8 then some (sz, bits) else none
  | _ + 1, .bytes sz bits, .arraySizeOf (.uint w) _ =>
    if w == 8 then some (sz, bits) else none
  | fuel + 1, .adt adtId inner, _ =>
    (findAdtDecl adts adtId).bind fun decl =>
      if decl.repr == .unmodeled then
        none
      else
        extractFieldBits (extractTransmuteBitsFuel adts fuel) decl.fields inner
  | _, _, _ => none

def extractTransmuteBits (adts : List AdtDecl) (v : MirVal)
    (srcTy : MirTy := .unmodeled) : Option (Nat × Nat) :=
  extractTransmuteBitsFuel adts (adts.length + 1) v srcTy

/-- Construct a list of field values from `bits`, returning the sum of field
byte sizes along with the constructed field values. -/
def constructFieldVals (construct : Nat → MirTy → Option MirVal)
    (bits : Nat) : List FieldDecl → Option (Nat × List MirVal)
  | [] => some (0, [])
  | f :: rest =>
    (primitiveByteSize defaultTargetLayout f.ty).bind fun fSz =>
      (construct fSz f.ty).bind fun v =>
        (constructFieldVals construct
          (Nat.div bits (Nat.pow 2 (8 * fSz))) rest).map
          fun (restSz, vs) => (fSz + restSz, v :: vs)

/-- Build the `transmute` result of type `ty` from `dstSz` bytes holding
`bits`, with at most `fuel` nested struct unfoldings. Fails (`none`) unless
every bit pattern of that size is a valid value of `ty`:

- All-bit-pattern integers (`usize`, `isize`, `u*`, `i*`), `()` (0 bytes), and
  byte arrays (`[u8; N]`, `[u8; size_of::<T>()]`) accept every initialized bit
  pattern of matching byte length.
- A struct accepts the result only if safe code could build it from arbitrary
  field values (`AdtDecl.allFieldsPubSafe`) and its fields have no padding
  (`sumSz == dstSz`); otherwise its library invariant might be violated.
- `bool`, `char`, and references are rejected because not every bit pattern is
  valid (`src/behavior-considered-undefined.md`, "invalid values"):
  > "A value other than `false` (`0`) or `true` (`1`) in a `bool`."
- An unconstrained type parameter is rejected because it could be instantiated
  with `bool`, a reference, or a struct with an invariant. -/
def constructTransmuteVal (adts : List AdtDecl)
    (dstSz bits : Nat) : Nat → MirTy → Option MirVal
  | 0, _ => none
  | _ + 1, .usize | _ + 1, .isize =>
    if dstSz == 8 then some (.usize bits) else none
  | _ + 1, .uint w | _ + 1, .int w =>
    match intBitWidthLayout defaultTargetLayout w with
    | some (sz, _) => if dstSz == sz then some (.usize bits) else none
    | none => none
  | _ + 1, .bool | _ + 1, .char => none
  | _ + 1, .unit => if dstSz == 0 then some .unit else none
  | _ + 1, .array (.uint w) len =>
    if w == 8 && dstSz == len then some (.bytes dstSz bits) else none
  | _ + 1, .arraySizeOf (.uint w) _ =>
    if w == 8 then some (.bytes dstSz bits) else none
  | fuel + 1, .adt id =>
    (findAdtDecl adts id).bind fun decl =>
      if decl.allFieldsPubSafe && decl.repr != .unmodeled then
        match decl.fields with
        | [f] =>
          (constructTransmuteVal adts dstSz bits fuel f.ty).map
            (MirVal.adt id)
        | fields =>
          (constructFieldVals
            (fun fSz fTy => constructTransmuteVal adts fSz bits fuel fTy)
            bits fields).bind fun (sumSz, vs) =>
              if sumSz == dstSz then
                some (.adt id (packFields vs))
              else
                none
      else
        none
  | _ + 1, _ => none

/-- Evaluate a by-value transmutation of `srcVal` from `srcTy` to `dstTy`
(`CastKind.transmute` and the core of `transmute_copy`).

Accepts either:
1. Equal-size transparent wrapper peeling/wrapping (`peelTransparent` +
   `wrapTransparent`) when the peeled payload type equals the target payload
   type (for example, `Wrapper<T> <-> T` under `#[repr(transparent)]`), or
2. Equal-size bit-pattern transmutation when `srcVal` has `vSz = srcSz`
   initialized non-padding bytes (`extractTransmuteBits`) and every bit pattern
   of that size is valid at `dstTy` (`constructTransmuteVal`). -/
def evalTransmuteVal (adts : List AdtDecl) (s : MirState)
    (srcTy dstTy : MirTy) (srcVal : MirVal)
    (target : TargetLayout := defaultTargetLayout) : Option MirVal :=
  if !srcVal.isFullyInit then
    none
  else
    match evalTyByteSize adts s.tySizes srcTy s.adtPad target,
          evalTyByteSize adts s.tySizes dstTy s.adtPad target with
    | some srcSz, some dstSz =>
      if decide (srcSz = dstSz) then
        let fuel := adts.length + 1
        match (peelTransparent adts s.adtPad fuel srcTy srcVal).bind
            (fun (baseTy, baseVal) =>
              wrapTransparent adts s.adtPad fuel baseTy dstTy baseVal) with
        | some wrapped => some wrapped
        | none =>
          match extractTransmuteBits adts srcVal srcTy with
          | some (vSz, bits) =>
            if decide (vSz = srcSz) then
              constructTransmuteVal adts dstSz bits fuel dstTy
            else
              none
          | none => none
      else
        none
    | _, _ => none

/-- Operational evaluation of `core::mem::transmute_copy::<srcTy, dstTy>(&src)`
(`rustc@f8a08b68`, `library/core/src/mem/mod.rs#L1028-L1039`):
> "Interprets `src` as having type `&Dst`, and then reads `src` without moving
> the contained value."
> "This function triggers undefined behavior if `Dst` is larger than `Src`." -/
def evalTransmuteCopy (adts : List AdtDecl) (s : MirState)
    (srcTy dstTy : MirTy) (argVal : MirVal)
    (target : TargetLayout := defaultTargetLayout) : Option MirVal :=
  match argVal with
  | .ref frameId gen loc fieldDepth =>
    match resolveRef s frameId gen loc fieldDepth with
    | some pointee => evalTransmuteVal adts s srcTy dstTy pointee target
    | none => none
  | _ => none

/-! ## Small-step statement, terminator, and constant evaluation -/

/-- Advance to the next statement in the current basic block with `locals'`. -/
def MirState.nextStmt :
    MirState → (Nat → Option MirVal) → RawStep MirState MirReturn
  | ⟨_, localGens, block, stmtIdx, tySizes, curBody, stack, frameId,
     nextFrameId, adtPad, ubChecks⟩, locals' =>
    .silent ⟨locals', localGens, block, stmtIdx + 1, tySizes, curBody, stack,
      frameId, nextFrameId, adtPad, ubChecks⟩

/-- Advance to the next statement updating both `locals'` and `localGens'`. -/
def MirState.nextStmtGen :
    MirState → (Nat → Option MirVal) → (Nat → Nat) →
      RawStep MirState MirReturn
  | ⟨_, _, block, stmtIdx, tySizes, curBody, stack, frameId, nextFrameId,
     adtPad, ubChecks⟩, locals', localGens' =>
    .silent ⟨locals', localGens', block, stmtIdx + 1, tySizes, curBody, stack,
      frameId, nextFrameId, adtPad, ubChecks⟩

/-- Jump to statement `0` of basic block `target` in the current frame. -/
def MirState.gotoBlock :
    MirState → (Nat → Option MirVal) → Nat →
      RawStep MirState MirReturn
  | ⟨_, localGens, _, _, tySizes, curBody, stack, frameId, nextFrameId,
     adtPad, ubChecks⟩, locals', target =>
    .silent ⟨locals', localGens, target, 0, tySizes, curBody, stack, frameId,
      nextFrameId, adtPad, ubChecks⟩

/-- Canonical initial state for evaluating a zero-argument compile-time constant
`MirBody` under `tySizes` and `adtPad`. -/
def constEntryState (tySizes : Nat → Nat)
    (adtPad : Nat → Nat := fun _ => 0) : MirState where
  locals := fun _ => none
  block := 0
  stmtIdx := 0
  tySizes := tySizes
  adtPad := adtPad

/-- Extract the repeated byte value from a `[elem; N]` repeat operand. -/
def evalRepeatElem : MirVal → Option Nat
  | .usize bits => some bits
  | .bool b => some (if b then 1 else 0)
  | _ => none

/-- Single-step operational evaluation of a MIR statement inside `activeBody`
(`src/behavior-considered-undefined.md#L54-L55`,
`src/expressions.md#L199-L215`):
> "After moving out of a place expression that evaluates to a local variable,
> the location is deinitialized and cannot be read from again until it is
> reinitialized."

`Stmt.evalConst` evaluates a compile-time constant or `const { ... }` block in
the exact basic-block statement order where `rustc` places it: a constant that
panics (`Terminator.panic` or `Terminator.assert`) terminates the enclosing
execution with `.terminated .compileTimeError` (pruning that layout or
type-parameter world as a compile-time error), whereas a constant that hits
undefined behavior or a model limit steps to `.failed`. -/
def evalMirStmt (activeBody : MirBody) (s : MirState)
    (stmt : Stmt) (adts : List AdtDecl)
    (bodies : List BodyDecl := [])
    (evalConstBody : MirBody → MirState → RawStep MirState MirReturn :=
      fun _ _ => .failed)
    (target : TargetLayout := defaultTargetLayout) :
    RawStep MirState MirReturn :=
  match stmt with
  | .assign dst (.use op) =>
    match evalOperand activeBody.localCount s op with
    | some (v, locals') =>
      match assignPlace activeBody.localCount locals' dst v with
      | some locals'' => s.nextStmt locals''
      | none => .failed
    | none => .failed
  | .assign dst (.repeat op len) =>
    match evalOperand activeBody.localCount s op with
    | some (v, locals') =>
      match evalRepeatElem v with
      | some bits =>
        match assignPlace activeBody.localCount locals' dst
            (.bytes len bits) with
        | some locals'' => s.nextStmt locals''
        | none => .failed
      | none => .failed
    | none => .failed
  | .assign dst (.repeatSizeOf op sizedTy) =>
    match evalOperand activeBody.localCount s op,
          evalTyByteSize adts s.tySizes sizedTy s.adtPad target with
    | some (v, locals'), some sz =>
      match evalRepeatElem v with
      | some bits =>
        match assignPlace activeBody.localCount locals' dst
            (.bytes sz bits) with
        | some locals'' => s.nextStmt locals''
        | none => .failed
      | none => .failed
    | _, _ => .failed
  | .assign dst (.binaryOp op lhs rhs) =>
    match evalOperand activeBody.localCount s lhs with
    | some (v1, locals1) =>
      match evalOperand activeBody.localCount
          { s with locals := locals1 } rhs with
      | some (v2, locals2) =>
        match evalBinOp op v1 v2 with
        | some outVal =>
          match assignPlace activeBody.localCount locals2 dst outVal with
          | some locals3 => s.nextStmt locals3
          | none => .failed
        | none => .failed
      | none => .failed
    | none => .failed
  | .assign dst (.unaryOp op src) =>
    match evalOperand activeBody.localCount s src with
    | some (v, locals') =>
      match evalUnOp op v with
      | some outVal =>
        match assignPlace activeBody.localCount locals' dst outVal with
        | some locals'' => s.nextStmt locals''
        | none => .failed
      | none => .failed
    | none => .failed
  | .assign dst (.aggregate adtId op) =>
    if (findAdtDecl adts adtId).any
        (fun d => d.fields.length == 1 && d.repr != .unmodeled) then
      match evalOperand activeBody.localCount s op with
      | some (v, locals') =>
        match assignPlace activeBody.localCount locals' dst (.adt adtId v) with
        | some locals'' => s.nextStmt locals''
        | none => .failed
      | none => .failed
    else
      .failed
  | .assign dst (.aggregateFields ops adtIdOpt) =>
    match evalOperandList activeBody.localCount s ops with
    | some (vs, locals') =>
      match adtIdOpt with
      | some adtId =>
        if (findAdtDecl adts adtId).any
            (fun d => d.fields.length == vs.length && d.repr != .unmodeled) then
          match assignPlace activeBody.localCount locals' dst
              (.adt adtId (packFields vs)) with
          | some locals'' => s.nextStmt locals''
          | none => .failed
        else
          .failed
      | none =>
        match assignPlace activeBody.localCount locals' dst (packFields vs) with
        | some locals'' => s.nextStmt locals''
        | none => .failed
    | none => .failed
  | .assign dst (.ref src) | .assign dst (.rawPtr _ src) =>
    match evalRefPlace activeBody.localCount s src with
    | some refVal =>
      match assignPlace activeBody.localCount s.locals dst refVal with
      | some locals' => s.nextStmt locals'
      | none => .failed
    | none => .failed
  | .assign dst (.cast (.transmute srcTy) op dstTy) =>
    match evalOperand activeBody.localCount s op with
    | some (v, locals') =>
      match evalTransmuteVal adts { s with locals := locals' }
          srcTy dstTy v target with
      | some outVal =>
        match assignPlace activeBody.localCount locals' dst outVal with
        | some locals'' => s.nextStmt locals''
        | none => .failed
      | none => .failed
    | none => .failed
  | .assign dst (.cast .intToInt op dstTy)
  | .assign dst (.cast .ptrToPtr op dstTy) =>
    if (evalTyByteSize adts s.tySizes dstTy s.adtPad target).isSome then
      match evalOperand activeBody.localCount s op with
      | some (v, locals') =>
        match assignPlace activeBody.localCount locals' dst v with
        | some locals'' => s.nextStmt locals''
        | none => .failed
      | none => .failed
    else
      .failed
  | .assign _ _ =>
    .failed
  | .evalConst dst constId typeArgs =>
    match (findBody bodies constId).bind (MirBody.subst typeArgs) with
    | some cBody =>
      if cBody.argTys.isEmpty then
        match evalConstBody cBody (constEntryState s.tySizes s.adtPad) with
        | .terminated (.normal ret) =>
          if ret.value.isConstScalar then
            match assignPlace activeBody.localCount s.locals dst ret.value with
            | some locals' => s.nextStmt locals'
            | none => .failed
          else
            .failed
        | .terminated .unwind | .terminated .abort
        | .terminated .compileTimeError =>
          .terminated .compileTimeError
        | _ => .failed
      else
        .failed
    | none => .failed
  | .placeMention p =>
    match p.projection with
    | [] =>
      if p.loc.index < activeBody.localCount then
        s.nextStmt s.locals
      else
        .failed
    | _ =>
      match evalPlace activeBody.localCount s p with
      | some _ => s.nextStmt s.locals
      | none => .failed
  | .storageLive loc | .storageDead loc =>
    if loc.index < activeBody.localCount then
      s.nextStmtGen (updateLocal s.locals loc.index none)
        (bumpGen s.localGens loc.index)
    else
      .failed
  | .nop | .constEvalCounter =>
    s.nextStmt s.locals
  | _ =>
    .failed

/-- Single-step operational evaluation of a MIR terminator
(`compiler/rustc_middle/src/mir/syntax.rs#L684-L798`):
> "Returning very likely at least assigns the value currently in the return
> place (`_0`) to the place specified in the associated `Call` terminator in the
> calling function, as if assigned via `dest = move _0`."

A root `return_` produces `.terminated (.normal ⟨value, s⟩)`, carrying the
terminal state. A `call1` looks up the callee's `BodyId` in `bodies`,
instantiates it with `MirBody.subst`, and runs it in a fresh activation; an
unknown `BodyId` or failed instantiation is undefined behavior. -/
def evalMirTerminator (adts : List AdtDecl)
    (bodies : List BodyDecl) (activeBody : MirBody) (s : MirState)
    (term : Terminator) (targetLayout : TargetLayout := defaultTargetLayout) :
    RawStep MirState MirReturn :=
  match term with
  | .return_ =>
    if 0 < activeBody.localCount then
      match s.locals 0 with
      | none => .failed
      | some retVal =>
        if retVal.isFullyInit &&
           retVal.returnRefsOk s activeBody.localCount then
          match s.stack with
          | [] => .terminated (.normal ⟨retVal, s⟩)
          | frame :: restStack =>
            if frame.retBlock < frame.callerBody.blocks.length then
              match assignPlace frame.callerBody.localCount frame.callerLocals
                  frame.retDst retVal with
              | some callerLocals' =>
                .silent {
                  locals := callerLocals'
                  localGens := frame.callerLocalGens
                  block := frame.retBlock
                  stmtIdx := 0
                  tySizes := s.tySizes
                  curBody :=
                    if restStack.isEmpty then none else some frame.callerBody
                  stack := restStack
                  frameId := frame.callerFrameId
                  nextFrameId := s.nextFrameId
                  adtPad := s.adtPad
                  ubChecks := s.ubChecks
                }
              | none => .failed
            else
              .failed
        else
          .failed
    else
      .failed
  | .goto target =>
    if target.index < activeBody.blocks.length then
      s.gotoBlock s.locals target.index
    else
      .failed
  | .unreachable =>
    .failed
  | .panic hasCleanup =>
    if hasCleanup || !s.stack.isEmpty then
      .failed
    else
      .terminated .unwind
  | .assert cond expected target onFail hasCleanup =>
    match evalOperand activeBody.localCount s cond with
    | some (.bool b, locals') =>
      if b == expected then
        if target.index < activeBody.blocks.length then
          s.gotoBlock locals' target.index
        else
          .failed
      else
        match onFail with
        | .unwind =>
          if hasCleanup || !s.stack.isEmpty then
            .failed
          else
            .terminated .unwind
        | .abort => .terminated .abort
        | .ub => .failed
    | _ => .failed
  | .switchInt discr falseTarget trueTarget =>
    match evalOperand activeBody.localCount s discr with
    | some (.bool false, locals') =>
      if falseTarget.index < activeBody.blocks.length then
        s.gotoBlock locals' falseTarget.index
      else
        .failed
    | some (.bool true, locals') =>
      if trueTarget.index < activeBody.blocks.length then
        s.gotoBlock locals' trueTarget.index
      else
        .failed
    | _ => .failed
  | .callLayout dst query target =>
    if target.index < activeBody.blocks.length then
      match evalLayoutQuery adts s.tySizes query s.adtPad targetLayout with
      | some val =>
        match assignPlace activeBody.localCount s.locals dst (.usize val) with
        | some locals' => s.gotoBlock locals' target.index
        | none => .failed
      | none => .failed
    else
      .failed
  | .callTransmuteCopy dst srcTy dstTy op target =>
    if target.index < activeBody.blocks.length then
      match evalOperand activeBody.localCount s op with
      | some (argVal, locals') =>
        match evalTransmuteCopy adts { s with locals := locals' }
            srcTy dstTy argVal targetLayout with
        | some outVal =>
          match assignPlace activeBody.localCount locals' dst outVal with
          | some locals'' => s.gotoBlock locals'' target.index
          | none => .failed
        | none => .failed
      | none => .failed
    else
      .failed
  | .call1 dst calleeId arg target typeArgs =>
    ((findBody bodies calleeId).bind (MirBody.subst typeArgs)).elim .failed
      fun instCallee =>
      if dst.loc.index < activeBody.localCount &&
         target.index < activeBody.blocks.length &&
         instCallee.argTys.length == 1 &&
         2 ≤ instCallee.localCount &&
         0 < instCallee.blocks.length then
        match evalOperand activeBody.localCount s arg with
        | some (argVal, callerLocals') =>
          let calleeLocals : Nat → Option MirVal :=
            updateLocal (fun _ => none) 1 (some argVal)
          let frame : StackFrame := {
            callerBody := activeBody
            callerLocals := callerLocals'
            callerLocalGens := s.localGens
            retDst := dst
            retBlock := target.index
            callerFrameId := s.frameId
          }
          .silent {
            locals := calleeLocals
            localGens := fun _ => 0
            block := 0
            stmtIdx := 0
            tySizes := s.tySizes
            curBody := some instCallee
            stack := frame :: s.stack
            frameId := s.nextFrameId
            nextFrameId := s.nextFrameId + 1
            adtPad := s.adtPad
            ubChecks := s.ubChecks
          }
        | none => .failed
      else
        .failed
  | _ =>
    .failed

/-- Single-step transition of `rootBody` parameterized by a constant-body
evaluator `evalConstBody`. -/
def evalMirStepWith (adts : List AdtDecl) (bodies : List BodyDecl)
    (evalConstBody : MirBody → MirState → RawStep MirState MirReturn)
    (target : TargetLayout) (rootBody : MirBody)
    (s : MirState) : RawStep MirState MirReturn :=
  let active := s.curBody.getD rootBody
  match lookupAt active.blocks s.block with
  | none => .failed
  | some bb =>
    match lookupAt bb.stmts s.stmtIdx with
    | some stmt =>
      evalMirStmt active s stmt adts bodies evalConstBody target
    | none =>
      if s.stmtIdx == bb.stmts.length then
        evalMirTerminator adts bodies active s bb.terminator target
      else
        .failed

/-- Run `stepFn` for at most `fuel` silent steps on `cBody` starting from `cs`
(`src/const_eval.md#L1-L25`):
> "A constant expression is evaluated at compile time. If evaluation fails (for
> example, due to a panic or integer overflow), compilation fails." -/
def runConstSteps (stepFn : MirBody → MirState → RawStep MirState MirReturn) :
    Nat → MirBody → MirState → RawStep MirState MirReturn
  | 0, _, _ => .failed
  | fuel + 1, cBody, cs =>
    match stepFn cBody cs with
    | .silent cs' => runConstSteps stepFn fuel cBody cs'
    | out => out

/-- Default step budget per compile-time constant evaluation. -/
def defaultConstFuel : Nat := 64

/-- Evaluate `evalMirStepWith` supporting up to `depth` nested constant
evaluations via structural recursion on `depth`. -/
def evalMirStepDepth (adts : List AdtDecl) (bodies : List BodyDecl)
    (target : TargetLayout) :
    Nat → MirBody → MirState → RawStep MirState MirReturn
  | 0, rootBody, s =>
    evalMirStepWith adts bodies (fun _ _ => .failed) target rootBody s
  | depth + 1, rootBody, s =>
    let stepFn := evalMirStepDepth adts bodies target depth
    evalMirStepWith adts bodies
      (runConstSteps stepFn defaultConstFuel) target rootBody s

/-- Single-step transition function of a `MirBody` under `adts`, `bodies`, and
`target`. -/
def evalMirStep (adts : List AdtDecl)
    (bodies : List BodyDecl := []) (rootBody : MirBody)
    (s : MirState) (target : TargetLayout := defaultTargetLayout) :
    RawStep MirState MirReturn :=
  evalMirStepDepth adts bodies target 2 rootBody s

/-- Relational step transition of a `MirBody`. -/
abbrev MirStep (adts : List AdtDecl) (bodies : List BodyDecl := [])
    (body : MirBody) (s : MirState)
    (r : StepResult MirState Empty MirReturn) : Prop :=
  r = (evalMirStep adts bodies body s).toStepResult

/-! ## Post-monomorphization constants -/

/-- `RequiresConst bodies (some body) c` holds when instantiating `body`
requires the constant instance `c` to evaluate successfully
(`Body::required_consts`, `compiler/rustc_middle/src/mir/mod.rs#L279-L285`,
`compiler/rustc_monomorphize/src/collector.rs#L1185-L1207`):
> "Constants that are required to evaluate successfully for this `Body` to be
> well-formed. Wait until monomorphization to evaluate them."

Requirements are transitive through the constants' own required constants and
through the bodies of called functions. Every instance is looked up in `bodies`
by `BodyId` and instantiated with `MirBody.subst`, so it is in the root
function's parameter space and is evaluated under the root's `tySizes`. An
undeclared `BodyId` or failed instantiation yields `none`, and `failedInstance`
makes `none` require the unsatisfiable constant `none`, so a failed lookup or
instantiation can never silently drop a requirement. -/
inductive RequiresConst (bodies : List BodyDecl) :
    Option MirBody → Option MirBody → Prop where
  | failedInstance : RequiresConst bodies none none
  | direct {body : MirBody} {cId : BodyId} {typeArgs : List MirTy} :
      (cId, typeArgs) ∈ body.requiredConsts →
      RequiresConst bodies (some body)
        ((findBody bodies cId).bind (MirBody.subst typeArgs))
  | viaConst {body : MirBody} {cId : BodyId} {typeArgs : List MirTy}
      {d : Option MirBody} :
      (cId, typeArgs) ∈ body.requiredConsts →
      RequiresConst bodies
        ((findBody bodies cId).bind (MirBody.subst typeArgs)) d →
      RequiresConst bodies (some body) d
  | viaCall {body : MirBody} {bb : BasicBlock} {dst : Place}
      {calleeId : BodyId} {arg : Operand} {target : BlockId}
      {typeArgs : List MirTy} {d : Option MirBody} :
      bb ∈ body.blocks →
      bb.terminator = .call1 dst calleeId arg target typeArgs →
      RequiresConst bodies
        ((findBody bodies calleeId).bind (MirBody.subst typeArgs)) d →
      RequiresConst bodies (some body) d

/-- Compile-Time Function Evaluation (CTFE) success predicate
(`src/const_eval.md#L1-L25`):
> "A constant expression is evaluated at compile time. If evaluation fails (for
> example, due to a panic or integer overflow), compilation fails." -/
def ConstSucceeds (adts : List AdtDecl) (bodies : List BodyDecl := [])
    (tySizes : Nat → Nat) (c : MirBody) : Prop :=
  c.argTys = [] ∧
  ∃ n v,
    ReachesPrefix (MirStep adts bodies) c n (constEntryState tySizes) []
      (.terminated (.normal v))

/-- A required constant cleanly panics (`Terminator.panic` or
`Terminator.assert`) under `tySizes`. In `rustc`, a `const` block that panics
during monomorphization causes CTFE to reject that monomorphization at compile
time (a Post-Monomorphization Error). By contrast, a constant that steps to
`.failed` or diverges reflects either undefined behavior or a model limit,
which must never silently exclude a `tySizes` assignment from verification. -/
def ConstUnwinds (adts : List AdtDecl) (bodies : List BodyDecl := [])
    (tySizes : Nat → Nat) (c : MirBody) : Prop :=
  c.argTys = [] ∧
  ∃ n,
    ReachesPrefix (MirStep adts bodies) c n (constEntryState tySizes) []
      (.terminated .unwind)

/-- Every reachable required constant of `body` is total across all valid
`tySizes` assignments (`ValidTySizes`): at every `tySizes`, lookup and
substitution succeed and the constant either returns normally (`ConstSucceeds`)
or panics cleanly (`ConstUnwinds`). If any required constant steps to `.failed`
or fails lookup/substitution on even a single valid `tySizes` branch,
`ConstsTotal` is false and `initMirState` becomes empty everywhere, causing
`NonVacuousOn` to fail closed. -/
def ConstsTotal (adts : List AdtDecl) (bodies : List BodyDecl := [])
    (body : MirBody) : Prop :=
  ∀ (tySizes : Nat → Nat) (c : Option MirBody),
    ValidTySizes tySizes →
    RequiresConst bodies (some body) c →
    ∃ cBody, c = some cBody ∧
      (ConstSucceeds adts bodies tySizes cBody ∨
       ConstUnwinds adts bodies tySizes cBody)

/-- Monomorphization admission: every constant instance that `body` requires
exists and evaluates successfully under `tySizes`. A constant the model cannot
evaluate makes this false, which empties the function's initial-state set and
fails closed (see `NonVacuousOn`). -/
def MonoAdmitted (adts : List AdtDecl) (bodies : List BodyDecl := [])
    (tySizes : Nat → Nat) (body : MirBody) : Prop :=
  ∀ c, RequiresConst bodies (some body) c →
    ∃ cBody, c = some cBody ∧ ConstSucceeds adts bodies tySizes cBody

/-- Full initial state predicate of `MirMachine` for `body`. -/
def initMirState (adts : List AdtDecl) (bodies : List BodyDecl := [])
    (body : MirBody) (s : MirState) : Prop :=
  initEntryState adts body s ∧
  ConstsTotal adts bodies body ∧
  MonoAdmitted adts bodies s.tySizes body

/-- Small-step operational machine for `MirBody` under `adts` and `bodies`. -/
def MirMachine (adts : List AdtDecl) (bodies : List BodyDecl := []) :
    SmallStepMachine MirBody MirState Empty MirReturn where
  wf := StaticBodyWf adts
  initState := initMirState adts bodies
  step := MirStep adts bodies

/-- Operational language of Rust MIR (`(MirMachine adts bodies).toLanguage`). -/
def MirLang (adts : List AdtDecl) (bodies : List BodyDecl := []) :
    Language :=
  (MirMachine adts bodies).toLanguage

/-- Operational behavior of a `MirBody`. -/
abbrev MirSem (adts : List AdtDecl) (bodies : List BodyDecl := [])
    (body : MirBody) : (MirLang adts bodies).Behavior :=
  (MirLang adts bodies).sem body

/-! ## Library contract and first-order spec denotation -/

/-- Admissibility of an ADT representation invariant `adtInv`
(`r[expr.struct.safety]`, `src/expressions/struct-expr.md#L58-L65`).

If safe code can build a struct directly (all fields public and safe), the
invariant must accept every structurally valid payload, in every state:
otherwise unsafe code could rely on a property that safe code can violate.
Quantifying over the state `s` makes reference-valued payloads count too (a
reference is valid only relative to a state); `callerBase := 0` accepts the
widest set of references, which only strengthens the requirement.

There is no requirement that every declared struct be inhabited. An
invariant that no value satisfies only makes functions that take the struct
unverifiable (their initial-state set is empty), and an unsupported struct
shape affects only the functions that mention it. -/
def AdmissibleAdtInv (adts : List AdtDecl) (adtInv : AdtInv) : Prop :=
  NoDupIds (adts.map AdtDecl.id) ∧
  ∀ decl, decl ∈ adts → decl.allFieldsPubSafe = true →
    ∀ (s : MirState) (inner : MirVal),
      validAdtDecl (MirVal.valid adts defaultAdtInv s 0) decl inner →
      adtInv decl.id inner

/-- Postcondition asserting that a normal return value equals the initial value
of argument local `argLocal`. -/
def EnsuresEqArg (argLocal : Nat) (adts : List AdtDecl := [])
    (bodies : List BodyDecl := []) : (MirLang adts bodies).Behavior :=
  (MirLang adts bodies).Spec (fun s out =>
    ∀ tr r, out = .terminated tr (.normal r) →
      s.locals argLocal = some r.value)

/-- Denote an optional first-order `RequiresSpec` (`/// anneal:requires`) as a
precondition on the entry `MirState`. -/
def denoteRequires : Option RequiresSpec → MirState → Prop
  | none, _ => True
  | some req, s =>
    ∀ n, s.locals req.argLocal = some (.usize n) → n ≠ req.ne

/-- Denote a first-order `PostSpec` (`/// anneal:spec`) as a behavioral
specification in `MirLang adts bodies`. -/
def denotePostSpec (adts : List AdtDecl) (bodies : List BodyDecl := []) :
    PostSpec → (MirLang adts bodies).Behavior
  | .ensuresEqArg argLocal => EnsuresEqArg argLocal adts bodies

/-- Denoted `# Safety` precondition of `fn`. -/
abbrev CapturedFn.safetyPre (fn : CapturedFn) : MirState → Prop :=
  denoteRequires fn.requires

/-- Denoted library representation invariant of `c`. -/
abbrev Crate.adtInv (c : Crate) : AdtInv :=
  denoteAdtInv c.adts

/-! ## Contract well-formedness, obligations, and `CrateTheorem` -/

/-- Whether `tcb` carries a `TCBItem.compileTimeGuard` waiver for `fn`. -/
def hasCompileTimeGuardWaiver (fn : CapturedFn) (tcb : List TCBItem) : Bool :=
  tcb.any fun
    | .compileTimeGuard name bodyId =>
      name == fn.name && bodyId.index == fn.bodyId.index
    | _ => false

/-- Whether `tcb` carries a `TCBItem.pinnedCompilerCoupled` waiver for `fn`. -/
def hasPinnedCoupledWaiver (fn : CapturedFn) (tcb : List TCBItem) : Bool :=
  tcb.any fun
    | .pinnedCompilerCoupled name bodyId _ =>
      name == fn.name && bodyId.index == fn.bodyId.index
    | _ => false

/-- Post-monomorphization contract completeness (`MonoConstsWf`) for `fn` and
`body`:
- When `fn` carries an explicit Anneal contract (`fn.requires.isSome` or
  `!fn.specs.isEmpty`), every valid type-size assignment whose local layouts are
  admitted must also satisfy `MonoAdmitted` (so an unguarded PME in a contracted
  function fails closed).
- When `fn` is an unannotated Level-1 function (`fn.requires.isNone` and
  `fn.specs.isEmpty`), at least one valid type-size assignment must satisfy both
  `LocalLayoutsAdmitted` and `MonoAdmitted` (so a dead-on-arrival function that
  panics at compile time for every monomorphization is rejected, while a
  generic Level-1 function is verified across the monomorphizations that `rustc`
  admits). -/
def MonoConstsWf (adts : List AdtDecl) (bodies : List BodyDecl := [])
    (fn : CapturedFn) (body : MirBody) : Prop :=
  if fn.requires.isSome || !fn.specs.isEmpty then
    ∀ tySizes,
      ValidTySizes tySizes →
      LocalLayoutsAdmitted adts body tySizes = true →
      MonoAdmitted adts bodies tySizes body
  else
    ∃ tySizes,
      ValidTySizes tySizes ∧
      LocalLayoutsAdmitted adts body tySizes = true ∧
      MonoAdmitted adts bodies tySizes body

/-- Unwaivable static and post-monomorphization contract well-formedness of a
single `MirBody` for `fn`. -/
def ContractWellFormed (adts : List AdtDecl) (bodies : List BodyDecl := [])
    (fn : CapturedFn) (body : MirBody) : Prop :=
  StaticBodyWf adts body ∧
  ConstsTotal adts bodies body ∧
  MonoConstsWf adts bodies fn body

/-- Canonical ill-formed fallback `MirBody` returned when a `BodyId` is missing
from `Crate.bodies`, ensuring `StaticBodyWf` (`0 < localCount`,
`0 < blocks.length`, `LocalLayoutsAdmitted`) fails closed. -/
def illFormedFallbackBody : MirBody where
  argTys := []
  retTy := .unmodeled
  localCount := 0
  blocks := []

/-- Look up `id` in `bodies`, falling back to `illFormedFallbackBody` if `id` is
missing. -/
def resolveBodyById (bodies : List BodyDecl) (id : BodyId) : MirBody :=
  (findBody bodies id).getD illFormedFallbackBody

/-- Look up `fn.bodyId` in `bodies`, falling back to `illFormedFallbackBody` so
any missing `BodyId` fails `StaticBodyWf`. -/
def CapturedFn.resolveBody (bodies : List BodyDecl) (fn : CapturedFn) :
    MirBody :=
  resolveBodyById bodies fn.bodyId

/-- Unwaivable contract well-formedness across both `fn.bodyId` (`--release`)
and optional `fn.debugBodyId` (`--debug`). -/
def FnContractWellFormed (adts : List AdtDecl) (bodies : List BodyDecl)
    (fn : CapturedFn) : Prop :=
  ContractWellFormed adts bodies fn (fn.resolveBody bodies) ∧
  match fn.debugBodyId with
  | none => True
  | some dbgId =>
    ContractWellFormed adts bodies fn (resolveBodyById bodies dbgId)

/-- Baseline safety precondition of `body` for `fn`:
an initialized entry state (`initMirState`), arguments valid under the crate's
library representation invariant `adtInv`, and—only when `fn.isUnsafe = true`—
the function's `# Safety` precondition `fn.safetyPre`. Safe functions
(`fn.isUnsafe = false`) cannot assume `fn.safetyPre` to avoid undefined behavior
or violate library representation invariants. When a
`TCBItem.pinnedCompilerCoupled` waiver is present in `tcb`, the precondition
additionally restricts `s.adtPad` to the pinned compiler's zero-extra-padding
world (`s.adtPad = fun _ => 0`). -/
def SafetyPre (adts : List AdtDecl) (bodies : List BodyDecl)
    (adtInv : AdtInv) (fn : CapturedFn) (body : MirBody)
    (s : MirState) (tcb : List TCBItem := []) : Prop :=
  initMirState adts bodies body s ∧
  argsMatchInv adts adtInv body.localCount s body.argTys ∧
  (if hasPinnedCoupledWaiver fn tcb then
     s.adtPad = (fun _ => 0) ∧ (fn.isUnsafe = true → fn.safetyPre s)
   else
     (fn.isUnsafe = true → fn.safetyPre s))

/-- Mandatory return-validity and compile-time guard postcondition:
1. Any normal return yields a value that is valid (including `adtInv`) in the
   terminal state, with references restricted to caller-owned referents.
2. When `allowCompileTimeGuard` is `false` (no `TCBItem.compileTimeGuard` waiver
   in `Crate.tcb`), execution never terminates with `.compileTimeError` in any
   layout or type-parameter world. When `allowCompileTimeGuard` is `true`,
   `.compileTimeError` may prune incompatible layout or type-parameter worlds,
   provided execution still never hits `.compileTimeError` in the pinned
   zero-extra-padding world (`s.adtPad = fun _ => 0` and `s.tySizes = fun _ => 8`). -/
def SafetyPost (adts : List AdtDecl) (adtInv : AdtInv)
    (body : MirBody) (s : MirState)
    (out : EventualOut Empty MirReturn)
    (allowCompileTimeGuard : Bool := false) : Prop :=
  (∀ tr r, out = .terminated tr (.normal r) →
    r.value.valid adts adtInv r.state body.localCount body.retTy) ∧
  (if allowCompileTimeGuard then
     s.adtPad = (fun _ => 0) ∧ s.tySizes = (fun _ => 8) →
       ∀ tr, out ≠ .terminated tr .compileTimeError
   else
     ∀ tr, out ≠ .terminated tr .compileTimeError)

/-- Conjunction of all user-declared postconditions (`fn.specs`) evaluated at
initial state `s` and outcome `out`. -/
def ContractPost (adts : List AdtDecl) (bodies : List BodyDecl)
    (fn : CapturedFn) (s : MirState)
    (out : EventualOut Empty MirReturn) : Prop :=
  AllHold (fn.specs.map (fun p =>
    (denotePostSpec adts bodies p s).val True.intro out))

/-- Multi-guarantee postcondition combining unconditional return validity
(`SafetyPost`) with conditional functional correctness
(`fn.safetyPre s → ContractPost`). By `Anneal.verified_meet_iff`, verifying
`body` against `(SafetyPre, EffectivePost)` is equivalent to verifying
`(SafetyPre, SafetyPost)` and refining
`SpecOn (SafetyPre ∧ fn.safetyPre) ContractPost`. -/
def EffectivePost (adts : List AdtDecl) (bodies : List BodyDecl)
    (adtInv : AdtInv) (fn : CapturedFn) (body : MirBody)
    (s : MirState) (out : EventualOut Empty MirReturn)
    (tcb : List TCBItem := []) : Prop :=
  SafetyPost adts adtInv body s out (hasCompileTimeGuardWaiver fn tcb) ∧
  (fn.safetyPre s → ContractPost adts bodies fn s out)

/-- Behavioral verification of a single lowered `MirBody` (`bodyId` or
`debugBodyId`) for `fn`. -/
def FnBodyVerified (adts : List AdtDecl) (bodies : List BodyDecl)
    (adtInv : AdtInv) (fn : CapturedFn) (body : MirBody)
    (tcb : List TCBItem := []) : Prop :=
  (MirLang adts bodies).Verified
    (fun s => SafetyPre adts bodies adtInv fn body s tcb)
    (fun s out => EffectivePost adts bodies adtInv fn body s out tcb)
    body

/-- Behavioral verification of `fn` across both `fn.bodyId` (`--release`) and
optional `fn.debugBodyId` (`--debug`). -/
def FnVerified (adts : List AdtDecl) (bodies : List BodyDecl)
    (adtInv : AdtInv) (fn : CapturedFn) (tcb : List TCBItem := []) : Prop :=
  FnBodyVerified adts bodies adtInv fn (fn.resolveBody bodies) tcb ∧
  match fn.debugBodyId with
  | none => True
  | some dbgId =>
    FnBodyVerified adts bodies adtInv fn (resolveBodyById bodies dbgId) tcb

/-- Named behavioral verification obligation for `fn`. -/
def CapturedFn.obligation (adts : List AdtDecl) (bodies : List BodyDecl)
    (adtInv : AdtInv) (fn : CapturedFn) (tcb : List TCBItem := []) :
    Obligation ObligationId where
  id := .fnBody fn.name
  prop := FnVerified adts bodies adtInv fn tcb

/-- Top-level theorem required of every verified Rust crate:
1. Non-empty function inventory (`c.functions ≠ []`),
2. Distinct body IDs and function names (`NoDupIds`),
3. Unwaivable ADT invariant admissibility (`AdmissibleAdtInv`),
4. Unwaivable static and post-monomorphization contract well-formedness
   (`FnContractWellFormed`) for every function in `c.functions`, and
5. Waiver-aware behavioral verification (`VerificationResult c.tcbWaivedIds`)
   across every function in `c.functions`. -/
def CrateTheorem (c : Crate) : Prop :=
  c.functions ≠ [] ∧
  NoDupIds (c.bodies.map (fun d => d.id.index)) ∧
  NoDupIds (c.functions.map CapturedFn.name) ∧
  AdmissibleAdtInv c.adts c.adtInv ∧
  AllHold (c.functions.map (FnContractWellFormed c.adts c.bodies)) ∧
  VerificationResult c.tcbWaivedIds
    (c.functions.map (fun fn => fn.obligation c.adts c.bodies c.adtInv c.tcb))

end Trusted

/-!
## Section 2: Unified Small-Step Bridge (`ExecSafePost`) and Static/ADT Checkers
-/

namespace Anneal.SymEval

open Trusted

/-- `RawStep.toStepResult` preserves inhabitedness of `.choice` branches. -/
theorem toStepResult_choice_inhabited {State Obs Val : Type}
    {r : RawStep State Val} {branches : State → Prop}
    (h : StepResult.choice (Obs := Obs) (Val := Val) branches =
      r.toStepResult) :
    ∃ s', branches s' := by
  cases r with
  | silent s' =>
    injection h with hbr
    subst hbr
    exact ⟨s', rfl⟩
  | terminated _ => nomatch h
  | failed => nomatch h

/-- Constructive prefix existence for `MirMachine adts bodies` at every step
budget `n : Nat` from any state `s`. -/
theorem mir_exists_reaches_prefix (adts : List AdtDecl) (bodies : List BodyDecl)
    (body : MirBody) :
    ∀ (n : Nat) (s : MirState),
      ∃ tr out,
        ReachesPrefix (MirStep adts bodies) body n s tr out ∧ out ≠ .stuck
  | 0, s =>
    ⟨[], .running s, ReachesPrefix.zero s, fun h => by cases h⟩
  | k + 1, s => by
    cases hstep : evalMirStep adts bodies body s with
    | silent s' =>
      have hstepR :
          MirStep adts bodies body s (.silent s') :=
        congrArg RawStep.toStepResult hstep.symm
      cases mir_exists_reaches_prefix adts bodies body k s' with
      | intro tr hrest =>
        cases hrest with
        | intro out hpair =>
          exact ⟨tr, out,
            ReachesPrefix.choice k s s' (fun s₂ => s₂ = s') tr out
              hstepR rfl hpair.1,
            hpair.2⟩
    | terminated term =>
      have hstepR :
          MirStep adts bodies body s (.terminated term) :=
        congrArg RawStep.toStepResult hstep.symm
      exact ⟨[], .terminated term,
        ReachesPrefix.terminated k s term hstepR,
        fun h => by cases h⟩
    | failed =>
      have hstepR :
          MirStep adts bodies body s .failed :=
        congrArg RawStep.toStepResult hstep.symm
      exact ⟨[], .failed,
        ReachesPrefix.failed k s hstepR,
        fun h => by cases h⟩

theorem reachesPrefix_of_silent
    {adts : List AdtDecl} {bodies : List BodyDecl} {body : MirBody}
    {s s' : MirState} {n : Nat} {tr : List Empty}
    {out : PrefixOutcome MirState MirReturn}
    (hstep : evalMirStep adts bodies body s = .silent s')
    (hreach : ReachesPrefix (MirStep adts bodies) body n s tr out) :
    out = .running s ∨
      ∃ n' tr', ReachesPrefix (MirStep adts bodies) body n' s' tr' out := by
  have hstepR :
      (evalMirStep adts bodies body s).toStepResult (Obs := Empty) =
        StepResult.silent s' :=
    congrArg RawStep.toStepResult hstep
  cases hreach with
  | zero => exact Or.inl rfl
  | step _ _ _ obs _ _ _ _ => nomatch obs
  | choice n' _ s₂ branches _ _ h1 hbr hr =>
    have h1' :
        StepResult.choice branches =
          (evalMirStep adts bodies body s).toStepResult := h1
    rw [hstepR] at h1'
    injection h1' with hbr_eq
    subst hbr_eq
    subst hbr
    exact Or.inr ⟨n', tr, hr⟩
  | emptyChoice _ _ branches h1 hemp =>
    have h1' :
        StepResult.choice branches =
          (evalMirStep adts bodies body s).toStepResult := h1
    rw [hstepR] at h1'
    injection h1' with hbr_eq
    subst hbr_eq
    exact False.elim (hemp ⟨s', rfl⟩)
  | terminated _ _ _ h1 =>
    have h1' : _ = (evalMirStep adts bodies body s).toStepResult := h1
    rw [hstepR] at h1'; cases h1'
  | failed _ _ h1 =>
    have h1' : _ = (evalMirStep adts bodies body s).toStepResult := h1
    rw [hstepR] at h1'; cases h1'
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, hstepR.symm⟩)

theorem reachesPrefix_of_terminated
    {adts : List AdtDecl} {bodies : List BodyDecl} {body : MirBody}
    {s : MirState} {n : Nat} {tr : List Empty}
    {out : PrefixOutcome MirState MirReturn}
    {term : TerminationKind MirReturn}
    (hstep : evalMirStep adts bodies body s = .terminated term)
    (hreach : ReachesPrefix (MirStep adts bodies) body n s tr out) :
    out = .running s ∨ out = .terminated term := by
  have hstepR :
      (evalMirStep adts bodies body s).toStepResult (Obs := Empty) =
        StepResult.terminated term :=
    congrArg RawStep.toStepResult hstep
  cases hreach with
  | zero => exact Or.inl rfl
  | step _ _ _ obs _ _ _ _ => nomatch obs
  | choice _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = (evalMirStep adts bodies body s).toStepResult := h1
    rw [hstepR] at h1'; cases h1'
  | emptyChoice _ _ _ h1 _ =>
    have h1' : _ = (evalMirStep adts bodies body s).toStepResult := h1
    rw [hstepR] at h1'; cases h1'
  | terminated _ _ t h1 =>
    have h1' :
        StepResult.terminated t =
          (evalMirStep adts bodies body s).toStepResult := h1
    rw [hstepR] at h1'
    injection h1' with ht
    subst ht
    exact Or.inr rfl
  | failed _ _ h1 =>
    have h1' : _ = (evalMirStep adts bodies body s).toStepResult := h1
    rw [hstepR] at h1'; cases h1'
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, hstepR.symm⟩)

/-- Unified finite-execution safety and postcondition relation over `MirState`.
`ExecSafePost adts bodies body allowCte P s` witnesses that from state `s`,
`evalMirStep adts bodies body` deterministically reaches a safe terminal state
satisfying:
- `P r` on `.terminated (.normal r)`,
- unconditional safety on `.terminated .unwind` and `.terminated .abort`, and
- `allowCte` on `.terminated .compileTimeError`. -/
inductive ExecSafePost (adts : List AdtDecl) (bodies : List BodyDecl)
    (body : MirBody) (allowCte : Prop) (P : MirReturn → Prop) :
    MirState → Prop where
  | step {s s' : MirState} :
      evalMirStep adts bodies body s = .silent s' →
      ExecSafePost adts bodies body allowCte P s' →
      ExecSafePost adts bodies body allowCte P s
  | normal {s : MirState} {r : MirReturn} :
      evalMirStep adts bodies body s = .terminated (.normal r) →
      P r →
      ExecSafePost adts bodies body allowCte P s
  | unwind {s : MirState} :
      evalMirStep adts bodies body s = .terminated .unwind →
      ExecSafePost adts bodies body allowCte P s
  | abort {s : MirState} :
      evalMirStep adts bodies body s = .terminated .abort →
      ExecSafePost adts bodies body allowCte P s
  | compileTimeError {s : MirState} :
      evalMirStep adts bodies body s = .terminated .compileTimeError →
      allowCte →
      ExecSafePost adts bodies body allowCte P s

theorem execSafePost_reachesPrefix
    {adts : List AdtDecl} {bodies : List BodyDecl} {body : MirBody}
    {allowCte : Prop} {P : MirReturn → Prop} {s : MirState}
    (hexec : ExecSafePost adts bodies body allowCte P s) :
    ∀ {n : Nat} {tr : List Empty} {out : PrefixOutcome MirState MirReturn},
      ReachesPrefix (MirStep adts bodies) body n s tr out →
      out.isSafe ∧
      (∀ r, out = .terminated (.normal r) → P r) ∧
      (out = .terminated .compileTimeError → allowCte) := by
  induction hexec with
  | step hstep _ ih =>
    intro n tr out hreach
    cases reachesPrefix_of_silent hstep hreach with
    | inl hrun =>
      subst hrun
      exact ⟨True.intro, (fun _ h => by cases h), (fun h => by cases h)⟩
    | inr hex =>
      rcases hex with ⟨n', tr', hr'⟩
      exact ih hr'
  | normal hstep hPr =>
    intro n tr out hreach
    cases reachesPrefix_of_terminated hstep hreach with
    | inl hrun =>
      subst hrun
      exact ⟨True.intro, (fun _ h => by cases h), (fun h => by cases h)⟩
    | inr hterm =>
      subst hterm
      refine ⟨True.intro, ?_, (fun h => by cases h)⟩
      intro r hr
      injection hr with h1
      injection h1 with h2
      subst h2
      exact hPr
  | unwind hstep =>
    intro n tr out hreach
    cases reachesPrefix_of_terminated hstep hreach with
    | inl hrun =>
      subst hrun
      exact ⟨True.intro, (fun _ h => by cases h), (fun h => by cases h)⟩
    | inr hterm =>
      subst hterm
      exact ⟨True.intro, (fun _ h => by cases h), (fun h => by cases h)⟩
  | abort hstep =>
    intro n tr out hreach
    cases reachesPrefix_of_terminated hstep hreach with
    | inl hrun =>
      subst hrun
      exact ⟨True.intro, (fun _ h => by cases h), (fun h => by cases h)⟩
    | inr hterm =>
      subst hterm
      exact ⟨True.intro, (fun _ h => by cases h), (fun h => by cases h)⟩
  | compileTimeError hstep hcte =>
    intro n tr out hreach
    cases reachesPrefix_of_terminated hstep hreach with
    | inl hrun =>
      subst hrun
      exact ⟨True.intro, (fun _ h => by cases h), (fun h => by cases h)⟩
    | inr hterm =>
      subst hterm
      exact ⟨True.intro, (fun _ h => by cases h), (fun _ => hcte)⟩

theorem execSafePost_exists_terminated
    {adts : List AdtDecl} {bodies : List BodyDecl} {body : MirBody}
    {allowCte : Prop} {P : MirReturn → Prop} {s : MirState}
    (hexec : ExecSafePost adts bodies body allowCte P s) :
    ∃ n term,
      ReachesPrefix (MirStep adts bodies) body n s [] (.terminated term) := by
  induction hexec with
  | @step s s' hstep _ ih =>
    rcases ih with ⟨n, term, hreach⟩
    have hstepR : MirStep adts bodies body s (.silent s') :=
      congrArg RawStep.toStepResult hstep.symm
    exact ⟨n + 1, term,
      ReachesPrefix.choice n s s' (fun s₂ => s₂ = s') [] (.terminated term)
        hstepR rfl hreach⟩
  | @normal s r hstep _ =>
    have hstepR : MirStep adts bodies body s (.terminated (.normal r)) :=
      congrArg RawStep.toStepResult hstep.symm
    exact ⟨1, .normal r, ReachesPrefix.terminated 0 s (.normal r) hstepR⟩
  | @unwind s hstep =>
    have hstepR : MirStep adts bodies body s (.terminated .unwind) :=
      congrArg RawStep.toStepResult hstep.symm
    exact ⟨1, .unwind, ReachesPrefix.terminated 0 s .unwind hstepR⟩
  | @abort s hstep =>
    have hstepR : MirStep adts bodies body s (.terminated .abort) :=
      congrArg RawStep.toStepResult hstep.symm
    exact ⟨1, .abort, ReachesPrefix.terminated 0 s .abort hstepR⟩
  | @compileTimeError s hstep _ =>
    have hstepR : MirStep adts bodies body s (.terminated .compileTimeError) :=
      congrArg RawStep.toStepResult hstep.symm
    exact ⟨1, .compileTimeError,
      ReachesPrefix.terminated 0 s .compileTimeError hstepR⟩

/-- Postcondition predicate on a normal return `r : MirReturn` for `fn` and
initial state `s₀`: the conjunction of all `PostSpec` items in `fn.specs`. -/
def HoldsPostSpecs (specs : List PostSpec) (s₀ : MirState)
    (r : MirReturn) : Prop :=
  AllHold (specs.map fun
    | .ensuresEqArg argLocal => s₀.locals argLocal = some r.value)

theorem contractPost_of_holdsPostSpecs {adts : List AdtDecl}
    {bodies : List BodyDecl} {s₀ : MirState}
    {out : EventualOut Empty MirReturn}
    (hpost : ∀ tr r, out = .terminated tr (.normal r) →
      HoldsPostSpecs specs s₀ r) :
    AllHold (specs.map (fun p =>
      (denotePostSpec adts bodies p s₀).val True.intro out)) := by
  induction specs with
  | nil => exact True.intro
  | cons spec rest ih =>
    cases spec with
    | ensuresEqArg argLocal =>
      dsimp [List.map, AllHold, denotePostSpec, EnsuresEqArg,
             Language.Spec, Language.SpecOn]
      exact ⟨fun tr r hout => (hpost tr r hout).1,
             ih (fun tr r hout => (hpost tr r hout).2)⟩

/-- Master bridge from `ExecSafePost` to `FnBodyVerified`. -/
theorem execSafePost_fnBodyVerified
    {adts : List AdtDecl} {bodies : List BodyDecl} {adtInv : AdtInv}
    {fn : CapturedFn} {body : MirBody} {tcb : List TCBItem}
    (hwf : StaticBodyWf adts body)
    (hexec : ∀ s₀,
      SafetyPre adts bodies adtInv fn body s₀ tcb →
      ExecSafePost adts bodies body
        (hasCompileTimeGuardWaiver fn tcb = true ∧
          ¬ (s₀.adtPad = (fun _ => 0) ∧ s₀.tySizes = (fun _ => 8)))
        (fun r =>
          r.value.valid adts adtInv r.state body.localCount body.retTy ∧
          (fn.safetyPre s₀ → HoldsPostSpecs fn.specs s₀ r))
        s₀) :
    FnBodyVerified adts bodies adtInv fn body tcb := by
  refine ⟨hwf, ?_, ?_⟩
  · intro s₀ hpre
    have hex := hexec s₀ hpre
    have hdef : ((MirLang adts bodies).sem body s₀).defined :=
      fun _ _ _ _ hreach => (execSafePost_reachesPrefix hex hreach).1
    rcases execSafePost_exists_terminated hex with ⟨n, term, hreach⟩
    exact ⟨hdef, .terminated [] term, ⟨hpre.1, ⟨n, hreach⟩⟩⟩
  · intro s₀ hpre
    have hex := hexec s₀ hpre
    have hsafe : ((MirLang adts bodies).sem body s₀).defined :=
      fun _ _ _ _ hreach => (execSafePost_reachesPrefix hex hreach).1
    refine ⟨hsafe, ?_⟩
    intro out hsem
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro tr r hout
      subst hout
      rcases hsem.2 with ⟨n, hreach⟩
      exact ((execSafePost_reachesPrefix hex hreach).2.1 r rfl).1
    · cases hwaiv : hasCompileTimeGuardWaiver fn tcb with
      | false =>
        dsimp
        intro tr hout
        subst hout
        rcases hsem.2 with ⟨n, hreach⟩
        have hcte := (execSafePost_reachesPrefix hex hreach).2.2 rfl
        rw [hwaiv] at hcte
        cases hcte.1
      | true =>
        dsimp
        intro hpin tr hout
        subst hout
        rcases hsem.2 with ⟨n, hreach⟩
        have hcte := (execSafePost_reachesPrefix hex hreach).2.2 rfl
        exact hcte.2 hpin
    · intro hsafPre
      unfold ContractPost
      refine contractPost_of_holdsPostSpecs ?_
      intro tr r hout
      subst hout
      rcases hsem.2 with ⟨n, hreach⟩
      exact ((execSafePost_reachesPrefix hex hreach).2.1 r rfl).2 hsafPre

/-!
### Executable Checkers for `StaticBodyWf`, `RequiresConst`, `NoDupIds`, and `AdmissibleAdtInv`
-/

def checkStaticBodyWf (adts : List AdtDecl) (body : MirBody) : Bool :=
  decide (1 + body.argTys.length ≤ body.localCount) &&
  decide (0 < body.blocks.length) &&
  LocalLayoutsAdmitted adts body (fun _ => 0) &&
  LocalLayoutsAdmitted adts body (fun _ => 1)

theorem checkStaticBodyWf_sound {adts : List AdtDecl} {body : MirBody}
    (h : checkStaticBodyWf adts body = true) :
    StaticBodyWf adts body := by
  unfold checkStaticBodyWf at h
  rcases Bool.and_eq_true_iff.mp h with ⟨h123, hl1⟩
  rcases Bool.and_eq_true_iff.mp h123 with ⟨h12, hl0⟩
  rcases Bool.and_eq_true_iff.mp h12 with ⟨hc, hb⟩
  exact ⟨of_decide_eq_true hc, of_decide_eq_true hb, hl0, hl1⟩

def checkBlockNoRequiredConsts (bodies : List BodyDecl)
    (checkRec : MirBody → Bool) (bb : BasicBlock) : Bool :=
  match bb.terminator with
  | .call1 _ calleeId _ _ typeArgs =>
    match (findBody bodies calleeId).bind (MirBody.subst typeArgs) with
    | some calleeBody => checkRec calleeBody
    | none => false
  | _ => true

def checkNoRequiredConsts : Nat → List BodyDecl → MirBody → Bool
  | 0, _, _ => false
  | fuel + 1, bodies, body =>
    decide (body.requiredConsts = []) &&
    body.blocks.all
      (checkBlockNoRequiredConsts bodies (checkNoRequiredConsts fuel bodies))

theorem list_all_mem {α : Type} {p : α → Bool} {xs : List α} {x : α}
    (hall : xs.all p = true) (hmem : x ∈ xs) : p x = true := by
  induction xs with
  | nil => cases hmem
  | cons y ys ih =>
    dsimp [List.all] at hall
    rcases Bool.and_eq_true_iff.mp hall with ⟨hpy, hpys⟩
    cases hmem with
    | head => exact hpy
    | tail _ hmem' => exact ih hpys hmem'

theorem noRequiresConst_of_check :
    ∀ {fuel : Nat} {bodies : List BodyDecl} {body : MirBody}
      {c : Option MirBody},
      checkNoRequiredConsts fuel bodies body = true →
      RequiresConst bodies (some body) c →
      False
  | 0, _, _, _, hchk, _ => by cases hchk
  | fuel + 1, bodies, body, c, hchk, hc => by
    dsimp [checkNoRequiredConsts] at hchk
    rcases Bool.and_eq_true_iff.mp hchk with ⟨hrcDec, hbbs⟩
    have hrc : body.requiredConsts = [] := of_decide_eq_true hrcDec
    cases hc with
    | direct hmem => rw [hrc] at hmem; cases hmem
    | viaConst hmem _ => rw [hrc] at hmem; cases hmem
    | viaCall hbb hterm hreq =>
      have hbbChk := list_all_mem hbbs hbb
      dsimp [checkBlockNoRequiredConsts] at hbbChk
      rw [hterm] at hbbChk
      dsimp at hbbChk
      cases hcallee :
          (findBody bodies _).bind (MirBody.subst _) with
      | none =>
        rw [hcallee] at hbbChk
        cases hbbChk
      | some calleeBody =>
        rw [hcallee] at hbbChk hreq
        exact noRequiresConst_of_check hbbChk hreq

theorem one_le_isizeMaxBytes : 1 ≤ isizeMaxBytes := by decide

theorem validTySizes_one : ValidTySizes (fun _ => 1) :=
  fun _ => one_le_isizeMaxBytes

theorem contractWellFormed_of_checks {adts : List AdtDecl}
    {bodies : List BodyDecl} {fn : CapturedFn} {body : MirBody} {fuel : Nat}
    (hwf : checkStaticBodyWf adts body = true)
    (hrc : checkNoRequiredConsts fuel bodies body = true) :
    ContractWellFormed adts bodies fn body := by
  have hStatic := checkStaticBodyWf_sound hwf
  have hTotal : ConstsTotal adts bodies body :=
    fun _ _ _ hc => False.elim (noRequiresConst_of_check hrc hc)
  have hMono : ∀ tySizes, MonoAdmitted adts bodies tySizes body :=
    fun _ _ hc => False.elim (noRequiresConst_of_check hrc hc)
  refine ⟨hStatic, hTotal, ?_⟩
  unfold MonoConstsWf
  cases fn.requires.isSome || !fn.specs.isEmpty with
  | true => exact fun tySizes _ _ => hMono tySizes
  | false => exact ⟨fun _ => 1, validTySizes_one, hStatic.2.2.2, hMono _⟩

def beqObligationId : ObligationId → ObligationId → Bool
  | .fnBody n1, .fnBody n2 => decide (n1 = n2)

theorem eq_of_beqObligationId :
    ∀ {a b : ObligationId}, beqObligationId a b = true → a = b
  | .fnBody _, .fnBody _, h => by
    dsimp [beqObligationId] at h
    rw [of_decide_eq_true h]

theorem ne_of_beqObligationId_false :
    ∀ {a b : ObligationId}, beqObligationId a b = false → a ≠ b
  | .fnBody _, .fnBody _, h => by
    intro heq
    injection heq with hn
    subst hn
    dsimp [beqObligationId] at h
    rw [decide_eq_true rfl] at h
    cases h

def checkNotMem {α : Type} (beq : α → α → Bool) (x : α) : List α → Bool
  | [] => true
  | y :: ys => !beq x y && checkNotMem beq x ys

theorem allHold_ne_of_checkNotMem {α : Type} {beq : α → α → Bool}
    (hne : ∀ {x y : α}, beq x y = false → x ≠ y) {x : α} :
    ∀ {ys : List α},
      checkNotMem beq x ys = true →
      AllHold (ys.map (fun y => x ≠ y))
  | [], _ => True.intro
  | y :: ys, h => by
    dsimp [checkNotMem] at h
    rcases Bool.and_eq_true_iff.mp h with ⟨hxy, hrest⟩
    cases hbeq : beq x y with
    | true => rw [hbeq] at hxy; cases hxy
    | false => exact ⟨hne hbeq, allHold_ne_of_checkNotMem hne hrest⟩

def checkNoDupFoldr {α : Type} (beq : α → α → Bool) :
    List α → Bool × List α
  | [] => (true, [])
  | x :: xs =>
    let r := checkNoDupFoldr beq xs
    (checkNotMem beq x r.2 && r.1, x :: r.2)

theorem noDupIds_of_checkNoDupFoldr {α : Type} {beq : α → α → Bool}
    (hne : ∀ {x y : α}, beq x y = false → x ≠ y) :
    ∀ {xs : List α},
      (checkNoDupFoldr beq xs).1 = true →
      NoDupIds xs ∧
      (checkNoDupFoldr beq xs).2 =
        (xs.foldr
          (fun id (acc : Prop × List α) =>
            (AllHold (acc.2.map (fun id' => id ≠ id')) ∧ acc.1,
             id :: acc.2))
          (True, [])).2
  | [], _ => ⟨True.intro, rfl⟩
  | x :: xs, h => by
    dsimp [checkNoDupFoldr] at h
    rcases Bool.and_eq_true_iff.mp h with ⟨h1, h2⟩
    have ih := noDupIds_of_checkNoDupFoldr hne h2
    have hall := allHold_ne_of_checkNotMem hne h1
    rw [ih.2] at hall
    exact ⟨⟨hall, ih.1⟩, congrArg (List.cons x) ih.2⟩

def checkNoDupIds {α : Type} (beq : α → α → Bool) (xs : List α) : Bool :=
  (checkNoDupFoldr beq xs).1

theorem noDupIds_of_check {α : Type} {beq : α → α → Bool}
    (hne : ∀ {x y : α}, beq x y = false → x ≠ y) {xs : List α}
    (h : checkNoDupIds beq xs = true) : NoDupIds xs :=
  (noDupIds_of_checkNoDupFoldr hne h).1

def checkMemObligationId (x : ObligationId) : List ObligationId → Bool
  | [] => false
  | y :: ys => beqObligationId x y || checkMemObligationId x ys

theorem mem_of_checkMemObligationId {x : ObligationId} :
    ∀ {ys : List ObligationId}, checkMemObligationId x ys = true → x ∈ ys
  | [], h => by cases h
  | y :: ys, h => by
    dsimp [checkMemObligationId] at h
    cases hxy : beqObligationId x y with
    | true =>
      rw [eq_of_beqObligationId hxy]
      exact .head _
    | false =>
      rw [hxy, Bool.false_or] at h
      exact .tail _ (mem_of_checkMemObligationId h)

theorem allHold_fnBody_ne {m : String} :
    ∀ {ns : List String},
      AllHold (ns.map (fun n' => m ≠ n')) →
      AllHold ((ns.map ObligationId.fnBody).map (fun id' =>
        ObligationId.fnBody m ≠ id'))
  | [], _ => True.intro
  | _ :: _, ⟨h1, h2⟩ =>
    ⟨fun heq => by injection heq with hname; exact h1 hname,
     allHold_fnBody_ne h2⟩

theorem noDupIds_fnBody_of_names :
    ∀ {fns : List CapturedFn},
      NoDupIds (fns.map CapturedFn.name) →
      NoDupIds (fns.map (fun fn => ObligationId.fnBody fn.name)) ∧
      ((fns.map (fun fn => ObligationId.fnBody fn.name)).foldr
        (fun id (acc : Prop × List ObligationId) =>
          (AllHold (acc.2.map (fun id' => id ≠ id')) ∧ acc.1,
           id :: acc.2))
        (True, [])).2 =
      ((fns.map CapturedFn.name).foldr
        (fun n (acc : Prop × List String) =>
          (AllHold (acc.2.map (fun n' => n ≠ n')) ∧ acc.1,
           n :: acc.2))
        (True, [])).2.map ObligationId.fnBody
  | [], _ => ⟨True.intro, rfl⟩
  | fn :: rest, ⟨hall, hrest⟩ => by
    have ih := noDupIds_fnBody_of_names hrest
    dsimp [List.map, List.foldr, NoDupIds]
    refine ⟨⟨?_, ih.1⟩, congrArg (List.cons (.fnBody fn.name)) ih.2⟩
    rw [ih.2]
    exact allHold_fnBody_ne hall

theorem map_obligation_id {adts : List AdtDecl} {bodies : List BodyDecl}
    {adtInv : AdtInv} {tcb : List TCBItem} :
    ∀ (fns : List CapturedFn),
      (fns.map (fun fn => fn.obligation adts bodies adtInv tcb)).map
          Obligation.id =
        fns.map (fun fn => ObligationId.fnBody fn.name)
  | [] => rfl
  | fn :: rest => by
    dsimp [List.map, CapturedFn.obligation]
    exact congrArg (List.cons (.fnBody fn.name)) (map_obligation_id rest)

/-- Check `AdmissibleAdtInv adts (denoteAdtInv adts)` for an arbitrary ADT
table: every `AdtDecl.id` is distinct, and no struct with
`allFieldsPubSafe = true` declares a library invariant (`invariant.isNone`). -/
def checkAdmissibleAdtInv (adts : List AdtDecl) : Bool :=
  checkNoDupIds (fun a b => decide (a = b)) (adts.map AdtDecl.id) &&
  adts.all (fun d => !d.allFieldsPubSafe || d.invariant.isNone)

theorem findAdtDecl_invariant_none_of_all
    {adts : List AdtDecl} {id : Nat} {d : AdtDecl}
    (hall : adts.all (fun d => !d.allFieldsPubSafe || d.invariant.isNone) = true)
    (hfind : findAdtDecl adts id = some d)
    (hpub : d.allFieldsPubSafe = true) :
    d.invariant = none := by
  unfold findAdtDecl at hfind
  induction adts with
  | nil => cases hfind
  | cons x xs ih =>
    dsimp [List.find?] at hfind
    dsimp [List.all] at hall
    rcases Bool.and_eq_true_iff.mp hall with ⟨hx, hxs⟩
    cases hxeq : (x.id == id) with
    | true =>
      rw [hxeq] at hfind
      injection hfind with hd
      subst hd
      cases hinv : x.invariant with
      | none => rfl
      | some _ => rw [hpub, hinv] at hx; cases hx
    | false =>
      rw [hxeq] at hfind
      exact ih hxs hfind

theorem checkNoDupFoldr_snd {α : Type} (beq : α → α → Bool) :
    ∀ (xs : List α), (checkNoDupFoldr beq xs).2 = xs
  | [] => rfl
  | x :: xs => congrArg (List.cons x) (checkNoDupFoldr_snd beq xs)

theorem checkNotMem_ne_of_mem {x : Nat} :
    ∀ {ys : List Nat},
      checkNotMem (fun a b => decide (a = b)) x ys = true →
      ∀ {y : Nat}, y ∈ ys → (x == y) = false
  | [], _, _, hmem => by cases hmem
  | z :: zs, hchk, y, hmem => by
    dsimp [checkNotMem] at hchk
    rcases Bool.and_eq_true_iff.mp hchk with ⟨hxz, hrest⟩
    cases hmem with
    | head =>
      cases hdec : decide (x = z) with
      | true => rw [hdec] at hxz; cases hxz
      | false =>
        have hne : x ≠ z := of_decide_eq_false hdec
        exact beq_eq_false_iff_ne.mpr hne
    | tail _ hmem' => exact checkNotMem_ne_of_mem hrest hmem'

theorem findAdtDecl_of_mem_nodup :
    ∀ {adts : List AdtDecl} {decl : AdtDecl},
      checkNoDupIds (fun a b => decide (a = b)) (adts.map AdtDecl.id) = true →
      decl ∈ adts →
      findAdtDecl adts decl.id = some decl
  | [], _, _, hmem => by cases hmem
  | d :: rest, decl, hnodup, hmem => by
    unfold checkNoDupIds at hnodup
    dsimp [List.map, checkNoDupFoldr] at hnodup
    rw [checkNoDupFoldr_snd] at hnodup
    rcases Bool.and_eq_true_iff.mp hnodup with ⟨hnotmem, hrestNodup⟩
    unfold findAdtDecl
    dsimp [List.find?]
    cases hmem with
    | head =>
      have heq : (d.id == d.id) = true := beq_self_eq_true d.id
      rw [heq]
    | tail _ hmemRest =>
      have hidMem : decl.id ∈ rest.map AdtDecl.id :=
        List.mem_map_of_mem hmemRest
      have hne : (d.id == decl.id) = false :=
        checkNotMem_ne_of_mem hnotmem hidMem
      rw [hne]
      exact findAdtDecl_of_mem_nodup hrestNodup hmemRest

theorem checkAdmissibleAdtInv_sound {adts : List AdtDecl}
    (h : checkAdmissibleAdtInv adts = true) :
    AdmissibleAdtInv adts (denoteAdtInv adts) := by
  unfold checkAdmissibleAdtInv at h
  rcases Bool.and_eq_true_iff.mp h with ⟨hnodup, hall⟩
  refine ⟨noDupIds_of_check (fun hf => of_decide_eq_false hf) hnodup, ?_⟩
  intro decl hmem hpub s inner _
  have hfind := findAdtDecl_of_mem_nodup hnodup hmem
  have hinv := findAdtDecl_invariant_none_of_all hall hfind hpub
  unfold denoteAdtInv
  cases adts.all (fun d => d.invariant.isNone) with
  | true => exact True.intro
  | false =>
    dsimp
    rw [hfind]
    cases decl
    dsimp at hinv ⊢
    rw [hinv]
    exact True.intro

/-!
## Section 3: Symbolic Domain (`SymNat`, `SymBool`, `SymVal`), Path Conditions, and `SymState`
-/

/-- Identifier of an input component: `(argLocal, path)`, where `argLocal` is
the 1-based argument local index in the entry state `s₀` and `path` is a
sequence of `0`/`1` steps into `.adt`, `.fieldCons`, or `.ref` pointees. -/
abbrev SymVarId := Nat × List Nat

/-- Single step along an input value path in initial state `s₀`. -/
def stepValPath (s₀ : MirState) : Nat → MirVal → Option MirVal
  | 0, .adt _ inner => some inner
  | 0, .fieldCons h _ => some h
  | 0, .ref frameId gen loc fieldDepth =>
    resolveRef s₀ frameId gen loc fieldDepth
  | 1, .fieldCons _ t => some t
  | _, _ => none

/-- Follow a sequence of path steps starting from `ov : Option MirVal`. -/
def evalInputPathFrom (s₀ : MirState) :
    List Nat → Option MirVal → Option MirVal
  | [], ov => ov
  | step :: rest, some v =>
    evalInputPathFrom s₀ rest (stepValPath s₀ step v)
  | _ :: _, none => none

/-- Evaluate the input component at `vid = (argLocal, path)` in initial state
`s₀`. -/
def evalInputPath (s₀ : MirState) (vid : SymVarId) : Option MirVal :=
  evalInputPathFrom s₀ vid.2 (s₀.locals vid.1)

theorem evalInputPathFrom_append_singleton (s₀ : MirState) :
    ∀ (path : List Nat) (s : Nat) (ov : Option MirVal),
      evalInputPathFrom s₀ (path ++ [s]) ov =
        (evalInputPathFrom s₀ path ov).bind (stepValPath s₀ s)
  | [], _, none => rfl
  | [], _, some _ => rfl
  | _ :: _, _, none => rfl
  | step :: rest, s, some v =>
    evalInputPathFrom_append_singleton s₀ rest s (stepValPath s₀ step v)

theorem evalInputPath_append_singleton (s₀ : MirState) (vid : SymVarId)
    (s : Nat) :
    evalInputPath s₀ (vid.1, vid.2 ++ [s]) =
      (evalInputPath s₀ vid).bind (stepValPath s₀ s) :=
  evalInputPathFrom_append_singleton s₀ vid.2 s (s₀.locals vid.1)

/-- Extract the `Nat` payload of a scalar or opaque-bytes input component at
`vid` in `s₀`. -/
def evalInputScalar (s₀ : MirState) (vid : SymVarId) : Nat :=
  match evalInputPath s₀ vid with
  | some (.usize n) => n
  | some (.bytes _ data) => data
  | _ => 0

/-- Extract the `Bool` payload of a boolean input component at `vid` in `s₀`. -/
def evalInputBool (s₀ : MirState) (vid : SymVarId) : Bool :=
  match evalInputPath s₀ vid with
  | some (.bool b) => b
  | _ => false

/-- Extract the `(loc, fieldDepth)` target of a reference input component at
`vid` in `s₀`. -/
def evalInputRef (s₀ : MirState) (vid : SymVarId) : LocalId × Nat :=
  match evalInputPath s₀ vid with
  | some (.ref _ _ loc d) => (loc, d)
  | _ => (⟨0⟩, 0)

/-- Symbolic natural-number expression denoting a runtime scalar or layout
quantity in `s₀`. -/
inductive SymNat where
  | const (n : Nat)
  | var (vid : SymVarId)
  | tySize (idx : Nat)
  | adtSize (base : Nat) (adtId : Nat)
  | bitPack (lo hi : SymNat) (loBytes : Nat)
  deriving DecidableEq

/-- Denote a `SymNat` in initial state `s₀`. -/
def SymNat.denote (s₀ : MirState) : SymNat → Nat
  | .const n => n
  | .var vid => evalInputScalar s₀ vid
  | .tySize idx => s₀.tySizes idx
  | .adtSize base adtId => s₀.adtPad adtId + base
  | .bitPack lo hi loBytes =>
    lo.denote s₀ + hi.denote s₀ * Nat.pow 2 (8 * loBytes)

/-- Symbolic boolean expression denoting a runtime boolean in `s₀`. -/
inductive SymBool where
  | const (b : Bool)
  | var (vid : SymVarId)
  | eq (a b : SymNat)
  | ne (a b : SymNat)
  | not (x : SymBool)
  deriving DecidableEq

/-- Denote a `SymBool` in initial state `s₀`. -/
def SymBool.denote (s₀ : MirState) : SymBool → Bool
  | .const b => b
  | .var vid => evalInputBool s₀ vid
  | .eq a b => a.denote s₀ == b.denote s₀
  | .ne a b => a.denote s₀ != b.denote s₀
  | .not x => !(x.denote s₀)

instance : DecidableEq LocalId
  | ⟨a⟩, ⟨b⟩ =>
    if h : a = b then isTrue (congrArg LocalId.mk h)
    else isFalse (fun heq => by injection heq with hab; exact h hab)

/-- Symbolic MIR value tracking scalars, booleans, structs, opaque generic
bytes, frame-local references, and caller-owned references. -/
inductive SymVal where
  | uninit
  | usize (n : SymNat)
  | bool (b : SymBool)
  | unit
  | adt (id : Nat) (v : SymVal)
  | fieldCons (h : SymVal) (t : SymVal)
  | bytes (size : SymNat) (data : SymNat)
  | ref (frameId : Nat) (gen : Nat) (loc : LocalId) (fieldDepth : Nat)
  | callerRef (vid : SymVarId) (extraDepth : Nat)
  deriving DecidableEq

/-- Denote a `SymVal` in initial state `s₀`. -/
def SymVal.denote (s₀ : MirState) : SymVal → MirVal
  | .uninit => .uninit
  | .usize n => .usize (n.denote s₀)
  | .bool b => .bool (b.denote s₀)
  | .unit => .unit
  | .adt id v => .adt id (v.denote s₀)
  | .fieldCons h t => .fieldCons (h.denote s₀) (t.denote s₀)
  | .bytes sz data => .bytes (sz.denote s₀) (data.denote s₀)
  | .ref frameId gen loc fieldDepth => .ref frameId gen loc fieldDepth
  | .callerRef vid extraDepth =>
    let r := evalInputRef s₀ vid
    .ref 0 0 r.1 (r.2 + extraDepth)

/-- Whether a `SymVal` is fully initialized (contains no `.uninit` sub-value). -/
def SymVal.isFullyInit : SymVal → Bool
  | .uninit => false
  | .usize _ | .bool _ | .unit | .bytes _ _
  | .ref _ _ _ _ | .callerRef _ _ => true
  | .adt _ inner => inner.isFullyInit
  | .fieldCons h t => h.isFullyInit && t.isFullyInit

theorem SymVal.isFullyInit_denote (s₀ : MirState) :
    ∀ (v : SymVal), (v.denote s₀).isFullyInit = v.isFullyInit
  | .uninit => rfl
  | .usize _ | .bool _ | .unit | .bytes _ _
  | .ref _ _ _ _ | .callerRef _ _ => rfl
  | .adt _ inner => SymVal.isFullyInit_denote s₀ inner
  | .fieldCons h t => by
    dsimp [SymVal.denote, MirVal.isFullyInit, SymVal.isFullyInit]
    rw [SymVal.isFullyInit_denote s₀ h, SymVal.isFullyInit_denote s₀ t]

/-- Pack a list of `SymVal` field values into a struct payload. -/
def symPackFields : List SymVal → SymVal
  | [] => .unit
  | [v] => v
  | v :: rest => .fieldCons v (symPackFields rest)

theorem symPackFields_denote (s₀ : MirState) :
    ∀ (vs : List SymVal),
      (symPackFields vs).denote s₀ = packFields (vs.map (SymVal.denote s₀))
  | [] => rfl
  | [_] => rfl
  | v :: w :: rest =>
    congrArg (MirVal.fieldCons (v.denote s₀))
      (symPackFields_denote s₀ (w :: rest))

/-- Extract field `0` from a symbolic struct payload. -/
def symFirstFieldVal : SymVal → SymVal
  | .fieldCons h _ => h
  | v => v

theorem symFirstFieldVal_denote (s₀ : MirState) :
    ∀ (v : SymVal),
      (symFirstFieldVal v).denote s₀ = firstFieldVal (v.denote s₀)
  | .uninit | .usize _ | .bool _ | .unit | .adt _ _
  | .bytes _ _ | .ref _ _ _ _ | .callerRef _ _ => rfl
  | .fieldCons _ _ => rfl

/-- Extract field `idx` from a symbolic struct payload. -/
def symGetFieldVal : Nat → SymVal → Option SymVal
  | 0, v => some (symFirstFieldVal v)
  | i + 1, .fieldCons _ t => symGetFieldVal i t
  | _ + 1, _ => none

theorem symGetFieldVal_denote (s₀ : MirState) :
    ∀ (idx : Nat) (v : SymVal),
      (symGetFieldVal idx v).map (SymVal.denote s₀) =
        getFieldVal idx (v.denote s₀)
  | 0, v => by
    dsimp [symGetFieldVal, getFieldVal, Option.map]
    exact congrArg some (symFirstFieldVal_denote s₀ v)
  | i + 1, .fieldCons _ t => symGetFieldVal_denote s₀ i t
  | _ + 1, .uninit | _ + 1, .usize _ | _ + 1, .bool _ | _ + 1, .unit
  | _ + 1, .adt _ _ | _ + 1, .bytes _ _ | _ + 1, .ref _ _ _ _
  | _ + 1, .callerRef _ _ => rfl

/-- Replace field `idx` in a symbolic struct payload with `newField`. -/
def symSetFieldVal (newField : SymVal) : Nat → SymVal → Option SymVal
  | 0, .fieldCons _ t => some (.fieldCons newField t)
  | 0, _ => some newField
  | i + 1, .fieldCons h t => (symSetFieldVal newField i t).map (.fieldCons h)
  | _ + 1, _ => none

theorem symSetFieldVal_denote (s₀ : MirState) (newField : SymVal) :
    ∀ (idx : Nat) (v : SymVal),
      (symSetFieldVal newField idx v).map (SymVal.denote s₀) =
        setFieldVal (newField.denote s₀) idx (v.denote s₀)
  | 0, .fieldCons _ _ => rfl
  | 0, .uninit | 0, .usize _ | 0, .bool _ | 0, .unit
  | 0, .adt _ _ | 0, .bytes _ _ | 0, .ref _ _ _ _ | 0, .callerRef _ _ => rfl
  | i + 1, .fieldCons h t => by
    dsimp [symSetFieldVal, setFieldVal, SymVal.denote]
    rw [← symSetFieldVal_denote s₀ newField i t]
    cases symSetFieldVal newField i t <;> rfl
  | _ + 1, .uninit | _ + 1, .usize _ | _ + 1, .bool _ | _ + 1, .unit
  | _ + 1, .adt _ _ | _ + 1, .bytes _ _ | _ + 1, .ref _ _ _ _
  | _ + 1, .callerRef _ _ => rfl

/-- Peel `d` `.field 0` projections off `.adt` wrappers in a `SymVal`. -/
def symPeelFields : Nat → SymVal → Option SymVal
  | 0, v => some v
  | d + 1, .adt _ inner => symPeelFields d (symFirstFieldVal inner)
  | _ + 1, _ => none

theorem symPeelFields_denote (s₀ : MirState) :
    ∀ (d : Nat) (v : SymVal),
      (symPeelFields d v).map (SymVal.denote s₀) =
        peelFields d (v.denote s₀)
  | 0, _ => rfl
  | d + 1, .adt _ inner => by
    dsimp [symPeelFields, peelFields, SymVal.denote]
    rw [← symFirstFieldVal_denote s₀ inner]
    exact symPeelFields_denote s₀ d (symFirstFieldVal inner)
  | _ + 1, .uninit | _ + 1, .usize _ | _ + 1, .bool _ | _ + 1, .unit
  | _ + 1, .fieldCons _ _ | _ + 1, .bytes _ _ | _ + 1, .ref _ _ _ _
  | _ + 1, .callerRef _ _ => rfl

theorem peelFields_add :
    ∀ (d1 d2 : Nat) (v : MirVal),
      peelFields (d1 + d2) v = (peelFields d1 v).bind (peelFields d2)
  | 0, d2, v => by
    rw [Nat.zero_add]
    rfl
  | d1 + 1, d2, .adt id inner => by
    rw [Nat.succ_add]
    dsimp [peelFields]
    exact peelFields_add d1 d2 (firstFieldVal inner)
  | d1 + 1, d2, .uninit | d1 + 1, d2, .usize _ | d1 + 1, d2, .bool _
  | d1 + 1, d2, .unit | d1 + 1, d2, .fieldCons _ _ | d1 + 1, d2, .bytes _ _
  | d1 + 1, d2, .ref _ _ _ _ => by
    rw [Nat.succ_add]
    rfl

/-!
### Path Conditions (`PathCond`) and Branch Splits (`SymSplit`)
-/

/-- Finite path condition tracking constraints accumulated along a symbolic
execution branch. -/
structure PathCond where
  /-- Known equality constraints `evalInputScalar s₀ vid = k`. -/
  varEq : List (SymVarId × Nat) := []
  /-- Known disequality constraints `evalInputScalar s₀ vid ≠ k`. -/
  varNe : List (SymVarId × Nat) := []
  /-- Known boolean variable assignments `evalInputBool s₀ vid = b`. -/
  boolEq : List (SymVarId × Bool) := []
  /-- Known `s₀.adtPad id = 0` vs `0 < s₀.adtPad id` (`true` = zero padding,
  `false` = positive padding). -/
  adtPadZero : List (Nat × Bool) := []
  /-- Known equality constraints `s₀.tySizes idx = k`. -/
  tySizeEq : List (Nat × Nat) := []
  /-- Known disequality constraints `s₀.tySizes idx ≠ k`. -/
  tySizeNe : List (Nat × Nat) := []
  /-- Optional constraint on `s₀.ubChecks`. -/
  ubChecks : Option Bool := none
  /-- Caller-owned reference pointee table `(vid, ptVal)` populated at entry. -/
  callerRefs : List (SymVarId × SymVal) := []
  /-- Entry argument local bindings `(argLocal, symVal)` populated at entry. -/
  initArgs : List (Nat × SymVal) := []

/-- Semantic satisfaction of `pc : PathCond` by initial state `s₀` (for a root
function with `rootLC` locals). -/
def PathCond.Matches (rootLC : Nat) (s₀ : MirState) (pc : PathCond) : Prop :=
  (∀ p ∈ pc.varEq, evalInputScalar s₀ p.1 = p.2) ∧
  (∀ p ∈ pc.varNe, evalInputScalar s₀ p.1 ≠ p.2) ∧
  (∀ p ∈ pc.boolEq, evalInputBool s₀ p.1 = p.2) ∧
  (∀ p ∈ pc.adtPadZero,
    if p.2 then s₀.adtPad p.1 = 0 else 0 < s₀.adtPad p.1) ∧
  (∀ p ∈ pc.tySizeEq, s₀.tySizes p.1 = p.2) ∧
  (∀ p ∈ pc.tySizeNe, s₀.tySizes p.1 ≠ p.2) ∧
  (match pc.ubChecks with
   | none => True
   | some b => s₀.ubChecks = b) ∧
  (∀ p ∈ pc.callerRefs,
    rootLC ≤ (evalInputRef s₀ p.1).1.index ∧
    s₀.frameId = 0 ∧
    s₀.localGens (evalInputRef s₀ p.1).1.index = 0 ∧
    resolveRef s₀ 0 0 (evalInputRef s₀ p.1).1 (evalInputRef s₀ p.1).2 =
      some (p.2.denote s₀)) ∧
  (∀ p ∈ pc.initArgs, s₀.locals p.1 = some (p.2.denote s₀))

/-- Whether `pc` refutes the pinned zero-extra-padding world
`s₀.adtPad = (fun _ => 0) ∧ s₀.tySizes = (fun _ => 8)`. -/
def PathCond.refutesPinnedWorld (pc : PathCond) : Bool :=
  pc.adtPadZero.any (fun p => !p.2) ||
  pc.tySizeEq.any (fun p => p.2 != 8) ||
  pc.tySizeNe.any (fun p => p.2 == 8)

theorem list_any_iff_exists {α : Type} {p : α → Bool} {xs : List α} :
    xs.any p = true → ∃ x ∈ xs, p x = true := by
  induction xs with
  | nil => intro h; cases h
  | cons x xs ih =>
    dsimp [List.any]
    intro h
    cases hpx : p x with
    | true => exact ⟨x, .head _, hpx⟩
    | false =>
      rw [hpx, Bool.false_or] at h
      rcases ih h with ⟨y, hmem, hpy⟩
      exact ⟨y, .tail _ hmem, hpy⟩

theorem refutesPinnedWorld_sound {rootLC : Nat} {s₀ : MirState} {pc : PathCond}
    (hmatch : pc.Matches rootLC s₀)
    (href : pc.refutesPinnedWorld = true) :
    ¬ (s₀.adtPad = (fun _ => 0) ∧ s₀.tySizes = (fun _ => 8)) := by
  intro ⟨hpad, hty⟩
  unfold PathCond.refutesPinnedWorld at href
  rcases Bool.or_eq_true_iff.mp href with h12 | h3
  · rcases Bool.or_eq_true_iff.mp h12 with h1 | h2
    · rcases list_any_iff_exists h1 with ⟨p, hmem, hp⟩
      have hm := hmatch.2.2.2.1 p hmem
      cases hb : p.2 with
      | true => rw [hb] at hp; cases hp
      | false =>
        rw [hb] at hm
        dsimp at hm
        rw [hpad] at hm
        exact Nat.lt_irrefl 0 hm
    · rcases list_any_iff_exists h2 with ⟨p, hmem, hp⟩
      have hm := hmatch.2.2.2.2.1 p hmem
      rw [hty] at hm
      dsimp at hm
      rw [← hm] at hp
      cases hp
  · rcases list_any_iff_exists h3 with ⟨p, hmem, hp⟩
    have hm := hmatch.2.2.2.2.2.1 p hmem
    rw [hty] at hm
    dsimp at hm
    have heq : p.2 = 8 := eq_of_beq hp
    exact hm heq.symm

/-- Case-split directive emitted when symbolic execution encounters an
unconstrained symbolic variable, layout parameter, or `ubChecks` flag. -/
inductive SymSplit where
  | adtPad (adtId : Nat)
  | tySizeVal (idx : Nat) (val : Nat)
  | varVal (vid : SymVarId) (val : Nat)
  | boolVar (vid : SymVarId)
  | ubChecks
  deriving DecidableEq

/-- Refine `pc : PathCond` along the two complementary branches (`true` vs
`false`) of a `SymSplit`. -/
def applySplit (pc : PathCond) : SymSplit → PathCond × PathCond
  | .adtPad adtId =>
    ({ pc with adtPadZero := (adtId, true) :: pc.adtPadZero },
     { pc with adtPadZero := (adtId, false) :: pc.adtPadZero })
  | .tySizeVal idx val =>
    ({ pc with tySizeEq := (idx, val) :: pc.tySizeEq },
     { pc with tySizeNe := (idx, val) :: pc.tySizeNe })
  | .varVal vid val =>
    ({ pc with varEq := (vid, val) :: pc.varEq },
     { pc with varNe := (vid, val) :: pc.varNe })
  | .boolVar vid =>
    ({ pc with boolEq := (vid, true) :: pc.boolEq },
     { pc with boolEq := (vid, false) :: pc.boolEq })
  | .ubChecks =>
    ({ pc with ubChecks := some true },
     { pc with ubChecks := some false })

theorem applySplit_complete (rootLC : Nat) (s₀ : MirState) (pc : PathCond)
    (sp : SymSplit) (h : pc.Matches rootLC s₀) :
    (applySplit pc sp).1.Matches rootLC s₀ ∨
      (applySplit pc sp).2.Matches rootLC s₀ := by
  rcases h with ⟨hveq, hvne, hbeq, hpad, hteq, htne, hub, hcref, hinit⟩
  cases sp with
  | adtPad adtId =>
    cases h0 : s₀.adtPad adtId with
    | zero =>
      refine Or.inl ⟨hveq, hvne, hbeq, ?_, hteq, htne, hub, hcref, hinit⟩
      intro p hp
      cases hp with
      | head => exact h0
      | tail _ hmem => exact hpad p hmem
    | succ k =>
      refine Or.inr ⟨hveq, hvne, hbeq, ?_, hteq, htne, hub, hcref, hinit⟩
      intro p hp
      cases hp with
      | head =>
        dsimp
        rw [h0]
        exact Nat.zero_lt_succ k
      | tail _ hmem => exact hpad p hmem
  | tySizeVal idx val =>
    cases hdec : decide (s₀.tySizes idx = val) with
    | true =>
      refine Or.inl ⟨hveq, hvne, hbeq, hpad, ?_, htne, hub, hcref, hinit⟩
      intro p hp
      cases hp with
      | head => exact of_decide_eq_true hdec
      | tail _ hmem => exact hteq p hmem
    | false =>
      refine Or.inr ⟨hveq, hvne, hbeq, hpad, hteq, ?_, hub, hcref, hinit⟩
      intro p hp
      cases hp with
      | head => exact of_decide_eq_false hdec
      | tail _ hmem => exact htne p hmem
  | varVal vid val =>
    cases hdec : decide (evalInputScalar s₀ vid = val) with
    | true =>
      refine Or.inl ⟨?_, hvne, hbeq, hpad, hteq, htne, hub, hcref, hinit⟩
      intro p hp
      cases hp with
      | head => exact of_decide_eq_true hdec
      | tail _ hmem => exact hveq p hmem
    | false =>
      refine Or.inr ⟨hveq, ?_, hbeq, hpad, hteq, htne, hub, hcref, hinit⟩
      intro p hp
      cases hp with
      | head => exact of_decide_eq_false hdec
      | tail _ hmem => exact hvne p hmem
  | boolVar vid =>
    cases hb : evalInputBool s₀ vid with
    | true =>
      refine Or.inl ⟨hveq, hvne, ?_, hpad, hteq, htne, hub, hcref, hinit⟩
      intro p hp
      cases hp with
      | head => exact hb
      | tail _ hmem => exact hbeq p hmem
    | false =>
      refine Or.inr ⟨hveq, hvne, ?_, hpad, hteq, htne, hub, hcref, hinit⟩
      intro p hp
      cases hp with
      | head => exact hb
      | tail _ hmem => exact hbeq p hmem
  | ubChecks =>
    cases hub0 : s₀.ubChecks with
    | true =>
      exact Or.inl ⟨hveq, hvne, hbeq, hpad, hteq, htne, hub0, hcref, hinit⟩
    | false =>
      exact Or.inr ⟨hveq, hvne, hbeq, hpad, hteq, htne, hub0, hcref, hinit⟩

/-!
### Evaluating `SymNat` and `SymBool` Under `PathCond`
-/

theorem list_find_some_mem {α : Type} {p : α → Bool} {xs : List α} {x : α}
    (h : xs.find? p = some x) : x ∈ xs ∧ p x = true := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    dsimp [List.find?] at h
    cases hpy : p y with
    | true =>
      rw [hpy] at h
      injection h with hy
      subst hy
      exact ⟨.head _, hpy⟩
    | false =>
      rw [hpy] at h
      rcases ih h with ⟨hmem, hpx⟩
      exact ⟨.tail _ hmem, hpx⟩

/-- Simplify a `SymNat` to a concrete constant when `pc` fixes its value. -/
def evalSymNatUnder (pc : PathCond) : SymNat → SymNat
  | .const n => .const n
  | .var vid =>
    match pc.varEq.find? (fun p => decide (p.1 = vid)) with
    | some (_, k) => .const k
    | none => .var vid
  | .tySize idx =>
    match pc.tySizeEq.find? (fun p => decide (p.1 = idx)) with
    | some (_, k) => .const k
    | none => .tySize idx
  | .adtSize base adtId =>
    match pc.adtPadZero.find? (fun p => decide (p.1 = adtId)) with
    | some (_, true) => .const base
    | _ => .adtSize base adtId
  | .bitPack lo hi loBytes => .bitPack lo hi loBytes

theorem evalSymNatUnder_sound {rootLC : Nat} {s₀ : MirState} {pc : PathCond}
    (hmatch : pc.Matches rootLC s₀) (x : SymNat) :
    (evalSymNatUnder pc x).denote s₀ = x.denote s₀ := by
  cases x with
  | const n => rfl
  | bitPack lo hi loBytes => rfl
  | var vid =>
    dsimp [evalSymNatUnder]
    cases hfind : pc.varEq.find? (fun p => decide (p.1 = vid)) with
    | none => rfl
    | some p =>
      rcases list_find_some_mem hfind with ⟨hmem, hdec⟩
      rcases p with ⟨v', k⟩
      have hv : v' = vid := of_decide_eq_true hdec
      subst hv
      have heq := hmatch.1 (v', k) hmem
      dsimp [SymNat.denote]
      exact heq.symm
  | tySize idx =>
    dsimp [evalSymNatUnder]
    cases hfind : pc.tySizeEq.find? (fun p => decide (p.1 = idx)) with
    | none => rfl
    | some p =>
      rcases list_find_some_mem hfind with ⟨hmem, hdec⟩
      rcases p with ⟨idx', k⟩
      have hi : idx' = idx := of_decide_eq_true hdec
      subst hi
      have heq := hmatch.2.2.2.2.1 (idx', k) hmem
      dsimp [SymNat.denote]
      exact heq.symm
  | adtSize base adtId =>
    dsimp [evalSymNatUnder]
    cases hfind : pc.adtPadZero.find? (fun p => decide (p.1 = adtId)) with
    | none => rfl
    | some p =>
      rcases list_find_some_mem hfind with ⟨hmem, hdec⟩
      rcases p with ⟨id', b⟩
      cases b with
      | false => rfl
      | true =>
        have hid : id' = adtId := of_decide_eq_true hdec
        subst hid
        have hpad : s₀.adtPad id' = 0 := hmatch.2.2.2.1 (id', true) hmem
        dsimp [SymNat.denote]
        rw [hpad, Nat.zero_add]

/-- Result of evaluating a symbolic condition under `pc`: either a decided
boolean `.val b`, a required branch split `.needSplit sp`, or `.unknown`. -/
inductive SymEvalRes (α : Type) where
  | val (v : α)
  | needSplit (sp : SymSplit)
  | unknown
  deriving DecidableEq

/-- Decide equality between two already-simplified `SymNat` expressions under
`pc`, assuming `a' ≠ b'`. -/
def evalSymNatEqDistinct (pc : PathCond) : SymNat → SymNat → SymEvalRes Bool
  | .const n1, .const n2 => .val (n1 == n2)
  | .var vid, .const k =>
    if pc.varNe.any (fun p => decide (p.1 = vid) && decide (p.2 = k)) then
      .val false
    else
      .needSplit (.varVal vid k)
  | .const k, .var vid =>
    if pc.varNe.any (fun p => decide (p.1 = vid) && decide (p.2 = k)) then
      .val false
    else
      .needSplit (.varVal vid k)
  | .tySize idx, .const k =>
    if pc.tySizeNe.any (fun p => decide (p.1 = idx) && decide (p.2 = k)) then
      .val false
    else
      .needSplit (.tySizeVal idx k)
  | .const k, .tySize idx =>
    if pc.tySizeNe.any (fun p => decide (p.1 = idx) && decide (p.2 = k)) then
      .val false
    else
      .needSplit (.tySizeVal idx k)
  | .adtSize base adtId, .const k =>
    match pc.adtPadZero.find? (fun p => decide (p.1 = adtId)) with
    | some (_, false) =>
      if decide (k ≤ base) then .val false else .unknown
    | some (_, true) => .val (base == k)
    | none => .needSplit (.adtPad adtId)
  | .const k, .adtSize base adtId =>
    match pc.adtPadZero.find? (fun p => decide (p.1 = adtId)) with
    | some (_, false) =>
      if decide (k ≤ base) then .val false else .unknown
    | some (_, true) => .val (k == base)
    | none => .needSplit (.adtPad adtId)
  | .adtSize base adtId, .tySize idx =>
    match pc.adtPadZero.find? (fun p => decide (p.1 = adtId)) with
    | none => .needSplit (.adtPad adtId)
    | some (_, true) =>
      if pc.tySizeNe.any (fun p => decide (p.1 = idx) && decide (p.2 = base)) then
        .val false
      else
        .needSplit (.tySizeVal idx base)
    | some (_, false) =>
      match pc.tySizeEq.find? (fun p => decide (p.1 = idx)) with
      | some (_, k) =>
        if decide (k ≤ base) then .val false else .unknown
      | none => .needSplit (.tySizeVal idx base)
  | .tySize idx, .adtSize base adtId =>
    match pc.adtPadZero.find? (fun p => decide (p.1 = adtId)) with
    | none => .needSplit (.adtPad adtId)
    | some (_, true) =>
      if pc.tySizeNe.any (fun p => decide (p.1 = idx) && decide (p.2 = base)) then
        .val false
      else
        .needSplit (.tySizeVal idx base)
    | some (_, false) =>
      match pc.tySizeEq.find? (fun p => decide (p.1 = idx)) with
      | some (_, k) =>
        if decide (k ≤ base) then .val false else .unknown
      | none => .needSplit (.tySizeVal idx base)
  | _, _ => .unknown

/-- Decide equality `a == b` between two `SymNat` expressions under `pc`,
requesting a finite `SymSplit` when an unconstrained symbolic quantity is
compared against a constant. -/
def evalSymNatEq (pc : PathCond) (a b : SymNat) : SymEvalRes Bool :=
  let a' := evalSymNatUnder pc a
  let b' := evalSymNatUnder pc b
  if decide (a' = b') then
    .val true
  else
    evalSymNatEqDistinct pc a' b'

theorem evalSymNatEqDistinct_sound {rootLC : Nat} {s₀ : MirState} {pc : PathCond}
    (hmatch : pc.Matches rootLC s₀) :
    ∀ (a' b' : SymNat) {res : Bool},
      evalSymNatEqDistinct pc a' b' = .val res →
      (a'.denote s₀ == b'.denote s₀) = res
  | .const n1, .const n2, _, heval => by
    injection heval with hres
  | .var vid, .const k, _, heval => by
    dsimp [evalSymNatEqDistinct] at heval
    cases hany : pc.varNe.any (fun p => decide (p.1 = vid) && decide (p.2 = k)) with
    | false => rw [hany] at heval; cases heval
    | true =>
      rw [hany] at heval
      injection heval with hres
      subst hres
      rcases list_any_iff_exists hany with ⟨p, hmem, hp⟩
      rcases Bool.and_eq_true_iff.mp hp with ⟨hp1, hp2⟩
      rcases p with ⟨v', k'⟩
      have hv : v' = vid := of_decide_eq_true hp1
      have hk : k' = k := of_decide_eq_true hp2
      subst hv; subst hk
      have hne := hmatch.2.1 (v', k') hmem
      exact beq_eq_false_iff_ne.mpr hne
  | .const k, .var vid, _, heval => by
    dsimp [evalSymNatEqDistinct] at heval
    cases hany : pc.varNe.any (fun p => decide (p.1 = vid) && decide (p.2 = k)) with
    | false => rw [hany] at heval; cases heval
    | true =>
      rw [hany] at heval
      injection heval with hres
      subst hres
      rcases list_any_iff_exists hany with ⟨p, hmem, hp⟩
      rcases Bool.and_eq_true_iff.mp hp with ⟨hp1, hp2⟩
      rcases p with ⟨v', k'⟩
      have hv : v' = vid := of_decide_eq_true hp1
      have hk : k' = k := of_decide_eq_true hp2
      subst hv; subst hk
      have hne := hmatch.2.1 (v', k') hmem
      exact beq_eq_false_iff_ne.mpr (Ne.symm hne)
  | .tySize idx, .const k, _, heval => by
    dsimp [evalSymNatEqDistinct] at heval
    cases hany : pc.tySizeNe.any (fun p => decide (p.1 = idx) && decide (p.2 = k)) with
    | false => rw [hany] at heval; cases heval
    | true =>
      rw [hany] at heval
      injection heval with hres
      subst hres
      rcases list_any_iff_exists hany with ⟨p, hmem, hp⟩
      rcases Bool.and_eq_true_iff.mp hp with ⟨hp1, hp2⟩
      rcases p with ⟨i', k'⟩
      have hi : i' = idx := of_decide_eq_true hp1
      have hk : k' = k := of_decide_eq_true hp2
      subst hi; subst hk
      have hne := hmatch.2.2.2.2.2.1 (i', k') hmem
      exact beq_eq_false_iff_ne.mpr hne
  | .const k, .tySize idx, _, heval => by
    dsimp [evalSymNatEqDistinct] at heval
    cases hany : pc.tySizeNe.any (fun p => decide (p.1 = idx) && decide (p.2 = k)) with
    | false => rw [hany] at heval; cases heval
    | true =>
      rw [hany] at heval
      injection heval with hres
      subst hres
      rcases list_any_iff_exists hany with ⟨p, hmem, hp⟩
      rcases Bool.and_eq_true_iff.mp hp with ⟨hp1, hp2⟩
      rcases p with ⟨i', k'⟩
      have hi : i' = idx := of_decide_eq_true hp1
      have hk : k' = k := of_decide_eq_true hp2
      subst hi; subst hk
      have hne := hmatch.2.2.2.2.2.1 (i', k') hmem
      exact beq_eq_false_iff_ne.mpr (Ne.symm hne)
  | .adtSize base adtId, .const k, _, heval => by
    dsimp [evalSymNatEqDistinct] at heval
    cases hfind : pc.adtPadZero.find? (fun p => decide (p.1 = adtId)) with
    | none => rw [hfind] at heval; cases heval
    | some p =>
      rcases list_find_some_mem hfind with ⟨hmem, hdecId⟩
      rcases p with ⟨id', b⟩
      have hid : id' = adtId := of_decide_eq_true hdecId
      subst hid
      cases b with
      | true =>
        rw [hfind] at heval
        injection heval with hres
        subst hres
        have hpad : s₀.adtPad id' = 0 := hmatch.2.2.2.1 (id', true) hmem
        dsimp [SymNat.denote]
        rw [hpad, Nat.zero_add]
      | false =>
        rw [hfind] at heval
        dsimp at heval
        cases hle : decide (k ≤ base) with
        | false => rw [hle] at heval; cases heval
        | true =>
          rw [hle] at heval
          injection heval with hres
          subst hres
          have hpad : 0 < s₀.adtPad id' := hmatch.2.2.2.1 (id', false) hmem
          have hle' : k ≤ base := of_decide_eq_true hle
          dsimp [SymNat.denote]
          have hne : s₀.adtPad id' + base ≠ k := by omega
          exact beq_eq_false_iff_ne.mpr hne
  | .const k, .adtSize base adtId, _, heval => by
    dsimp [evalSymNatEqDistinct] at heval
    cases hfind : pc.adtPadZero.find? (fun p => decide (p.1 = adtId)) with
    | none => rw [hfind] at heval; cases heval
    | some p =>
      rcases list_find_some_mem hfind with ⟨hmem, hdecId⟩
      rcases p with ⟨id', b⟩
      have hid : id' = adtId := of_decide_eq_true hdecId
      subst hid
      cases b with
      | true =>
        rw [hfind] at heval
        injection heval with hres
        subst hres
        have hpad : s₀.adtPad id' = 0 := hmatch.2.2.2.1 (id', true) hmem
        dsimp [SymNat.denote]
        rw [hpad, Nat.zero_add]
      | false =>
        rw [hfind] at heval
        dsimp at heval
        cases hle : decide (k ≤ base) with
        | false => rw [hle] at heval; cases heval
        | true =>
          rw [hle] at heval
          injection heval with hres
          subst hres
          have hpad : 0 < s₀.adtPad id' := hmatch.2.2.2.1 (id', false) hmem
          have hle' : k ≤ base := of_decide_eq_true hle
          dsimp [SymNat.denote]
          have hne : k ≠ s₀.adtPad id' + base := by omega
          exact beq_eq_false_iff_ne.mpr hne
  | .adtSize base adtId, .tySize idx, _, heval => by
    dsimp [evalSymNatEqDistinct] at heval
    cases hfind : pc.adtPadZero.find? (fun p => decide (p.1 = adtId)) with
    | none => rw [hfind] at heval; cases heval
    | some p =>
      rcases list_find_some_mem hfind with ⟨hmem, hdecId⟩
      rcases p with ⟨id', b⟩
      have hid : id' = adtId := of_decide_eq_true hdecId
      subst hid
      cases b with
      | true =>
        rw [hfind] at heval
        dsimp at heval
        cases hany : pc.tySizeNe.any (fun p => decide (p.1 = idx) && decide (p.2 = base)) with
        | false => rw [hany] at heval; cases heval
        | true =>
          rw [hany] at heval
          injection heval with hres
          subst hres
          rcases list_any_iff_exists hany with ⟨q, hqmem, hqp⟩
          rcases Bool.and_eq_true_iff.mp hqp with ⟨hqi, hqb⟩
          rcases q with ⟨i', b'⟩
          have hi : i' = idx := of_decide_eq_true hqi
          have hb : b' = base := of_decide_eq_true hqb
          subst hi; subst hb
          have hpad : s₀.adtPad id' = 0 := hmatch.2.2.2.1 (id', true) hmem
          have hne := hmatch.2.2.2.2.2.1 (i', b') hqmem
          dsimp [SymNat.denote]
          rw [hpad, Nat.zero_add]
          exact beq_eq_false_iff_ne.mpr (Ne.symm hne)
      | false =>
        rw [hfind] at heval
        dsimp at heval
        cases hteq : pc.tySizeEq.find? (fun p => decide (p.1 = idx)) with
        | none => rw [hteq] at heval; cases heval
        | some q =>
          rcases list_find_some_mem hteq with ⟨hqmem, hqi⟩
          rcases q with ⟨i', k⟩
          have hi : i' = idx := of_decide_eq_true hqi
          subst hi
          rw [hteq] at heval
          dsimp at heval
          cases hle : decide (k ≤ base) with
          | false => rw [hle] at heval; cases heval
          | true =>
            rw [hle] at heval
            injection heval with hres
            subst hres
            have hpad : 0 < s₀.adtPad id' := hmatch.2.2.2.1 (id', false) hmem
            have hsz : s₀.tySizes i' = k := hmatch.2.2.2.2.1 (i', k) hqmem
            have hle' : k ≤ base := of_decide_eq_true hle
            dsimp [SymNat.denote]
            rw [hsz]
            have hne : s₀.adtPad id' + base ≠ k := by omega
            exact beq_eq_false_iff_ne.mpr hne
  | .tySize idx, .adtSize base adtId, _, heval => by
    dsimp [evalSymNatEqDistinct] at heval
    cases hfind : pc.adtPadZero.find? (fun p => decide (p.1 = adtId)) with
    | none => rw [hfind] at heval; cases heval
    | some p =>
      rcases list_find_some_mem hfind with ⟨hmem, hdecId⟩
      rcases p with ⟨id', b⟩
      have hid : id' = adtId := of_decide_eq_true hdecId
      subst hid
      cases b with
      | true =>
        rw [hfind] at heval
        dsimp at heval
        cases hany : pc.tySizeNe.any (fun p => decide (p.1 = idx) && decide (p.2 = base)) with
        | false => rw [hany] at heval; cases heval
        | true =>
          rw [hany] at heval
          injection heval with hres
          subst hres
          rcases list_any_iff_exists hany with ⟨q, hqmem, hqp⟩
          rcases Bool.and_eq_true_iff.mp hqp with ⟨hqi, hqb⟩
          rcases q with ⟨i', b'⟩
          have hi : i' = idx := of_decide_eq_true hqi
          have hb : b' = base := of_decide_eq_true hqb
          subst hi; subst hb
          have hpad : s₀.adtPad id' = 0 := hmatch.2.2.2.1 (id', true) hmem
          have hne := hmatch.2.2.2.2.2.1 (i', b') hqmem
          dsimp [SymNat.denote]
          rw [hpad, Nat.zero_add]
          exact beq_eq_false_iff_ne.mpr hne
      | false =>
        rw [hfind] at heval
        dsimp at heval
        cases hteq : pc.tySizeEq.find? (fun p => decide (p.1 = idx)) with
        | none => rw [hteq] at heval; cases heval
        | some q =>
          rcases list_find_some_mem hteq with ⟨hqmem, hqi⟩
          rcases q with ⟨i', k⟩
          have hi : i' = idx := of_decide_eq_true hqi
          subst hi
          rw [hteq] at heval
          dsimp at heval
          cases hle : decide (k ≤ base) with
          | false => rw [hle] at heval; cases heval
          | true =>
            rw [hle] at heval
            injection heval with hres
            subst hres
            have hpad : 0 < s₀.adtPad id' := hmatch.2.2.2.1 (id', false) hmem
            have hsz : s₀.tySizes i' = k := hmatch.2.2.2.2.1 (i', k) hqmem
            have hle' : k ≤ base := of_decide_eq_true hle
            dsimp [SymNat.denote]
            rw [hsz]
            have hne : k ≠ s₀.adtPad id' + base := by omega
            exact beq_eq_false_iff_ne.mpr hne
  | .var _, .var _, _, heval => by cases heval
  | .var _, .tySize _, _, heval => by cases heval
  | .var _, .adtSize _ _, _, heval => by cases heval
  | .tySize _, .var _, _, heval => by cases heval
  | .tySize _, .tySize _, _, heval => by cases heval
  | .adtSize _ _, .var _, _, heval => by cases heval
  | .adtSize _ _, .adtSize _ _, _, heval => by cases heval
  | .bitPack _ _ _, _, _, heval => by cases heval
  | .const _, .bitPack _ _ _, _, heval => by cases heval
  | .var _, .bitPack _ _ _, _, heval => by cases heval
  | .tySize _, .bitPack _ _ _, _, heval => by cases heval
  | .adtSize _ _, .bitPack _ _ _, _, heval => by cases heval

theorem evalSymNatEq_sound {rootLC : Nat} {s₀ : MirState} {pc : PathCond}
    (hmatch : pc.Matches rootLC s₀) (a b : SymNat) {res : Bool}
    (heval : evalSymNatEq pc a b = .val res) :
    (a.denote s₀ == b.denote s₀) = res := by
  unfold evalSymNatEq at heval
  dsimp at heval
  cases hdec : decide (evalSymNatUnder pc a = evalSymNatUnder pc b) with
  | true =>
    rw [hdec] at heval
    injection heval with hres
    subst hres
    have heq :
        (evalSymNatUnder pc a).denote s₀ = (evalSymNatUnder pc b).denote s₀ :=
      congrArg (SymNat.denote s₀) (of_decide_eq_true hdec)
    rw [evalSymNatUnder_sound hmatch a, evalSymNatUnder_sound hmatch b] at heq
    rw [heq]
    exact beq_self_eq_true _
  | false =>
    rw [hdec] at heval
    have hcore :=
      evalSymNatEqDistinct_sound hmatch (evalSymNatUnder pc a)
        (evalSymNatUnder pc b) heval
    rw [evalSymNatUnder_sound hmatch a, evalSymNatUnder_sound hmatch b] at hcore
    exact hcore

/-- Evaluate a `SymBool` under `pc`, requesting a `SymSplit` when an
unconstrained symbolic variable or layout parameter is encountered. -/
def evalSymBool (pc : PathCond) : SymBool → SymEvalRes Bool
  | .const b => .val b
  | .var vid =>
    match pc.boolEq.find? (fun p => decide (p.1 = vid)) with
    | some (_, b) => .val b
    | none => .needSplit (.boolVar vid)
  | .eq a b => evalSymNatEq pc a b
  | .ne a b =>
    match evalSymNatEq pc a b with
    | .val b => .val (!b)
    | .needSplit sp => .needSplit sp
    | .unknown => .unknown
  | .not x =>
    match evalSymBool pc x with
    | .val b => .val (!b)
    | .needSplit sp => .needSplit sp
    | .unknown => .unknown

theorem evalSymBool_sound {rootLC : Nat} {s₀ : MirState} {pc : PathCond}
    (hmatch : pc.Matches rootLC s₀) :
    ∀ (b : SymBool) {res : Bool},
      evalSymBool pc b = .val res →
      b.denote s₀ = res
  | .const _, _, h => by injection h with hr
  | .var vid, _, h => by
    dsimp [evalSymBool] at h
    cases hfind : pc.boolEq.find? (fun p => decide (p.1 = vid)) with
    | none => rw [hfind] at h; cases h
    | some p =>
      rcases list_find_some_mem hfind with ⟨hmem, hdec⟩
      rw [hfind] at h
      rcases p with ⟨v', b'⟩
      injection h with hr
      subst hr
      have hv : v' = vid := of_decide_eq_true hdec
      subst hv
      exact hmatch.2.2.1 (v', b') hmem
  | .eq a b, _, h => evalSymNatEq_sound hmatch a b h
  | .ne a b, _, h => by
    dsimp [evalSymBool] at h
    cases heq : evalSymNatEq pc a b with
    | val r =>
      rw [heq] at h
      injection h with hr
      subst hr
      dsimp [SymBool.denote, bne]
      rw [evalSymNatEq_sound hmatch a b heq]
    | needSplit _ => rw [heq] at h; cases h
    | unknown => rw [heq] at h; cases h
  | .not x, _, h => by
    dsimp [evalSymBool] at h
    cases hx : evalSymBool pc x with
    | val r =>
      rw [hx] at h
      injection h with hr
      subst hr
      dsimp [SymBool.denote]
      rw [evalSymBool_sound hmatch x hx]
    | needSplit _ => rw [hx] at h; cases h
    | unknown => rw [hx] at h; cases h

/-!
### Symbolic Call-Stack Frames (`SymStackFrame`) and Symbolic State (`SymState`)
-/

/-- Symbolic saved caller activation frame on a `.call1` transition. -/
structure SymStackFrame where
  callerBody      : MirBody
  callerLocals    : Nat → Option SymVal
  callerLocalGens : Nat → Nat
  retDst          : Place
  retBlock        : Nat
  callerFrameId   : Nat

/-- Update a symbolic local slot at index `idx`. -/
def updateSymLocal (locals : Nat → Option SymVal) (idx : Nat)
    (v : Option SymVal) : Nat → Option SymVal :=
  fun i => if i == idx then v else locals i

/-- Denote a symbolic local map into a concrete `Nat → Option MirVal`.
In the root frame (`isRootFrame = true`), caller-owned referents at indices
`i ≥ rootLC` are preserved directly from `s₀.locals i`. -/
def denoteLocals (s₀ : MirState) (isRootFrame : Bool) (rootLC : Nat)
    (symLocals : Nat → Option SymVal) (i : Nat) : Option MirVal :=
  if isRootFrame && decide (rootLC ≤ i) then
    s₀.locals i
  else
    (symLocals i).map (SymVal.denote s₀)

/-- Denote a symbolic generation map into a concrete `Nat → Nat`.
In the root frame (`isRootFrame = true`), caller-owned referents at indices
`i ≥ rootLC` preserve generation `0` from `s₀`. -/
def denoteLocalGens (isRootFrame : Bool) (rootLC : Nat)
    (symGens : Nat → Nat) (i : Nat) : Nat :=
  if isRootFrame && decide (rootLC ≤ i) then
    0
  else
    symGens i

theorem denoteLocals_lt (s₀ : MirState) (isRootFrame : Bool) (rootLC : Nat)
    (symLocals : Nat → Option SymVal) {i : Nat}
    (hi : ¬ (isRootFrame = true ∧ rootLC ≤ i)) :
    denoteLocals s₀ isRootFrame rootLC symLocals i =
      (symLocals i).map (SymVal.denote s₀) := by
  unfold denoteLocals
  cases h : isRootFrame && decide (rootLC ≤ i) with
  | false => rfl
  | true =>
    rcases Bool.and_eq_true_iff.mp h with ⟨hr, hle⟩
    exact False.elim (hi ⟨hr, of_decide_eq_true hle⟩)

theorem denoteLocals_ge_root (s₀ : MirState) (rootLC : Nat)
    (symLocals : Nat → Option SymVal) {i : Nat} (hi : rootLC ≤ i) :
    denoteLocals s₀ true rootLC symLocals i = s₀.locals i := by
  unfold denoteLocals
  rw [Bool.true_and, decide_eq_true hi]
  rfl

theorem denoteLocals_update_lt (s₀ : MirState) (isRootFrame : Bool)
    (rootLC : Nat) (symLocals : Nat → Option SymVal) {idx : Nat}
    (v : Option SymVal)
    (hidx : ¬ (isRootFrame = true ∧ rootLC ≤ idx)) :
    denoteLocals s₀ isRootFrame rootLC (updateSymLocal symLocals idx v) =
      updateLocal (denoteLocals s₀ isRootFrame rootLC symLocals) idx
        (v.map (SymVal.denote s₀)) := by
  funext i
  unfold updateLocal updateSymLocal
  cases heq : (i == idx) with
  | true =>
    have hi : i = idx := eq_of_beq heq
    subst hi
    rw [denoteLocals_lt s₀ isRootFrame rootLC _ hidx]
    dsimp
    rw [beq_self_eq_true i]
    rfl
  | false =>
    unfold denoteLocals
    cases isRootFrame && decide (rootLC ≤ i) with
    | true => rfl
    | false =>
      dsimp
      rw [heq]
      rfl

theorem denoteLocalGens_lt (isRootFrame : Bool) (rootLC : Nat)
    (symGens : Nat → Nat) {i : Nat}
    (hi : ¬ (isRootFrame = true ∧ rootLC ≤ i)) :
    denoteLocalGens isRootFrame rootLC symGens i = symGens i := by
  unfold denoteLocalGens
  cases h : isRootFrame && decide (rootLC ≤ i) with
  | false => rfl
  | true =>
    rcases Bool.and_eq_true_iff.mp h with ⟨hr, hle⟩
    exact False.elim (hi ⟨hr, of_decide_eq_true hle⟩)

theorem denoteLocalGens_ge_root (rootLC : Nat) (symGens : Nat → Nat)
    {i : Nat} (hi : rootLC ≤ i) :
    denoteLocalGens true rootLC symGens i = 0 := by
  unfold denoteLocalGens
  rw [Bool.true_and, decide_eq_true hi]
  rfl

theorem denoteLocalGens_update_lt (isRootFrame : Bool) (rootLC : Nat)
    (symGens : Nat → Nat) {idx : Nat} (newGen : Nat)
    (hidx : ¬ (isRootFrame = true ∧ rootLC ≤ idx)) :
    denoteLocalGens isRootFrame rootLC
      (fun i => if i == idx then newGen else symGens i) =
    (fun i =>
      if i == idx then newGen
      else denoteLocalGens isRootFrame rootLC symGens i) := by
  funext i
  cases heq : (i == idx) with
  | true =>
    have hi : i = idx := eq_of_beq heq
    subst hi
    rw [denoteLocalGens_lt isRootFrame rootLC _ hidx]
    rw [beq_self_eq_true i]
    rfl
  | false =>
    unfold denoteLocalGens
    cases isRootFrame && decide (rootLC ≤ i) with
    | true => rfl
    | false =>
      dsimp
      rw [heq]
      rfl

/-- Denote a `SymStackFrame` in initial state `s₀`. -/
def SymStackFrame.toStackFrame (rootLC : Nat) (s₀ : MirState)
    (f : SymStackFrame) : StackFrame where
  callerBody      := f.callerBody
  callerLocals    := denoteLocals s₀ (f.callerFrameId == 0) rootLC f.callerLocals
  callerLocalGens := denoteLocalGens (f.callerFrameId == 0) rootLC f.callerLocalGens
  retDst          := f.retDst
  retBlock        := f.retBlock
  callerFrameId   := f.callerFrameId

/-- Symbolic machine state paired with a path condition `pc : PathCond`. -/
structure SymState where
  block       : Nat := 0
  stmtIdx     : Nat := 0
  locals      : Nat → Option SymVal := fun _ => none
  curBody     : Option MirBody := none
  stack       : List SymStackFrame := []
  frameId     : Nat := 0
  nextFrameId : Nat := 1
  localGens   : Nat → Nat := fun _ => 0
  pc          : PathCond := {}

/-- Project a `SymState` to its concrete `MirState` under initial state `s₀`.
Notice that `toMirState` does not depend on `st.pc`, so updating `st.pc` at a
branch split leaves `st.toMirState rootLC s₀` definitionally unchanged (`rfl`). -/
def SymState.toMirState (rootLC : Nat) (s₀ : MirState)
    (st : SymState) : MirState where
  locals      := denoteLocals s₀ (st.frameId == 0) rootLC st.locals
  localGens   := denoteLocalGens (st.frameId == 0) rootLC st.localGens
  block       := st.block
  stmtIdx     := st.stmtIdx
  tySizes     := s₀.tySizes
  curBody     := st.curBody
  stack       := st.stack.map (SymStackFrame.toStackFrame rootLC s₀)
  frameId     := st.frameId
  nextFrameId := st.nextFrameId
  adtPad      := s₀.adtPad
  ubChecks    := s₀.ubChecks

/-- Active `MirBody` of a `SymState`. -/
def SymState.activeBody (rootBody : MirBody) (st : SymState) : MirBody :=
  st.curBody.getD rootBody

/-!
## Section 4: Symbolic Operations and Commutation Soundness Lemmas
-/

/-- Express `resolveRef` uniformly as `raw.bind (peelFields fieldDepth)`. -/
theorem resolveRef_eq_bind_peelFields (s : MirState)
    (targetFrameId gen : Nat) (loc : LocalId) (fieldDepth : Nat) :
    resolveRef s targetFrameId gen loc fieldDepth =
      (if targetFrameId == s.frameId then
         if s.localGens loc.index == gen then
           s.locals loc.index
         else
           none
       else
         match s.stack.find? (fun f => f.callerFrameId == targetFrameId) with
         | some frame =>
           if frame.callerLocalGens loc.index == gen then
             frame.callerLocals loc.index
           else
             none
         | none => none).bind (peelFields fieldDepth) := by
  unfold resolveRef
  cases fieldDepth with
  | zero =>
    cases
      (if targetFrameId == s.frameId then
         if s.localGens loc.index == gen then s.locals loc.index else none
       else
         match s.stack.find? (fun f => f.callerFrameId == targetFrameId) with
         | some frame =>
           if frame.callerLocalGens loc.index == gen then
             frame.callerLocals loc.index
           else none
         | none => none) <;> rfl
  | succ d => rfl

theorem find_map_toStackFrame (rootLC : Nat) (s₀ : MirState)
    (targetFrameId : Nat) :
    ∀ (stack : List SymStackFrame),
      (stack.map (SymStackFrame.toStackFrame rootLC s₀)).find?
          (fun f => f.callerFrameId == targetFrameId) =
        (stack.find? (fun f => f.callerFrameId == targetFrameId)).map
          (SymStackFrame.toStackFrame rootLC s₀)
  | [] => rfl
  | f :: rest => by
    dsimp [List.map, List.find?, SymStackFrame.toStackFrame]
    cases (f.callerFrameId == targetFrameId) with
    | true => rfl
    | false => exact find_map_toStackFrame rootLC s₀ targetFrameId rest

/-- Resolve a frame-allocated symbolic reference `.ref targetFrameId gen loc fieldDepth`. -/
def symResolveFrameRef (rootLC : Nat) (st : SymState)
    (targetFrameId gen : Nat) (loc : LocalId)
    (fieldDepth : Nat := 0) : Option SymVal :=
  if (targetFrameId == 0) && decide (rootLC ≤ loc.index) then
    none
  else
    let raw :=
      if targetFrameId == st.frameId then
        if st.localGens loc.index == gen then
          st.locals loc.index
        else
          none
      else
        match st.stack.find? (fun f => f.callerFrameId == targetFrameId) with
        | some frame =>
          if frame.callerLocalGens loc.index == gen then
            frame.callerLocals loc.index
          else
            none
        | none => none
    match fieldDepth with
    | 0 => raw
    | d + 1 => raw.bind (symPeelFields (d + 1))

theorem option_bind_map_peelFields (s₀ : MirState) (raw : Option SymVal)
    (fieldDepth : Nat) :
    (match fieldDepth with
     | 0 => raw
     | d + 1 => raw.bind (symPeelFields (d + 1))).map (SymVal.denote s₀) =
    match fieldDepth with
    | 0 => raw.map (SymVal.denote s₀)
    | d + 1 => (raw.map (SymVal.denote s₀)).bind (peelFields (d + 1)) := by
  cases fieldDepth with
  | zero => rfl
  | succ d =>
    cases raw with
    | none => rfl
    | some v => exact symPeelFields_denote s₀ (d + 1) v

theorem symResolveFrameRef_sound (rootLC : Nat) (s₀ : MirState)
    (st : SymState) (targetFrameId gen : Nat) (loc : LocalId)
    (fieldDepth : Nat) {ptVal : SymVal}
    (hres : symResolveFrameRef rootLC st targetFrameId gen loc fieldDepth =
      some ptVal) :
    resolveRef (st.toMirState rootLC s₀) targetFrameId gen loc fieldDepth =
      some (ptVal.denote s₀) := by
  unfold symResolveFrameRef at hres
  cases hguard : (targetFrameId == 0) && decide (rootLC ≤ loc.index) with
  | true => rw [hguard] at hres; cases hres
  | false =>
    rw [hguard] at hres
    dsimp at hres
    have hnot : ¬ ((targetFrameId == 0) = true ∧ rootLC ≤ loc.index) := by
      intro ⟨h1, h2⟩
      have h2' : decide (rootLC ≤ loc.index) = true := decide_eq_true h2
      rw [h1, h2'] at hguard
      cases hguard
    have hraw_eq :
        (if targetFrameId == (st.toMirState rootLC s₀).frameId then
           if (st.toMirState rootLC s₀).localGens loc.index == gen then
             (st.toMirState rootLC s₀).locals loc.index
           else
             none
         else
           match (st.toMirState rootLC s₀).stack.find?
               (fun f => f.callerFrameId == targetFrameId) with
           | some frame =>
             if frame.callerLocalGens loc.index == gen then
               frame.callerLocals loc.index
             else
               none
           | none => none) =
        (if targetFrameId == st.frameId then
           if st.localGens loc.index == gen then
             st.locals loc.index
           else
             none
         else
           match st.stack.find? (fun f => f.callerFrameId == targetFrameId) with
           | some frame =>
             if frame.callerLocalGens loc.index == gen then
               frame.callerLocals loc.index
             else
               none
           | none => none).map (SymVal.denote s₀) := by
      have hfid_to : (st.toMirState rootLC s₀).frameId = st.frameId := rfl
      have hgens_to : (st.toMirState rootLC s₀).localGens =
          denoteLocalGens (st.frameId == 0) rootLC st.localGens := rfl
      have hlocs_to : (st.toMirState rootLC s₀).locals =
          denoteLocals s₀ (st.frameId == 0) rootLC st.locals := rfl
      have hstk_to : (st.toMirState rootLC s₀).stack =
          st.stack.map (SymStackFrame.toStackFrame rootLC s₀) := rfl
      rw [hfid_to, hgens_to, hlocs_to, hstk_to]
      cases hfid : (targetFrameId == st.frameId) with
      | true =>
        have hfidEq : st.frameId = targetFrameId := (eq_of_beq hfid).symm
        rw [hfidEq]
        rw [denoteLocalGens_lt (targetFrameId == 0) rootLC st.localGens hnot]
        rw [denoteLocals_lt s₀ (targetFrameId == 0) rootLC st.locals hnot]
        cases (st.localGens loc.index == gen) <;> rfl
      | false =>
        rw [find_map_toStackFrame rootLC s₀ targetFrameId st.stack]
        cases hfind : st.stack.find? (fun f => f.callerFrameId == targetFrameId) with
        | none => rfl
        | some frame =>
          dsimp [Option.map]
          have hfgens : (frame.toStackFrame rootLC s₀).callerLocalGens =
              denoteLocalGens (frame.callerFrameId == 0) rootLC frame.callerLocalGens := rfl
          have hflocs : (frame.toStackFrame rootLC s₀).callerLocals =
              denoteLocals s₀ (frame.callerFrameId == 0) rootLC frame.callerLocals := rfl
          rw [hfgens, hflocs]
          rcases list_find_some_mem hfind with ⟨_, hcfid⟩
          have hcfidEq : frame.callerFrameId = targetFrameId := eq_of_beq hcfid
          rw [hcfidEq]
          rw [denoteLocalGens_lt (targetFrameId == 0) rootLC frame.callerLocalGens hnot]
          rw [denoteLocals_lt s₀ (targetFrameId == 0) rootLC frame.callerLocals hnot]
          cases (frame.callerLocalGens loc.index == gen) <;> rfl
    unfold resolveRef
    rw [hraw_eq]
    rw [← option_bind_map_peelFields s₀ _ fieldDepth]
    rw [hres]
    rfl

/-- Resolve a caller-owned symbolic reference `.callerRef vid extraDepth`. -/
def symResolveCallerRef (st : SymState) (vid : SymVarId)
    (extraDepth : Nat) : Option SymVal :=
  if (st.frameId == 0) || st.stack.any (fun f => f.callerFrameId == 0) then
    match st.pc.callerRefs.find? (fun p => decide (p.1 = vid)) with
    | some (_, ptVal) => symPeelFields extraDepth ptVal
    | none => none
  else
    none

theorem find_some_of_any {α : Type} {p : α → Bool} {xs : List α}
    (h : xs.any p = true) : ∃ x, xs.find? p = some x ∧ p x = true := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
    dsimp [List.any, List.find?] at h ⊢
    cases hpx : p x with
    | true => exact ⟨x, rfl, hpx⟩
    | false =>
      rw [hpx, Bool.false_or] at h
      exact ih h

theorem symResolveCallerRef_sound {rootLC : Nat} {s₀ : MirState}
    {st : SymState} (hmatch : st.pc.Matches rootLC s₀)
    (vid : SymVarId) (extraDepth : Nat) {ptVal : SymVal}
    (hres : symResolveCallerRef st vid extraDepth = some ptVal) :
    resolveRef (st.toMirState rootLC s₀) 0 0
      (evalInputRef s₀ vid).1 ((evalInputRef s₀ vid).2 + extraDepth) =
      some (ptVal.denote s₀) ∧
    rootLC ≤ (evalInputRef s₀ vid).1.index := by
  unfold symResolveCallerRef at hres
  cases hroot : (st.frameId == 0) || st.stack.any (fun f => f.callerFrameId == 0) with
  | false => rw [hroot] at hres; cases hres
  | true =>
    rw [hroot] at hres
    dsimp at hres
    cases hfind : st.pc.callerRefs.find? (fun p => decide (p.1 = vid)) with
    | none => rw [hfind] at hres; cases hres
    | some p =>
      rw [hfind] at hres
      rcases list_find_some_mem hfind with ⟨hmem, hdec⟩
      rcases p with ⟨v', basePt⟩
      have hv : v' = vid := of_decide_eq_true hdec
      subst hv
      rcases hmatch.2.2.2.2.2.2.2.1 (v', basePt) hmem with
        ⟨hle, hfid0, hgen0, hres0⟩
      refine ⟨?_, hle⟩
      have hraw_eq :
          (if 0 == (st.toMirState rootLC s₀).frameId then
             if (st.toMirState rootLC s₀).localGens (evalInputRef s₀ v').1.index == 0 then
               (st.toMirState rootLC s₀).locals (evalInputRef s₀ v').1.index
             else
               none
           else
             match (st.toMirState rootLC s₀).stack.find?
                 (fun f => f.callerFrameId == 0) with
             | some frame =>
               if frame.callerLocalGens (evalInputRef s₀ v').1.index == 0 then
                 frame.callerLocals (evalInputRef s₀ v').1.index
               else
                 none
             | none => none) =
          s₀.locals (evalInputRef s₀ v').1.index := by
        have hfid_to : (st.toMirState rootLC s₀).frameId = st.frameId := rfl
        have hgens_to : (st.toMirState rootLC s₀).localGens =
            denoteLocalGens (st.frameId == 0) rootLC st.localGens := rfl
        have hlocs_to : (st.toMirState rootLC s₀).locals =
            denoteLocals s₀ (st.frameId == 0) rootLC st.locals := rfl
        have hstk_to : (st.toMirState rootLC s₀).stack =
            st.stack.map (SymStackFrame.toStackFrame rootLC s₀) := rfl
        rw [hfid_to, hgens_to, hlocs_to, hstk_to]
        cases hfid : (st.frameId == 0) with
        | true =>
          have hfid0' : (0 == st.frameId) = true := by
            rw [eq_of_beq hfid]; rfl
          rw [hfid0']
          dsimp
          rw [denoteLocalGens_ge_root rootLC st.localGens hle]
          rw [denoteLocals_ge_root s₀ rootLC st.locals hle]
          rfl
        | false =>
          have hfid0' : (0 == st.frameId) = false := by
            cases h0 : (0 == st.frameId) with
            | false => rfl
            | true =>
              rw [(eq_of_beq h0).symm] at hfid
              cases hfid
          rw [hfid0']
          dsimp
          rw [hfid, Bool.false_or] at hroot
          rcases find_some_of_any hroot with ⟨frame, hfFind, hcfid⟩
          rw [find_map_toStackFrame rootLC s₀ 0 st.stack, hfFind]
          dsimp [Option.map]
          have hfgens : (frame.toStackFrame rootLC s₀).callerLocalGens =
              denoteLocalGens (frame.callerFrameId == 0) rootLC frame.callerLocalGens := rfl
          have hflocs : (frame.toStackFrame rootLC s₀).callerLocals =
              denoteLocals s₀ (frame.callerFrameId == 0) rootLC frame.callerLocals := rfl
          rw [hfgens, hflocs, hcfid]
          rw [denoteLocalGens_ge_root rootLC frame.callerLocalGens hle]
          rw [denoteLocals_ge_root s₀ rootLC frame.callerLocals hle]
          rfl
      have hraw0_eq :
          (if 0 == s₀.frameId then
             if s₀.localGens (evalInputRef s₀ v').1.index == 0 then
               s₀.locals (evalInputRef s₀ v').1.index
             else
               none
           else
             match s₀.stack.find? (fun f => f.callerFrameId == 0) with
             | some frame =>
               if frame.callerLocalGens (evalInputRef s₀ v').1.index == 0 then
                 frame.callerLocals (evalInputRef s₀ v').1.index
               else
                 none
             | none => none) =
          s₀.locals (evalInputRef s₀ v').1.index := by
        rw [hfid0, hgen0]
        rfl
      have hbind_add :
          (s₀.locals (evalInputRef s₀ v').1.index).bind
              (peelFields ((evalInputRef s₀ v').2 + extraDepth)) =
            ((s₀.locals (evalInputRef s₀ v').1.index).bind
              (peelFields (evalInputRef s₀ v').2)).bind
              (peelFields extraDepth) := by
        cases s₀.locals (evalInputRef s₀ v').1.index with
        | none => rfl
        | some rv => exact peelFields_add (evalInputRef s₀ v').2 extraDepth rv
      rw [resolveRef_eq_bind_peelFields, hraw_eq, hbind_add]
      rw [resolveRef_eq_bind_peelFields, hraw0_eq] at hres0
      rw [hres0]
      dsimp [Option.bind]
      dsimp at hres
      rw [← symPeelFields_denote s₀ extraDepth basePt, hres]
      rfl

/-!
### Symbolic Place Lenses (`symEvalProj`, `symEvalPlace`, `symAssignPlace`, `symEvalRefPlace`)
-/

/-- Follow a projection list from `v : SymVal` in symbolic state `st`. -/
def symEvalProj (rootLC : Nat) (st : SymState) :
    List PlaceElem → SymVal → Option SymVal
  | [], v => if v.isFullyInit then some v else none
  | .field idx :: rest, .adt _ inner =>
    (symGetFieldVal idx inner).bind (symEvalProj rootLC st rest)
  | .field idx :: rest, .fieldCons h t =>
    (symGetFieldVal idx (.fieldCons h t)).bind (symEvalProj rootLC st rest)
  | .deref :: rest, .ref frameId gen loc fieldDepth =>
    match symResolveFrameRef rootLC st frameId gen loc fieldDepth with
    | some pointee => symEvalProj rootLC st rest pointee
    | none => none
  | .deref :: rest, .callerRef vid extraDepth =>
    match symResolveCallerRef st vid extraDepth with
    | some pointee => symEvalProj rootLC st rest pointee
    | none => none
  | _, _ => none

theorem symEvalProj_sound {rootLC : Nat} {s₀ : MirState} {st : SymState}
    (hmatch : st.pc.Matches rootLC s₀) :
    ∀ (proj : List PlaceElem) (v : SymVal) {out : SymVal},
      symEvalProj rootLC st proj v = some out →
      evalProj (st.toMirState rootLC s₀) proj (v.denote s₀) =
        some (out.denote s₀)
  | [], v, out, h => by
    dsimp [symEvalProj] at h
    dsimp [evalProj]
    rw [SymVal.isFullyInit_denote s₀ v]
    cases hv : v.isFullyInit with
    | false => rw [hv] at h; cases h
    | true =>
      rw [hv] at h
      injection h with hout
      subst hout
      rfl
  | .field idx :: rest, .adt id inner, out, h => by
    dsimp [symEvalProj] at h
    dsimp [SymVal.denote, evalProj]
    rw [← symGetFieldVal_denote s₀ idx inner]
    cases hget : symGetFieldVal idx inner with
    | none => rw [hget] at h; cases h
    | some fval =>
      rw [hget] at h
      dsimp [Option.bind, Option.map] at h ⊢
      exact symEvalProj_sound hmatch rest fval h
  | .field idx :: rest, .fieldCons h1 t1, out, h => by
    dsimp [symEvalProj] at h
    dsimp [SymVal.denote, evalProj]
    have hget_eq := symGetFieldVal_denote s₀ idx (.fieldCons h1 t1)
    dsimp [SymVal.denote] at hget_eq
    rw [← hget_eq]
    cases hget : symGetFieldVal idx (.fieldCons h1 t1) with
    | none => rw [hget] at h; cases h
    | some fval =>
      rw [hget] at h
      dsimp [Option.bind, Option.map] at h ⊢
      exact symEvalProj_sound hmatch rest fval h
  | .deref :: rest, .ref frameId gen loc fieldDepth, out, h => by
    dsimp [symEvalProj] at h
    dsimp [SymVal.denote, evalProj]
    cases hres : symResolveFrameRef rootLC st frameId gen loc fieldDepth with
    | none => rw [hres] at h; cases h
    | some pt =>
      rw [hres] at h
      rw [symResolveFrameRef_sound rootLC s₀ st frameId gen loc fieldDepth hres]
      exact symEvalProj_sound hmatch rest pt h
  | .deref :: rest, .callerRef vid extraDepth, out, h => by
    dsimp [symEvalProj] at h
    dsimp [SymVal.denote, evalProj]
    cases hres : symResolveCallerRef st vid extraDepth with
    | none => rw [hres] at h; cases h
    | some pt =>
      rw [hres] at h
      rw [(symResolveCallerRef_sound hmatch vid extraDepth hres).1]
      exact symEvalProj_sound hmatch rest pt h
  | .field _ :: _, .uninit, _, h => by cases h
  | .field _ :: _, .usize _, _, h => by cases h
  | .field _ :: _, .bool _, _, h => by cases h
  | .field _ :: _, .unit, _, h => by cases h
  | .field _ :: _, .bytes _ _, _, h => by cases h
  | .field _ :: _, .ref _ _ _ _, _, h => by cases h
  | .field _ :: _, .callerRef _ _, _, h => by cases h
  | .deref :: _, .uninit, _, h => by cases h
  | .deref :: _, .usize _, _, h => by cases h
  | .deref :: _, .bool _, _, h => by cases h
  | .deref :: _, .unit, _, h => by cases h
  | .deref :: _, .adt _ _, _, h => by cases h
  | .deref :: _, .fieldCons _ _, _, h => by cases h
  | .deref :: _, .bytes _ _, _, h => by cases h
  | .index _ :: _, _, _, h => by cases h
  | .constantIndex _ _ _ :: _, _, _, h => by cases h
  | .subslice _ _ _ :: _, _, _, h => by cases h
  | .downcast _ :: _, _, _, h => by cases h
  | .opaqueCast _ :: _, _, _, h => by cases h
  | .unwrapUnsafeBinder _ :: _, _, _, h => by cases h

/-- Read the symbolic value at `p` within a frame of `localCount` locals. -/
def symEvalPlace (rootLC localCount : Nat) (st : SymState)
    (p : Place) : Option SymVal :=
  if (st.frameId == 0) && decide (rootLC ≤ p.loc.index) then
    none
  else if p.loc.index < localCount then
    match st.locals p.loc.index with
    | some v => symEvalProj rootLC st p.projection v
    | none => none
  else
    none

theorem symEvalPlace_sound {rootLC localCount : Nat} {s₀ : MirState}
    {st : SymState} (hmatch : st.pc.Matches rootLC s₀)
    (p : Place) {out : SymVal}
    (h : symEvalPlace rootLC localCount st p = some out) :
    evalPlace localCount (st.toMirState rootLC s₀) p =
      some (out.denote s₀) := by
  unfold symEvalPlace at h
  cases hguard : (st.frameId == 0) && decide (rootLC ≤ p.loc.index) with
  | true => rw [hguard] at h; cases h
  | false =>
    rw [hguard] at h
    dsimp at h
    have hnot : ¬ ((st.frameId == 0) = true ∧ rootLC ≤ p.loc.index) := by
      intro ⟨h1, h2⟩
      rw [h1, decide_eq_true h2] at hguard
      cases hguard
    unfold evalPlace
    dsimp [SymState.toMirState]
    cases hlt : decide (p.loc.index < localCount) with
    | false =>
      rw [if_neg (of_decide_eq_false hlt)] at h
      cases h
    | true =>
      have hlt' : p.loc.index < localCount := of_decide_eq_true hlt
      rw [if_pos hlt'] at h ⊢
      rw [denoteLocals_lt s₀ (st.frameId == 0) rootLC st.locals hnot]
      cases hloc : st.locals p.loc.index with
      | none => rw [hloc] at h; cases h
      | some v =>
        rw [hloc] at h
        dsimp [Option.map]
        exact symEvalProj_sound hmatch p.projection v h

/-- Replace the sub-value at `proj` inside a symbolic local's value with
`newVal`. -/
def symUpdateProj (newVal : SymVal) :
    List PlaceElem → Option SymVal → Option SymVal
  | [], _ => some newVal
  | .field idx :: rest, some (.adt id inner) =>
    (symGetFieldVal idx inner).bind fun curField =>
      (symUpdateProj newVal rest (some curField)).bind fun updatedField =>
        (symSetFieldVal updatedField idx inner).map (.adt id)
  | .field idx :: rest, some (.fieldCons h t) =>
    (symGetFieldVal idx (.fieldCons h t)).bind fun curField =>
      (symUpdateProj newVal rest (some curField)).bind fun updatedField =>
        symSetFieldVal updatedField idx (.fieldCons h t)
  | _, _ => none

theorem symUpdateProj_denote (s₀ : MirState) (newVal : SymVal) :
    ∀ (proj : List PlaceElem) (ov : Option SymVal),
      (symUpdateProj newVal proj ov).map (SymVal.denote s₀) =
        updateProj (newVal.denote s₀) proj (ov.map (SymVal.denote s₀))
  | [], _ => rfl
  | .field idx :: rest, some (.adt id inner) => by
    dsimp [symUpdateProj, updateProj, Option.map, SymVal.denote]
    rw [← symGetFieldVal_denote s₀ idx inner]
    cases hget : symGetFieldVal idx inner with
    | none => rfl
    | some curField =>
      dsimp [Option.bind, Option.map]
      have ih := symUpdateProj_denote s₀ newVal rest (some curField)
      dsimp [Option.map] at ih
      rw [← ih]
      cases hupd : symUpdateProj newVal rest (some curField) with
      | none => rfl
      | some updatedField =>
        dsimp [Option.bind, Option.map]
        rw [← symSetFieldVal_denote s₀ updatedField idx inner]
        cases symSetFieldVal updatedField idx inner <;> rfl
  | .field idx :: rest, some (.fieldCons h t) => by
    dsimp [symUpdateProj, updateProj, Option.map, SymVal.denote]
    have hget_eq := symGetFieldVal_denote s₀ idx (.fieldCons h t)
    dsimp [SymVal.denote] at hget_eq
    rw [← hget_eq]
    cases hget : symGetFieldVal idx (.fieldCons h t) with
    | none => rfl
    | some curField =>
      dsimp [Option.bind, Option.map]
      have ih := symUpdateProj_denote s₀ newVal rest (some curField)
      dsimp [Option.map] at ih
      rw [← ih]
      cases hupd : symUpdateProj newVal rest (some curField) with
      | none => rfl
      | some updatedField =>
        dsimp [Option.bind, Option.map]
        have hset_eq :=
          symSetFieldVal_denote s₀ updatedField idx (.fieldCons h t)
        dsimp [SymVal.denote] at hset_eq
        exact hset_eq
  | .field _ :: _, none => rfl
  | .field _ :: _, some .uninit => rfl
  | .field _ :: _, some (.usize _) => rfl
  | .field _ :: _, some (.bool _) => rfl
  | .field _ :: _, some .unit => rfl
  | .field _ :: _, some (.bytes _ _) => rfl
  | .field _ :: _, some (.ref _ _ _ _) => rfl
  | .field _ :: _, some (.callerRef _ _) => rfl
  | .deref :: _, _ => rfl
  | .index _ :: _, _ => rfl
  | .constantIndex _ _ _ :: _, _ => rfl
  | .subslice _ _ _ :: _, _ => rfl
  | .downcast _ :: _, _ => rfl
  | .opaqueCast _ :: _, _ => rfl
  | .unwrapUnsafeBinder _ :: _, _ => rfl

/-- Write `val` to `dst` within a frame of `localCount` symbolic locals. -/
def symAssignPlace (isRootFrame : Bool) (rootLC localCount : Nat)
    (locals : Nat → Option SymVal) (dst : Place) (val : SymVal) :
    Option (Nat → Option SymVal) :=
  if isRootFrame && decide (rootLC ≤ dst.loc.index) then
    none
  else if dst.loc.index < localCount then
    (symUpdateProj val dst.projection (locals dst.loc.index)).map fun v' =>
      updateSymLocal locals dst.loc.index (some v')
  else
    none

theorem symAssignPlace_sound (s₀ : MirState) (isRootFrame : Bool)
    (rootLC localCount : Nat) (locals : Nat → Option SymVal)
    (dst : Place) (val : SymVal) {locals' : Nat → Option SymVal}
    (h : symAssignPlace isRootFrame rootLC localCount locals dst val =
      some locals') :
    assignPlace localCount (denoteLocals s₀ isRootFrame rootLC locals) dst
      (val.denote s₀) =
      some (denoteLocals s₀ isRootFrame rootLC locals') := by
  unfold symAssignPlace at h
  cases hguard : isRootFrame && decide (rootLC ≤ dst.loc.index) with
  | true => rw [hguard] at h; cases h
  | false =>
    rw [hguard] at h
    dsimp at h
    have hnot : ¬ (isRootFrame = true ∧ rootLC ≤ dst.loc.index) := by
      intro ⟨h1, h2⟩
      rw [h1, decide_eq_true h2] at hguard
      cases hguard
    unfold assignPlace
    cases hlt : decide (dst.loc.index < localCount) with
    | false =>
      rw [if_neg (of_decide_eq_false hlt)] at h
      cases h
    | true =>
      have hlt' : dst.loc.index < localCount := of_decide_eq_true hlt
      rw [if_pos hlt'] at h ⊢
      rw [denoteLocals_lt s₀ isRootFrame rootLC locals hnot]
      rw [← symUpdateProj_denote s₀ val dst.projection (locals dst.loc.index)]
      cases hupd : symUpdateProj val dst.projection (locals dst.loc.index) with
      | none => rw [hupd] at h; cases h
      | some v' =>
        rw [hupd] at h
        injection h with hloc'
        subst hloc'
        dsimp [Option.map]
        rw [denoteLocals_update_lt s₀ isRootFrame rootLC locals (some v') hnot]
        rfl

/-- Deinitialize `p` after `Operand.move p` in symbolic `locals`. -/
def symDeinitPlace (isRootFrame : Bool) (rootLC localCount : Nat)
    (locals : Nat → Option SymVal) (p : Place) :
    Option (Nat → Option SymVal) :=
  if isRootFrame && decide (rootLC ≤ p.loc.index) then
    none
  else if p.loc.index < localCount then
    match p.projection with
    | [] => some (updateSymLocal locals p.loc.index none)
    | proj =>
      (symUpdateProj .uninit proj (locals p.loc.index)).map fun v' =>
        updateSymLocal locals p.loc.index (some v')
  else
    none

theorem symDeinitPlace_sound (s₀ : MirState) (isRootFrame : Bool)
    (rootLC localCount : Nat) (locals : Nat → Option SymVal)
    (p : Place) {locals' : Nat → Option SymVal}
    (h : symDeinitPlace isRootFrame rootLC localCount locals p =
      some locals') :
    deinitPlace localCount (denoteLocals s₀ isRootFrame rootLC locals) p =
      some (denoteLocals s₀ isRootFrame rootLC locals') := by
  unfold symDeinitPlace at h
  cases hguard : isRootFrame && decide (rootLC ≤ p.loc.index) with
  | true => rw [hguard] at h; cases h
  | false =>
    rw [hguard] at h
    dsimp at h
    have hnot : ¬ (isRootFrame = true ∧ rootLC ≤ p.loc.index) := by
      intro ⟨h1, h2⟩
      rw [h1, decide_eq_true h2] at hguard
      cases hguard
    unfold deinitPlace
    cases hlt : decide (p.loc.index < localCount) with
    | false =>
      rw [if_neg (of_decide_eq_false hlt)] at h
      cases h
    | true =>
      have hlt' : p.loc.index < localCount := of_decide_eq_true hlt
      rw [if_pos hlt'] at h ⊢
      cases hproj : p.projection with
      | nil =>
        rw [hproj] at h
        injection h with hloc'
        subst hloc'
        dsimp
        rw [denoteLocals_update_lt s₀ isRootFrame rootLC locals none hnot]
        rfl
      | cons e es =>
        rw [hproj] at h
        dsimp at h ⊢
        rw [denoteLocals_lt s₀ isRootFrame rootLC locals hnot]
        have hupd_eq :=
          symUpdateProj_denote s₀ .uninit (e :: es) (locals p.loc.index)
        dsimp [SymVal.denote] at hupd_eq
        rw [← hupd_eq]
        cases hupd : symUpdateProj .uninit (e :: es) (locals p.loc.index) with
        | none => rw [hupd] at h; cases h
        | some v' =>
          rw [hupd] at h
          injection h with hloc'
          subst hloc'
          dsimp [Option.map]
          rw [denoteLocals_update_lt s₀ isRootFrame rootLC locals (some v') hnot]
          rfl

/-- Symbolic target of an in-progress borrow evaluation `&p`: either a
frame-allocated local `(frameId, gen, loc, fieldDepth)` or a caller-owned
reference `(vid, extraDepth)`. -/
inductive SymRefTarget where
  | frame (frameId gen : Nat) (loc : LocalId) (fieldDepth : Nat)
  | caller (vid : SymVarId) (extraDepth : Nat)

def SymRefTarget.toSymVal : SymRefTarget → SymVal
  | .frame frameId gen loc fieldDepth => .ref frameId gen loc fieldDepth
  | .caller vid extraDepth => .callerRef vid extraDepth

def SymRefTarget.addDepth (tgt : SymRefTarget) (d : Nat) : SymRefTarget :=
  match tgt with
  | .frame frameId gen loc fieldDepth =>
    .frame frameId gen loc (fieldDepth + d)
  | .caller vid extraDepth =>
    .caller vid (extraDepth + d)

theorem SymRefTarget.denote_toSymVal (s₀ : MirState) :
    ∀ (tgt : SymRefTarget),
      tgt.toSymVal.denote s₀ =
        match tgt with
        | .frame frameId gen loc fieldDepth => .ref frameId gen loc fieldDepth
        | .caller vid extraDepth =>
          let r := evalInputRef s₀ vid
          .ref 0 0 r.1 (r.2 + extraDepth)
  | .frame _ _ _ _ => rfl
  | .caller _ _ => rfl

/-- Follow `.field 0` and `.deref` projections to evaluate a shared borrow `&p`
symbolically. -/
def symEvalRefProj (rootLC : Nat) (st : SymState) (tgt : SymRefTarget) :
    List PlaceElem → SymVal → Option SymVal
  | [], v =>
    if v.isFullyInit then some tgt.toSymVal else none
  | .field 0 :: rest, .adt _ inner =>
    symEvalRefProj rootLC st (tgt.addDepth 1) rest (symFirstFieldVal inner)
  | .deref :: rest, .ref frameId' gen' loc' fieldDepth' =>
    match symResolveFrameRef rootLC st frameId' gen' loc' fieldDepth' with
    | some pointee =>
      symEvalRefProj rootLC st (.frame frameId' gen' loc' fieldDepth')
        rest pointee
    | none => none
  | .deref :: rest, .callerRef vid extraDepth =>
    match symResolveCallerRef st vid extraDepth with
    | some pointee =>
      symEvalRefProj rootLC st (.caller vid extraDepth) rest pointee
    | none => none
  | _, _ => none

theorem symEvalRefProj_sound {rootLC : Nat} {s₀ : MirState} {st : SymState}
    (hmatch : st.pc.Matches rootLC s₀) :
    ∀ (proj : List PlaceElem) (tgt : SymRefTarget) (v : SymVal) {out : SymVal},
      symEvalRefProj rootLC st tgt proj v = some out →
      (match tgt with
       | .frame frameId gen loc fieldDepth =>
         evalRefProj (st.toMirState rootLC s₀) frameId gen loc fieldDepth
           proj (v.denote s₀)
       | .caller vid extraDepth =>
         let r := evalInputRef s₀ vid
         evalRefProj (st.toMirState rootLC s₀) 0 0 r.1 (r.2 + extraDepth)
           proj (v.denote s₀)) =
      some (out.denote s₀)
  | [], tgt, v, out, h => by
    dsimp [symEvalRefProj] at h
    cases hv : v.isFullyInit with
    | false => rw [hv] at h; cases h
    | true =>
      rw [hv] at h
      injection h with hout
      subst hout
      cases tgt <;>
        (dsimp [evalRefProj, SymRefTarget.toSymVal, SymVal.denote]
         rw [SymVal.isFullyInit_denote s₀ v, hv]
         rfl)
  | .field 0 :: rest, tgt, .adt id inner, out, h => by
    change symEvalRefProj rootLC st (tgt.addDepth 1) rest
      (symFirstFieldVal inner) = some out at h
    have ih := symEvalRefProj_sound hmatch rest (tgt.addDepth 1)
      (symFirstFieldVal inner) h
    cases tgt with
    | frame frameId gen loc fieldDepth =>
      change evalRefProj (st.toMirState rootLC s₀) frameId gen loc
        (fieldDepth + 1) rest (firstFieldVal (inner.denote s₀)) =
        some (out.denote s₀)
      rw [← symFirstFieldVal_denote s₀ inner]
      exact ih
    | caller vid extraDepth =>
      change evalRefProj (st.toMirState rootLC s₀) 0 0
        (evalInputRef s₀ vid).1 ((evalInputRef s₀ vid).2 + extraDepth + 1) rest
        (firstFieldVal (inner.denote s₀)) = some (out.denote s₀)
      rw [← symFirstFieldVal_denote s₀ inner]
      dsimp [SymRefTarget.addDepth] at ih
      rw [← Nat.add_assoc] at ih
      exact ih
  | .deref :: rest, tgt, .ref frameId' gen' loc' fieldDepth', out, h => by
    dsimp [symEvalRefProj] at h
    cases hres : symResolveFrameRef rootLC st frameId' gen' loc' fieldDepth' with
    | none => rw [hres] at h; cases h
    | some pt =>
      rw [hres] at h
      have hres_c :=
        symResolveFrameRef_sound rootLC s₀ st frameId' gen' loc' fieldDepth' hres
      have ih :=
        symEvalRefProj_sound hmatch rest
          (.frame frameId' gen' loc' fieldDepth') pt h
      cases tgt <;>
        (dsimp [SymVal.denote, evalRefProj]
         rw [hres_c]
         exact ih)
  | .deref :: rest, tgt, .callerRef vid extraDepth, out, h => by
    dsimp [symEvalRefProj] at h
    cases hres : symResolveCallerRef st vid extraDepth with
    | none => rw [hres] at h; cases h
    | some pt =>
      rw [hres] at h
      have hres_c := (symResolveCallerRef_sound hmatch vid extraDepth hres).1
      have ih :=
        symEvalRefProj_sound hmatch rest (.caller vid extraDepth) pt h
      cases tgt <;>
        (dsimp [SymVal.denote, evalRefProj]
         rw [hres_c]
         exact ih)
  | .field 0 :: _, _, .uninit, _, h => by cases h
  | .field 0 :: _, _, .usize _, _, h => by cases h
  | .field 0 :: _, _, .bool _, _, h => by cases h
  | .field 0 :: _, _, .unit, _, h => by cases h
  | .field 0 :: _, _, .fieldCons _ _, _, h => by cases h
  | .field 0 :: _, _, .bytes _ _, _, h => by cases h
  | .field 0 :: _, _, .ref _ _ _ _, _, h => by cases h
  | .field 0 :: _, _, .callerRef _ _, _, h => by cases h
  | .field (_ + 1) :: _, _, _, _, h => by cases h
  | .deref :: _, _, .uninit, _, h => by cases h
  | .deref :: _, _, .usize _, _, h => by cases h
  | .deref :: _, _, .bool _, _, h => by cases h
  | .deref :: _, _, .unit, _, h => by cases h
  | .deref :: _, _, .adt _ _, _, h => by cases h
  | .deref :: _, _, .fieldCons _ _, _, h => by cases h
  | .deref :: _, _, .bytes _ _, _, h => by cases h
  | .index _ :: _, _, _, _, h => by cases h
  | .constantIndex _ _ _ :: _, _, _, _, h => by cases h
  | .subslice _ _ _ :: _, _, _, _, h => by cases h
  | .downcast _ :: _, _, _, _, h => by cases h
  | .opaqueCast _ :: _, _, _, _, h => by cases h
  | .unwrapUnsafeBinder _ :: _, _, _, _, h => by cases h

/-- Evaluate a shared borrow `&p` (`Rvalue.ref p`) symbolically. -/
def symEvalRefPlace (rootLC localCount : Nat) (st : SymState)
    (p : Place) : Option SymVal :=
  if (st.frameId == 0) && decide (rootLC ≤ p.loc.index) then
    none
  else if p.loc.index < localCount then
    match st.locals p.loc.index with
    | some v =>
      symEvalRefProj rootLC st
        (.frame st.frameId (st.localGens p.loc.index) p.loc 0)
        p.projection v
    | none => none
  else
    none

theorem symEvalRefPlace_sound {rootLC localCount : Nat} {s₀ : MirState}
    {st : SymState} (hmatch : st.pc.Matches rootLC s₀)
    (p : Place) {out : SymVal}
    (h : symEvalRefPlace rootLC localCount st p = some out) :
    evalRefPlace localCount (st.toMirState rootLC s₀) p =
      some (out.denote s₀) := by
  unfold symEvalRefPlace at h
  cases hguard : (st.frameId == 0) && decide (rootLC ≤ p.loc.index) with
  | true => rw [hguard] at h; cases h
  | false =>
    rw [hguard] at h
    dsimp at h
    have hnot : ¬ ((st.frameId == 0) = true ∧ rootLC ≤ p.loc.index) := by
      intro ⟨h1, h2⟩
      rw [h1, decide_eq_true h2] at hguard
      cases hguard
    unfold evalRefPlace
    dsimp [SymState.toMirState]
    cases hlt : decide (p.loc.index < localCount) with
    | false =>
      rw [if_neg (of_decide_eq_false hlt)] at h
      cases h
    | true =>
      have hlt' : p.loc.index < localCount := of_decide_eq_true hlt
      rw [if_pos hlt'] at h ⊢
      rw [denoteLocals_lt s₀ (st.frameId == 0) rootLC st.locals hnot]
      rw [denoteLocalGens_lt (st.frameId == 0) rootLC st.localGens hnot]
      cases hloc : st.locals p.loc.index with
      | none => rw [hloc] at h; cases h
      | some v =>
        rw [hloc] at h
        dsimp [Option.map]
        exact symEvalRefProj_sound hmatch p.projection
          (.frame st.frameId (st.localGens p.loc.index) p.loc 0) v h

/-!
### Symbolic Operands, Binary/Unary Operations (`symEvalOperand`, `symEvalBinOp`, `symEvalUnOp`)
-/

/-- Lift a concrete `MirVal` constant scalar to a `SymVal`. -/
def symOfConstScalar : MirVal → Option SymVal
  | .usize n => some (.usize (.const n))
  | .bool b => some (.bool (.const b))
  | .unit => some .unit
  | .uninit | .adt _ _ | .fieldCons _ _ | .bytes _ _ | .ref _ _ _ _ => none

theorem symOfConstScalar_sound (s₀ : MirState) :
    ∀ (v : MirVal),
      (symOfConstScalar v).map (SymVal.denote s₀) =
        if v.isConstScalar then some v else none
  | .usize _ | .bool _ | .unit => rfl
  | .uninit | .adt _ _ | .fieldCons _ _ | .bytes _ _ | .ref _ _ _ _ => rfl

/-- Evaluate a MIR `Operand` symbolically, requesting `.needSplit .ubChecks`
when `Operand.runtimeChecks .ubChecks` is encountered and `st.pc.ubChecks` is
not yet constrained. -/
def symEvalOperand (rootLC localCount : Nat) (st : SymState)
    (op : Operand) : SymEvalRes (SymVal × (Nat → Option SymVal)) :=
  match op with
  | .copy src =>
    match symEvalPlace rootLC localCount st src with
    | some v => .val (v, st.locals)
    | none => .unknown
  | .move src =>
    match symEvalPlace rootLC localCount st src with
    | some v =>
      match symDeinitPlace (st.frameId == 0) rootLC localCount st.locals src with
      | some locals' => .val (v, locals')
      | none => .unknown
    | none => .unknown
  | .constVal v =>
    match symOfConstScalar v with
    | some sv => .val (sv, st.locals)
    | none => .unknown
  | .runtimeChecks .ubChecks =>
    match st.pc.ubChecks with
    | some b => .val (.bool (.const b), st.locals)
    | none => .needSplit .ubChecks
  | .runtimeChecks _ => .unknown

theorem symEvalOperand_sound {rootLC localCount : Nat} {s₀ : MirState}
    {st : SymState} (hmatch : st.pc.Matches rootLC s₀)
    (op : Operand) {v : SymVal} {locals' : Nat → Option SymVal}
    (h : symEvalOperand rootLC localCount st op = .val (v, locals')) :
    evalOperand localCount (st.toMirState rootLC s₀) op =
      some (v.denote s₀, denoteLocals s₀ (st.frameId == 0) rootLC locals') := by
  cases op with
  | copy src =>
    dsimp [symEvalOperand] at h
    cases hp : symEvalPlace rootLC localCount st src with
    | none => rw [hp] at h; cases h
    | some sv =>
      rw [hp] at h
      injection h with hpair
      injection hpair with hv hloc
      subst hv; subst hloc
      dsimp [evalOperand]
      rw [symEvalPlace_sound hmatch src hp]
      rfl
  | move src =>
    dsimp [symEvalOperand] at h
    cases hp : symEvalPlace rootLC localCount st src with
    | none => rw [hp] at h; cases h
    | some sv =>
      rw [hp] at h
      dsimp at h
      cases hde :
          symDeinitPlace (st.frameId == 0) rootLC localCount st.locals src with
      | none => rw [hde] at h; cases h
      | some loc' =>
        rw [hde] at h
        injection h with hpair
        injection hpair with hv hloc
        subst hv; subst hloc
        dsimp [evalOperand]
        rw [symEvalPlace_sound hmatch src hp]
        dsimp [Option.bind, SymState.toMirState]
        rw [symDeinitPlace_sound s₀ (st.frameId == 0) rootLC localCount
              st.locals src hde]
        rfl
  | constVal cv =>
    dsimp [symEvalOperand] at h
    cases cv <;> try (cases h; done)
    case usize n =>
      injection h with hpair
      injection hpair with hv hloc
      subst hv; subst hloc
      rfl
    case bool b =>
      injection h with hpair
      injection hpair with hv hloc
      subst hv; subst hloc
      rfl
    case unit =>
      injection h with hpair
      injection hpair with hv hloc
      subst hv; subst hloc
      rfl
  | runtimeChecks kind =>
    cases kind with
    | ubChecks =>
      dsimp [symEvalOperand] at h
      cases hub : st.pc.ubChecks with
      | none => rw [hub] at h; cases h
      | some b =>
        rw [hub] at h
        injection h with hpair
        injection hpair with hv hloc
        subst hv; subst hloc
        have hubEq := hmatch.2.2.2.2.2.2.1
        rw [hub] at hubEq
        dsimp [evalOperand, SymVal.denote, SymBool.denote, SymState.toMirState]
        rw [hubEq]
    | overflowChecks | contractChecks =>
      cases h

/-- Evaluate a list of operands left-to-right symbolically. -/
def symEvalOperandList (rootLC localCount : Nat) (st : SymState) :
    List Operand → SymEvalRes (List SymVal × (Nat → Option SymVal))
  | [] => .val ([], st.locals)
  | op :: rest =>
    match symEvalOperand rootLC localCount st op with
    | .val (v, locals1) =>
      match symEvalOperandList rootLC localCount
          { st with locals := locals1 } rest with
      | .val (vs, locals2) => .val (v :: vs, locals2)
      | .needSplit sp => .needSplit sp
      | .unknown => .unknown
    | .needSplit sp => .needSplit sp
    | .unknown => .unknown

theorem symEvalOperandList_sound {rootLC localCount : Nat} {s₀ : MirState} :
    ∀ (ops : List Operand) (st : SymState) {vs : List SymVal}
      {locals' : Nat → Option SymVal},
      st.pc.Matches rootLC s₀ →
      symEvalOperandList rootLC localCount st ops = .val (vs, locals') →
      evalOperandList localCount (st.toMirState rootLC s₀) ops =
        some (vs.map (SymVal.denote s₀),
          denoteLocals s₀ (st.frameId == 0) rootLC locals')
  | [], st, vs, locals', _, h => by
    dsimp [symEvalOperandList] at h
    injection h with hpair
    injection hpair with hvs hloc
    subst hvs; subst hloc
    rfl
  | op :: rest, st, vs, locals', hmatch, h => by
    dsimp [symEvalOperandList] at h
    cases hop : symEvalOperand rootLC localCount st op with
    | needSplit _ => rw [hop] at h; cases h
    | unknown => rw [hop] at h; cases h
    | val p1 =>
      rcases p1 with ⟨v, locals1⟩
      rw [hop] at h
      dsimp at h
      cases hrest :
          symEvalOperandList rootLC localCount
            { st with locals := locals1 } rest with
      | needSplit _ => rw [hrest] at h; cases h
      | unknown => rw [hrest] at h; cases h
      | val p2 =>
        rcases p2 with ⟨vsRest, locals2⟩
        rw [hrest] at h
        injection h with hpair
        injection hpair with hvs hloc
        subst hvs; subst hloc
        dsimp [evalOperandList]
        rw [symEvalOperand_sound hmatch op hop]
        dsimp [Option.bind]
        have ih :=
          symEvalOperandList_sound rest { st with locals := locals1 } hmatch
            hrest
        dsimp [SymState.toMirState] at ih ⊢
        rw [ih]
        rfl

/-- Evaluate a binary operation `BinOp` on two symbolic `SymVal` operands. -/
def symEvalBinOp (pc : PathCond) (op : BinOp) (lhs rhs : SymVal) :
    Option SymVal :=
  match op, lhs, rhs with
  | .eq, .usize a, .usize b => some (.bool (.eq a b))
  | .eq, .bool a, .bool b =>
    match evalSymBool pc a, evalSymBool pc b with
    | .val ba, .val bb => some (.bool (.const (decide (ba = bb))))
    | _, _ => none
  | .eq, .unit, .unit => some (.bool (.const true))
  | .ne, .usize a, .usize b => some (.bool (.ne a b))
  | .ne, .bool a, .bool b =>
    match evalSymBool pc a, evalSymBool pc b with
    | .val ba, .val bb => some (.bool (.const (decide (ba ≠ bb))))
    | _, _ => none
  | .ne, .unit, .unit => some (.bool (.const false))
  | .lt, .usize a, .usize b =>
    match evalSymNatUnder pc a, evalSymNatUnder pc b with
    | .const na, .const nb => some (.bool (.const (decide (na < nb))))
    | _, _ => none
  | .le, .usize a, .usize b =>
    match evalSymNatUnder pc a, evalSymNatUnder pc b with
    | .const na, .const nb => some (.bool (.const (decide (na ≤ nb))))
    | _, _ => none
  | .gt, .usize a, .usize b =>
    match evalSymNatUnder pc a, evalSymNatUnder pc b with
    | .const na, .const nb => some (.bool (.const (decide (nb < na))))
    | _, _ => none
  | .ge, .usize a, .usize b =>
    match evalSymNatUnder pc a, evalSymNatUnder pc b with
    | .const na, .const nb => some (.bool (.const (decide (nb ≤ na))))
    | _, _ => none
  | .add, .usize a, .usize b =>
    match evalSymNatUnder pc a, evalSymNatUnder pc b with
    | .const na, .const nb => some (.usize (.const (na + nb)))
    | _, _ => none
  | .sub, .usize a, .usize b =>
    match evalSymNatUnder pc a, evalSymNatUnder pc b with
    | .const na, .const nb =>
      if decide (nb ≤ na) then some (.usize (.const (na - nb))) else none
    | _, _ => none
  | .mul, .usize a, .usize b =>
    match evalSymNatUnder pc a, evalSymNatUnder pc b with
    | .const na, .const nb => some (.usize (.const (na * nb)))
    | _, _ => none
  | .bitAnd, .bool a, .bool b =>
    match evalSymBool pc a, evalSymBool pc b with
    | .val ba, .val bb => some (.bool (.const (ba && bb)))
    | _, _ => none
  | .bitOr, .bool a, .bool b =>
    match evalSymBool pc a, evalSymBool pc b with
    | .val ba, .val bb => some (.bool (.const (ba || bb)))
    | _, _ => none
  | .bitXor, .bool a, .bool b =>
    match evalSymBool pc a, evalSymBool pc b with
    | .val ba, .val bb => some (.bool (.const (bne ba bb)))
    | _, _ => none
  | _, _, _ => none

theorem nat_beq_eq_decide (a b : Nat) : (a == b) = decide (a = b) := by
  cases h : decide (a = b) with
  | true => exact beq_iff_eq.mpr (of_decide_eq_true h)
  | false => exact beq_eq_false_iff_ne.mpr (of_decide_eq_false h)

theorem nat_bne_eq_decide (a b : Nat) : (a != b) = decide (a ≠ b) := by
  dsimp [bne]
  rw [nat_beq_eq_decide]
  by_cases h : a = b
  · rw [decide_eq_true h, decide_eq_false (fun hne => hne h)]
    rfl
  · rw [decide_eq_false h, decide_eq_true h]
    rfl

theorem symEvalBinOp_sound {rootLC : Nat} {s₀ : MirState} {pc : PathCond}
    (hmatch : pc.Matches rootLC s₀) (op : BinOp) (lhs rhs : SymVal)
    {out : SymVal}
    (h : symEvalBinOp pc op lhs rhs = some out) :
    evalBinOp op (lhs.denote s₀) (rhs.denote s₀) = some (out.denote s₀) := by
  cases op <;> cases lhs <;> cases rhs <;> try (cases h; done)
  case eq.usize.usize a b =>
    injection h with hout; subst hout
    dsimp [evalBinOp, SymVal.denote, SymBool.denote]
    rw [nat_beq_eq_decide]
  case eq.bool.bool a b =>
    dsimp [symEvalBinOp] at h
    cases ha : evalSymBool pc a <;> cases hb : evalSymBool pc b <;>
      try (rw [ha, hb] at h; cases h; done)
    case val.val ba bb =>
      rw [ha, hb] at h
      injection h with hout; subst hout
      dsimp [evalBinOp, SymVal.denote, SymBool.denote]
      rw [evalSymBool_sound hmatch a ha, evalSymBool_sound hmatch b hb]
  case eq.unit.unit =>
    injection h with hout; subst hout; rfl
  case ne.usize.usize a b =>
    injection h with hout; subst hout
    dsimp [evalBinOp, SymVal.denote, SymBool.denote]
    rw [nat_bne_eq_decide]
  case ne.bool.bool a b =>
    dsimp [symEvalBinOp] at h
    cases ha : evalSymBool pc a <;> cases hb : evalSymBool pc b <;>
      try (rw [ha, hb] at h; cases h; done)
    case val.val ba bb =>
      rw [ha, hb] at h
      injection h with hout; subst hout
      dsimp [evalBinOp, SymVal.denote, SymBool.denote]
      rw [evalSymBool_sound hmatch a ha, evalSymBool_sound hmatch b hb]
  case ne.unit.unit =>
    injection h with hout; subst hout; rfl
  case lt.usize.usize a b =>
    dsimp [symEvalBinOp] at h
    cases ha : evalSymNatUnder pc a <;> cases hb : evalSymNatUnder pc b <;>
      try (rw [ha, hb] at h; cases h; done)
    case const.const na nb =>
      rw [ha, hb] at h
      injection h with hout; subst hout
      have ha' := evalSymNatUnder_sound hmatch a; rw [ha] at ha'
      have hb' := evalSymNatUnder_sound hmatch b; rw [hb] at hb'
      dsimp [evalBinOp, SymVal.denote, SymBool.denote, SymNat.denote] at ha' hb' ⊢
      rw [← ha', ← hb']
  case le.usize.usize a b =>
    dsimp [symEvalBinOp] at h
    cases ha : evalSymNatUnder pc a <;> cases hb : evalSymNatUnder pc b <;>
      try (rw [ha, hb] at h; cases h; done)
    case const.const na nb =>
      rw [ha, hb] at h
      injection h with hout; subst hout
      have ha' := evalSymNatUnder_sound hmatch a; rw [ha] at ha'
      have hb' := evalSymNatUnder_sound hmatch b; rw [hb] at hb'
      dsimp [evalBinOp, SymVal.denote, SymBool.denote, SymNat.denote] at ha' hb' ⊢
      rw [← ha', ← hb']
  case gt.usize.usize a b =>
    dsimp [symEvalBinOp] at h
    cases ha : evalSymNatUnder pc a <;> cases hb : evalSymNatUnder pc b <;>
      try (rw [ha, hb] at h; cases h; done)
    case const.const na nb =>
      rw [ha, hb] at h
      injection h with hout; subst hout
      have ha' := evalSymNatUnder_sound hmatch a; rw [ha] at ha'
      have hb' := evalSymNatUnder_sound hmatch b; rw [hb] at hb'
      dsimp [evalBinOp, SymVal.denote, SymBool.denote, SymNat.denote] at ha' hb' ⊢
      rw [← ha', ← hb']
  case ge.usize.usize a b =>
    dsimp [symEvalBinOp] at h
    cases ha : evalSymNatUnder pc a <;> cases hb : evalSymNatUnder pc b <;>
      try (rw [ha, hb] at h; cases h; done)
    case const.const na nb =>
      rw [ha, hb] at h
      injection h with hout; subst hout
      have ha' := evalSymNatUnder_sound hmatch a; rw [ha] at ha'
      have hb' := evalSymNatUnder_sound hmatch b; rw [hb] at hb'
      dsimp [evalBinOp, SymVal.denote, SymBool.denote, SymNat.denote] at ha' hb' ⊢
      rw [← ha', ← hb']
  case add.usize.usize a b =>
    dsimp [symEvalBinOp] at h
    cases ha : evalSymNatUnder pc a <;> cases hb : evalSymNatUnder pc b <;>
      try (rw [ha, hb] at h; cases h; done)
    case const.const na nb =>
      rw [ha, hb] at h
      injection h with hout; subst hout
      have ha' := evalSymNatUnder_sound hmatch a; rw [ha] at ha'
      have hb' := evalSymNatUnder_sound hmatch b; rw [hb] at hb'
      dsimp [evalBinOp, SymVal.denote, SymNat.denote] at ha' hb' ⊢
      rw [← ha', ← hb']
  case sub.usize.usize a b =>
    dsimp [symEvalBinOp] at h
    cases ha : evalSymNatUnder pc a <;> cases hb : evalSymNatUnder pc b <;>
      try (rw [ha, hb] at h; cases h; done)
    case const.const na nb =>
      rw [ha, hb] at h
      dsimp at h
      have ha' : a.denote s₀ = na := by
        rw [← evalSymNatUnder_sound hmatch a, ha]; rfl
      have hb' : b.denote s₀ = nb := by
        rw [← evalSymNatUnder_sound hmatch b, hb]; rfl
      dsimp [evalBinOp, SymVal.denote]
      rw [ha', hb']
      cases hle : decide (nb ≤ na) with
      | false => rw [hle] at h; cases h
      | true =>
        rw [hle] at h
        injection h with hout; subst hout
        rfl
  case mul.usize.usize a b =>
    dsimp [symEvalBinOp] at h
    cases ha : evalSymNatUnder pc a <;> cases hb : evalSymNatUnder pc b <;>
      try (rw [ha, hb] at h; cases h; done)
    case const.const na nb =>
      rw [ha, hb] at h
      injection h with hout; subst hout
      have ha' := evalSymNatUnder_sound hmatch a; rw [ha] at ha'
      have hb' := evalSymNatUnder_sound hmatch b; rw [hb] at hb'
      dsimp [evalBinOp, SymVal.denote, SymNat.denote] at ha' hb' ⊢
      rw [← ha', ← hb']
  case bitAnd.bool.bool a b =>
    dsimp [symEvalBinOp] at h
    cases ha : evalSymBool pc a <;> cases hb : evalSymBool pc b <;>
      try (rw [ha, hb] at h; cases h; done)
    case val.val ba bb =>
      rw [ha, hb] at h
      injection h with hout; subst hout
      dsimp [evalBinOp, SymVal.denote, SymBool.denote]
      rw [evalSymBool_sound hmatch a ha, evalSymBool_sound hmatch b hb]
  case bitOr.bool.bool a b =>
    dsimp [symEvalBinOp] at h
    cases ha : evalSymBool pc a <;> cases hb : evalSymBool pc b <;>
      try (rw [ha, hb] at h; cases h; done)
    case val.val ba bb =>
      rw [ha, hb] at h
      injection h with hout; subst hout
      dsimp [evalBinOp, SymVal.denote, SymBool.denote]
      rw [evalSymBool_sound hmatch a ha, evalSymBool_sound hmatch b hb]
  case bitXor.bool.bool a b =>
    dsimp [symEvalBinOp] at h
    cases ha : evalSymBool pc a <;> cases hb : evalSymBool pc b <;>
      try (rw [ha, hb] at h; cases h; done)
    case val.val ba bb =>
      rw [ha, hb] at h
      injection h with hout; subst hout
      dsimp [evalBinOp, SymVal.denote, SymBool.denote]
      rw [evalSymBool_sound hmatch a ha, evalSymBool_sound hmatch b hb]

/-- Evaluate a unary operation `UnOp` on a `SymVal`. -/
def symEvalUnOp (op : UnOp) (v : SymVal) : Option SymVal :=
  match op, v with
  | .not, .bool b => some (.bool (.not b))
  | _, _ => none

theorem symEvalUnOp_sound (s₀ : MirState) (op : UnOp) (v : SymVal)
    {out : SymVal} (h : symEvalUnOp op v = some out) :
    evalUnOp op (v.denote s₀) = some (out.denote s₀) := by
  cases op <;> cases v <;> try (cases h; done)
  case not.bool b =>
    injection h with hout; subst hout; rfl

/-!
### Symbolic Type Layouts (`symTyLayoutFuel`, `symEvalTyByteSize`, `symEvalLayoutQuery`)
-/

/-- Sequential `#[repr(C)]` field layout fold over symbolic `(SymNat × Nat)`
layouts when every field has a concrete `.const fSz` size. -/
def symFoldReprCFields (unfold : MirTy → Option (SymNat × Nat)) :
    List FieldDecl → Nat → Nat → Option (SymNat × Nat)
  | [], offset, maxAlign =>
    some (.const (alignUp offset maxAlign), maxAlign)
  | f :: rest, offset, maxAlign =>
    match unfold f.ty with
    | some (.const fSz, fAlign) =>
      let alignedOffset := alignUp offset fAlign
      symFoldReprCFields unfold rest (alignedOffset + fSz)
        (Nat.max maxAlign fAlign)
    | _ => none

theorem symFoldReprCFields_sound (s₀ : MirState)
    (unfold : MirTy → Option (SymNat × Nat))
    (cUnfold : MirTy → Option (Nat × Nat))
    (hunfold : ∀ ty sz al,
      unfold ty = some (sz, al) →
      cUnfold ty = some (sz.denote s₀, al)) :
    ∀ (fields : List FieldDecl) (offset maxAlign : Nat)
      {outSz : SymNat} {outAlign : Nat},
      symFoldReprCFields unfold fields offset maxAlign =
        some (outSz, outAlign) →
      foldReprCFields cUnfold fields offset maxAlign =
        some (outSz.denote s₀, outAlign)
  | [], offset, maxAlign, outSz, outAlign, h => by
    dsimp [symFoldReprCFields] at h
    injection h with hpair
    injection hpair with hsz hal
    subst hsz; subst hal
    rfl
  | f :: rest, offset, maxAlign, outSz, outAlign, h => by
    dsimp [symFoldReprCFields] at h
    cases hu : unfold f.ty with
    | none => rw [hu] at h; cases h
    | some p =>
      rcases p with ⟨fSymSz, fAlign⟩
      cases fSymSz <;> try (rw [hu] at h; cases h; done)
      case const fSz =>
        rw [hu] at h
        dsimp at h
        dsimp [foldReprCFields]
        rw [hunfold f.ty (.const fSz) fAlign hu]
        dsimp [SymNat.denote, Option.bind]
        exact symFoldReprCFields_sound s₀ unfold cUnfold hunfold rest
          (alignUp offset fAlign + fSz) (Nat.max maxAlign fAlign) h

/-- Symbolic `#[repr(C)]` field offset computation. -/
def symReprCFieldOffset (unfold : MirTy → Option (SymNat × Nat)) :
    List FieldDecl → Nat → Nat → Option Nat
  | [], _, _ => none
  | f :: rest, 0, offset =>
    match unfold f.ty with
    | some (.const fSz, fAlign) =>
      let alignedOffset := alignUp offset fAlign
      (symFoldReprCFields unfold rest (alignedOffset + fSz) fAlign).map
        fun _ => alignedOffset
    | _ => none
  | f :: rest, idx + 1, offset =>
    match unfold f.ty with
    | some (.const fSz, fAlign) =>
      let alignedOffset := alignUp offset fAlign
      symReprCFieldOffset unfold rest idx (alignedOffset + fSz)
    | _ => none

theorem symReprCFieldOffset_sound (s₀ : MirState)
    (unfold : MirTy → Option (SymNat × Nat))
    (cUnfold : MirTy → Option (Nat × Nat))
    (hunfold : ∀ ty sz al,
      unfold ty = some (sz, al) →
      cUnfold ty = some (sz.denote s₀, al)) :
    ∀ (fields : List FieldDecl) (fieldIdx offset : Nat) {outOff : Nat},
      symReprCFieldOffset unfold fields fieldIdx offset = some outOff →
      reprCFieldOffset cUnfold fields fieldIdx offset = some outOff
  | [], _, _, _, h => by cases h
  | f :: rest, 0, offset, outOff, h => by
    dsimp [symReprCFieldOffset] at h
    cases hu : unfold f.ty with
    | none => rw [hu] at h; cases h
    | some p =>
      rcases p with ⟨fSymSz, fAlign⟩
      cases fSymSz <;> try (rw [hu] at h; cases h; done)
      case const fSz =>
        rw [hu] at h
        dsimp at h
        dsimp [reprCFieldOffset]
        rw [hunfold f.ty (.const fSz) fAlign hu]
        dsimp [SymNat.denote, Option.bind]
        cases hfold :
            symFoldReprCFields unfold rest
              (alignUp offset fAlign + fSz) fAlign with
        | none => rw [hfold] at h; cases h
        | some fp =>
          rcases fp with ⟨totSz, totAlign⟩
          rw [hfold] at h
          injection h with hoff
          subst hoff
          rw [symFoldReprCFields_sound s₀ unfold cUnfold hunfold rest
                (alignUp offset fAlign + fSz) fAlign hfold]
          rfl
  | f :: rest, idx + 1, offset, outOff, h => by
    dsimp [symReprCFieldOffset] at h
    cases hu : unfold f.ty with
    | none => rw [hu] at h; cases h
    | some p =>
      rcases p with ⟨fSymSz, fAlign⟩
      cases fSymSz <;> try (rw [hu] at h; cases h; done)
      case const fSz =>
        rw [hu] at h
        dsimp at h
        dsimp [reprCFieldOffset]
        rw [hunfold f.ty (.const fSz) fAlign hu]
        dsimp [SymNat.denote, Option.bind]
        exact symReprCFieldOffset_sound s₀ unfold cUnfold hunfold rest idx
          (alignUp offset fAlign + fSz) h

/-- Symbolic byte size and alignment `(SymNat × Nat)` of `ty`. -/
def symTyLayoutStep (adts : List AdtDecl) (target : TargetLayout)
    (unfold : MirTy → Option (SymNat × Nat)) : MirTy → Option (SymNat × Nat)
  | .usize | .isize =>
    some (.const target.ptrByteWidth, target.ptrByteWidth)
  | .uint w | .int w =>
    (intBitWidthLayout target w).map fun (sz, al) => (.const sz, al)
  | .bool => some (.const 1, 1)
  | .char => some (.const 4, 4)
  | .unit => some (.const 0, 1)
  | .param idx => some (.tySize idx, 1)
  | .ref inner | .rawPtr inner _ =>
    (symTyLayoutStep adts target unfold inner).map fun _ =>
      (.const target.ptrByteWidth, target.ptrByteWidth)
  | .array elem len =>
    (symTyLayoutStep adts target unfold elem).bind fun (elemSz, elemAlign) =>
      match elemSz with
      | .const esz =>
        let sz := esz * len
        if decide (sz ≤ isizeMaxBytes) then
          some (.const sz, elemAlign)
        else
          none
      | _ => none
  | .arraySizeOf elem sizedTy =>
    (symTyLayoutStep adts target unfold elem).bind fun (elemSz, elemAlign) =>
      (symTyLayoutStep adts target unfold sizedTy).bind fun (n, _) =>
        if decide (elemSz = .const 1) then
          some (n, elemAlign)
        else
          match elemSz, n with
          | .const esz, .const nsz => some (.const (esz * nsz), elemAlign)
          | _, _ => none
  | .adt id =>
    (findAdtDecl adts id).bind fun decl =>
      let baseLayout :=
        match decl.fields with
        | [f] => unfold f.ty
        | fields => symFoldReprCFields unfold fields 0 1
      match decl.repr with
      | .unmodeled => none
      | .transparent | .c => baseLayout
      | .rust =>
        match baseLayout with
        | some (.const sz, al) => some (.adtSize sz id, al)
        | _ => none
  | _ => none

theorem symTyLayoutStep_sound (s₀ : MirState) (adts : List AdtDecl)
    (target : TargetLayout)
    (unfold : MirTy → Option (SymNat × Nat))
    (cUnfold : MirTy → Option (Nat × Nat))
    (hunfold : ∀ ty sz al,
      unfold ty = some (sz, al) →
      cUnfold ty = some (sz.denote s₀, al)) :
    ∀ (ty : MirTy) {outSz : SymNat} {outAlign : Nat},
      symTyLayoutStep adts target unfold ty = some (outSz, outAlign) →
      tyLayoutStep adts s₀.tySizes s₀.adtPad target cUnfold ty =
        some (outSz.denote s₀, outAlign)
  | .usize, _, _, h => by
    injection h with hp; injection hp with h1 h2; subst h1; subst h2; rfl
  | .isize, _, _, h => by
    injection h with hp; injection hp with h1 h2; subst h1; subst h2; rfl
  | .uint w, _, _, h => by
    dsimp [symTyLayoutStep, tyLayoutStep] at h ⊢
    cases hi : intBitWidthLayout target w with
    | none => rw [hi] at h; cases h
    | some p =>
      rcases p with ⟨sz, al⟩
      rw [hi] at h
      injection h with hp; injection hp with h1 h2; subst h1; subst h2; rfl
  | .int w, _, _, h => by
    dsimp [symTyLayoutStep, tyLayoutStep] at h ⊢
    cases hi : intBitWidthLayout target w with
    | none => rw [hi] at h; cases h
    | some p =>
      rcases p with ⟨sz, al⟩
      rw [hi] at h
      injection h with hp; injection hp with h1 h2; subst h1; subst h2; rfl
  | .bool, _, _, h => by
    injection h with hp; injection hp with h1 h2; subst h1; subst h2; rfl
  | .char, _, _, h => by
    injection h with hp; injection hp with h1 h2; subst h1; subst h2; rfl
  | .unit, _, _, h => by
    injection h with hp; injection hp with h1 h2; subst h1; subst h2; rfl
  | .param idx, _, _, h => by
    injection h with hp; injection hp with h1 h2; subst h1; subst h2; rfl
  | .ref inner, _, _, h => by
    dsimp [symTyLayoutStep, tyLayoutStep] at h ⊢
    cases hi : symTyLayoutStep adts target unfold inner with
    | none => rw [hi] at h; cases h
    | some p =>
      rcases p with ⟨isz, ial⟩
      rw [hi] at h
      injection h with hp; injection hp with h1 h2; subst h1; subst h2
      rw [symTyLayoutStep_sound s₀ adts target unfold cUnfold hunfold inner hi]
      rfl
  | .rawPtr inner m, _, _, h => by
    dsimp [symTyLayoutStep, tyLayoutStep] at h ⊢
    cases hi : symTyLayoutStep adts target unfold inner with
    | none => rw [hi] at h; cases h
    | some p =>
      rcases p with ⟨isz, ial⟩
      rw [hi] at h
      injection h with hp; injection hp with h1 h2; subst h1; subst h2
      rw [symTyLayoutStep_sound s₀ adts target unfold cUnfold hunfold inner hi]
      rfl
  | .array elem len, _, _, h => by
    dsimp [symTyLayoutStep, tyLayoutStep] at h ⊢
    cases he : symTyLayoutStep adts target unfold elem with
    | none => rw [he] at h; cases h
    | some p =>
      rcases p with ⟨elemSz, elemAlign⟩
      rw [he] at h
      dsimp [Option.bind] at h
      cases elemSz <;> try (cases h; done)
      case const esz =>
        dsimp at h
        rw [symTyLayoutStep_sound s₀ adts target unfold cUnfold hunfold elem he]
        dsimp [SymNat.denote, Option.bind]
        cases hle : decide (esz * len ≤ isizeMaxBytes) with
        | false => rw [hle] at h; cases h
        | true =>
          rw [hle] at h
          injection h with hp; injection hp with h1 h2; subst h1; subst h2
          rfl
  | .arraySizeOf elem sizedTy, _, _, h => by
    dsimp [symTyLayoutStep, tyLayoutStep] at h ⊢
    cases he : symTyLayoutStep adts target unfold elem with
    | none => rw [he] at h; cases h
    | some pe =>
      rcases pe with ⟨elemSz, elemAlign⟩
      rw [he] at h
      dsimp [Option.bind] at h
      cases hs : symTyLayoutStep adts target unfold sizedTy with
      | none => rw [hs] at h; cases h
      | some ps =>
        rcases ps with ⟨n, sAlign⟩
        rw [hs] at h
        dsimp [Option.bind] at h
        rw [symTyLayoutStep_sound s₀ adts target unfold cUnfold hunfold elem he]
        rw [symTyLayoutStep_sound s₀ adts target unfold cUnfold hunfold sizedTy hs]
        dsimp [Option.bind, Option.map]
        cases h1 : decide (elemSz = .const 1) with
        | true =>
          rw [h1] at h
          injection h with hp; injection hp with hsz hal; subst hsz; subst hal
          rw [of_decide_eq_true h1]
          dsimp [SymNat.denote]
          rw [Nat.one_mul]
        | false =>
          rw [h1] at h
          dsimp at h
          cases elemSz <;> cases n <;> try (cases h; done)
          case const.const esz nsz =>
            injection h with hp; injection hp with hsz hal; subst hsz; subst hal
            rfl
  | .adt id, _, _, h => by
    dsimp [symTyLayoutStep, tyLayoutStep] at h ⊢
    cases hfind : findAdtDecl adts id with
    | none => rw [hfind] at h; cases h
    | some decl =>
      rw [hfind] at h
      dsimp [Option.bind] at h ⊢
      have hbase_sound :
          ∀ {bsz : SymNat} {bal : Nat},
            (match decl.fields with
             | [f] => unfold f.ty
             | fields => symFoldReprCFields unfold fields 0 1) =
              some (bsz, bal) →
            (match decl.fields with
             | [f] => cUnfold f.ty
             | fields => foldReprCFields cUnfold fields 0 1) =
              some (bsz.denote s₀, bal) := by
        intro bsz bal hb
        cases hfields : decl.fields with
        | nil =>
          rw [hfields] at hb
          exact symFoldReprCFields_sound s₀ unfold cUnfold hunfold [] 0 1 hb
        | cons f1 rest =>
          cases rest with
          | nil =>
            rw [hfields] at hb
            exact hunfold f1.ty bsz bal hb
          | cons f2 rest2 =>
            rw [hfields] at hb
            exact symFoldReprCFields_sound s₀ unfold cUnfold hunfold
              (f1 :: f2 :: rest2) 0 1 hb
      cases hrepr : decl.repr with
      | unmodeled => rw [hrepr] at h; cases h
      | transparent =>
        rw [hrepr] at h
        exact hbase_sound h
      | c =>
        rw [hrepr] at h
        exact hbase_sound h
      | rust =>
        rw [hrepr] at h
        dsimp at h ⊢
        cases hb :
            (match decl.fields with
             | [f] => unfold f.ty
             | fields => symFoldReprCFields unfold fields 0 1) with
        | none => rw [hb] at h; cases h
        | some bp =>
          rcases bp with ⟨bsz, bal⟩
          cases bsz <;> try (rw [hb] at h; cases h; done)
          case const sz =>
            rw [hb] at h
            injection h with hp; injection hp with hsz hal; subst hsz; subst hal
            rw [hbase_sound hb]
            rfl
  | .float _, _, _, h => by cases h
  | .str, _, _, h => by cases h
  | .never, _, _, h => by cases h
  | .refMut _, _, _, h => by cases h
  | .slice _, _, _, h => by cases h
  | .tuple _, _, _, h => by cases h
  | .fnDef _, _, _, h => by cases h
  | .fnPtr, _, _, h => by cases h
  | .unmodeled, _, _, h => by cases h

def symTyLayoutFuel (adts : List AdtDecl)
    (target : TargetLayout := defaultTargetLayout) :
    Nat → MirTy → Option (SymNat × Nat)
  | 0, _ => none
  | fuel + 1, ty =>
    symTyLayoutStep adts target (symTyLayoutFuel adts target fuel) ty

theorem symTyLayoutFuel_sound (s₀ : MirState) (adts : List AdtDecl)
    (target : TargetLayout) :
    ∀ (fuel : Nat) (ty : MirTy) {outSz : SymNat} {outAlign : Nat},
      symTyLayoutFuel adts target fuel ty = some (outSz, outAlign) →
      tyLayoutFuel adts s₀.tySizes s₀.adtPad target fuel ty =
        some (outSz.denote s₀, outAlign)
  | 0, _, _, _, h => by cases h
  | fuel + 1, ty, _, _, h =>
    symTyLayoutStep_sound s₀ adts target
      (symTyLayoutFuel adts target fuel)
      (tyLayoutFuel adts s₀.tySizes s₀.adtPad target fuel)
      (fun t s a ht => symTyLayoutFuel_sound s₀ adts target fuel t ht)
      ty h

/-- Symbolic byte size of `ty`. -/
def symEvalTyByteSize (adts : List AdtDecl) (ty : MirTy)
    (target : TargetLayout := defaultTargetLayout) : Option SymNat :=
  (symTyLayoutFuel adts target (adts.length + 1) ty).map Prod.fst

theorem symEvalTyByteSize_sound (s₀ : MirState) (adts : List AdtDecl)
    (ty : MirTy) (target : TargetLayout) {outSz : SymNat}
    (h : symEvalTyByteSize adts ty target = some outSz) :
    evalTyByteSize adts s₀.tySizes ty s₀.adtPad target =
      some (outSz.denote s₀) := by
  unfold symEvalTyByteSize at h
  unfold evalTyByteSize
  cases hfuel : symTyLayoutFuel adts target (adts.length + 1) ty with
  | none => rw [hfuel] at h; cases h
  | some p =>
    rcases p with ⟨sz, al⟩
    rw [hfuel] at h
    injection h with hsz; subst hsz
    rw [symTyLayoutFuel_sound s₀ adts target (adts.length + 1) ty hfuel]
    rfl

/-- Symbolic byte alignment of `ty`. -/
def symEvalTyAlign (adts : List AdtDecl) (ty : MirTy)
    (target : TargetLayout := defaultTargetLayout) : Option Nat :=
  (symTyLayoutFuel adts target (adts.length + 1) ty).map Prod.snd

theorem symEvalTyAlign_sound (s₀ : MirState) (adts : List AdtDecl)
    (ty : MirTy) (target : TargetLayout) {outAlign : Nat}
    (h : symEvalTyAlign adts ty target = some outAlign) :
    evalTyAlign adts s₀.tySizes ty s₀.adtPad target = some outAlign := by
  unfold symEvalTyAlign at h
  unfold evalTyAlign
  cases hfuel : symTyLayoutFuel adts target (adts.length + 1) ty with
  | none => rw [hfuel] at h; cases h
  | some p =>
    rcases p with ⟨sz, al⟩
    rw [hfuel] at h
    injection h with hal; subst hal
    rw [symTyLayoutFuel_sound s₀ adts target (adts.length + 1) ty hfuel]
    rfl

/-- Decide whether `decl.isZeroPaddedWrapper s₀.adtPad` holds under `pc`,
requesting `.needSplit (.adtPad decl.id)` when `decl.repr == .rust` and
`decl.id` is not yet constrained in `pc.adtPadZero`. -/
def symIsZeroPaddedWrapper (pc : PathCond) (decl : AdtDecl) :
    SymEvalRes Bool :=
  if decl.repr == .transparent then
    .val true
  else if decl.repr == .rust then
    match pc.adtPadZero.find? (fun p => decide (p.1 = decl.id)) with
    | some (_, b) => .val b
    | none => .needSplit (.adtPad decl.id)
  else
    .val false

theorem symIsZeroPaddedWrapper_sound {rootLC : Nat} {s₀ : MirState}
    {pc : PathCond} (hmatch : pc.Matches rootLC s₀) (decl : AdtDecl)
    {res : Bool}
    (h : symIsZeroPaddedWrapper pc decl = .val res) :
    decl.isZeroPaddedWrapper s₀.adtPad = res := by
  unfold symIsZeroPaddedWrapper at h
  unfold AdtDecl.isZeroPaddedWrapper
  cases htr : (decl.repr == .transparent) with
  | true =>
    rw [htr] at h
    injection h with hres
  | false =>
    rw [htr] at h
    dsimp at h ⊢
    cases hru : (decl.repr == .rust) with
    | false =>
      rw [hru] at h
      injection h with hres
    | true =>
      rw [hru] at h
      dsimp at h ⊢
      cases hfind : pc.adtPadZero.find? (fun p => decide (p.1 = decl.id)) with
      | none => rw [hfind] at h; cases h
      | some p =>
        rw [hfind] at h
        rcases list_find_some_mem hfind with ⟨hmem, hdec⟩
        rcases p with ⟨id', b⟩
        injection h with hres; subst hres
        have hid : id' = decl.id := of_decide_eq_true hdec
        have hpad := hmatch.2.2.2.1 (id', b) hmem
        rw [← hid]
        cases b with
        | true =>
          dsimp at hpad
          rw [hpad]
          rfl
        | false =>
          dsimp at hpad
          have hne : s₀.adtPad id' ≠ 0 := by omega
          exact beq_eq_false_iff_ne.mpr hne

/-- Evaluate a `LayoutQuery` symbolically under `pc`. -/
def symEvalLayoutQuery (adts : List AdtDecl) (pc : PathCond)
    (query : LayoutQuery) (target : TargetLayout := defaultTargetLayout) :
    SymEvalRes SymNat :=
  match query with
  | .sizeOf ty =>
    match symEvalTyByteSize adts ty target with
    | some sz => .val sz
    | none => .unknown
  | .alignOf ty =>
    match symEvalTyAlign adts ty target with
    | some al => .val (.const al)
    | none => .unknown
  | .offsetOf (.adt id) variantIdx fieldIdx =>
    if variantIdx == 0 then
      match findAdtDecl adts id with
      | none => .unknown
      | some decl =>
        let unfold := symTyLayoutFuel adts target (adts.length + 1)
        if decl.repr == .c then
          match symReprCFieldOffset unfold decl.fields fieldIdx 0 with
          | some off => .val (.const off)
          | none => .unknown
        else
          match symIsZeroPaddedWrapper pc decl with
          | .needSplit sp => .needSplit sp
          | .unknown => .unknown
          | .val isZero =>
            if isZero && fieldIdx == 0 && decl.fields.length == 1 then
              match symEvalTyByteSize adts (.adt id) target with
              | some _ => .val (.const 0)
              | none => .unknown
            else
              .unknown
    else
      .unknown
  | .offsetOf _ _ _ => .unknown

theorem symEvalLayoutQuery_sound {rootLC : Nat} {s₀ : MirState}
    {pc : PathCond} (hmatch : pc.Matches rootLC s₀) (adts : List AdtDecl)
    (query : LayoutQuery) (target : TargetLayout) {outSz : SymNat}
    (h : symEvalLayoutQuery adts pc query target = .val outSz) :
    evalLayoutQuery adts s₀.tySizes query s₀.adtPad target =
      some (outSz.denote s₀) := by
  cases query with
  | sizeOf ty =>
    dsimp [symEvalLayoutQuery] at h
    cases hsz : symEvalTyByteSize adts ty target with
    | none => rw [hsz] at h; cases h
    | some sz =>
      rw [hsz] at h
      injection h with hout; subst hout
      exact symEvalTyByteSize_sound s₀ adts ty target hsz
  | alignOf ty =>
    dsimp [symEvalLayoutQuery] at h
    cases hal : symEvalTyAlign adts ty target with
    | none => rw [hal] at h; cases h
    | some al =>
      rw [hal] at h
      injection h with hout; subst hout
      exact symEvalTyAlign_sound s₀ adts ty target hal
  | offsetOf ty variantIdx fieldIdx =>
    cases ty <;> try (cases h; done)
    case adt id =>
      dsimp [symEvalLayoutQuery] at h
      dsimp [evalLayoutQuery]
      cases hvar : (variantIdx == 0) with
      | false => rw [hvar] at h; cases h
      | true =>
        rw [hvar] at h
        dsimp at h ⊢
        cases hfind : findAdtDecl adts id with
        | none => rw [hfind] at h; cases h
        | some decl =>
          rw [hfind] at h
          dsimp [Option.bind] at h ⊢
          cases hrepr : (decl.repr == .c) with
          | true =>
            rw [hrepr] at h
            dsimp at h ⊢
            cases hoff :
                symReprCFieldOffset
                  (symTyLayoutFuel adts target (adts.length + 1))
                  decl.fields fieldIdx 0 with
            | none => rw [hoff] at h; cases h
            | some off =>
              rw [hoff] at h
              injection h with hout; subst hout
              exact symReprCFieldOffset_sound s₀
                (symTyLayoutFuel adts target (adts.length + 1))
                (tyLayoutFuel adts s₀.tySizes s₀.adtPad target (adts.length + 1))
                (fun t s a ht =>
                  symTyLayoutFuel_sound s₀ adts target (adts.length + 1) t ht)
                decl.fields fieldIdx 0 hoff
          | false =>
            rw [hrepr] at h
            dsimp at h ⊢
            cases hz : symIsZeroPaddedWrapper pc decl with
            | needSplit _ => rw [hz] at h; cases h
            | unknown => rw [hz] at h; cases h
            | val isZero =>
              rw [hz] at h
              dsimp at h
              rw [symIsZeroPaddedWrapper_sound hmatch decl hz]
              cases hcond : isZero && fieldIdx == 0 && decl.fields.length == 1 with
              | false => rw [hcond] at h; cases h
              | true =>
                rw [hcond] at h
                dsimp at h ⊢
                cases hsz : symEvalTyByteSize adts (.adt id) target with
                | none => rw [hsz] at h; cases h
                | some sz =>
                  rw [hsz] at h
                  injection h with hout; subst hout
                  rw [symEvalTyByteSize_sound s₀ adts (.adt id) target hsz]
                  rfl

/-!
### Symbolic Transmutation (`symPeelTransparent`, `symWrapTransparent`, `symEvalTransmuteVal`, `symEvalTransmuteCopy`)
-/

/-- Symbolic `peelTransparent` under `pc`. -/
def symPeelTransparent (adts : List AdtDecl) (pc : PathCond) :
    Nat → MirTy → SymVal → SymEvalRes (Option (MirTy × SymVal))
  | 0, ty, v => .val (some (ty, v))
  | fuel + 1, .adt id, .adt vId inner =>
    if vId == id then
      match findAdtDecl adts id with
      | some decl =>
        match symIsZeroPaddedWrapper pc decl with
        | .needSplit sp => .needSplit sp
        | .unknown => .unknown
        | .val true =>
          match decl.payloadTy with
          | some payload => symPeelTransparent adts pc fuel payload inner
          | none => .val (some (.adt id, .adt vId inner))
        | .val false =>
          .val (some (.adt id, .adt vId inner))
      | none => .val none
    else
      .val none
  | _ + 1, ty, v => .val (some (ty, v))

theorem symPeelTransparent_sound {rootLC : Nat} {s₀ : MirState}
    {pc : PathCond} (hmatch : pc.Matches rootLC s₀) (adts : List AdtDecl) :
    ∀ (fuel : Nat) (ty : MirTy) (v : SymVal)
      {outOpt : Option (MirTy × SymVal)},
      symPeelTransparent adts pc fuel ty v = .val outOpt →
      peelTransparent adts s₀.adtPad fuel ty (v.denote s₀) =
        outOpt.map (fun (bt, bv) => (bt, bv.denote s₀))
  | 0, ty, v, _, h => by
    dsimp [symPeelTransparent] at h
    injection h with hout; subst hout; rfl
  | fuel + 1, .adt id, .adt vId inner, outOpt, h => by
    dsimp [symPeelTransparent] at h
    dsimp [SymVal.denote, peelTransparent]
    cases hvid : (vId == id) with
    | false =>
      rw [hvid] at h
      injection h with hout; subst hout; rfl
    | true =>
      rw [hvid] at h
      dsimp at h ⊢
      cases hfind : findAdtDecl adts id with
      | none =>
        rw [hfind] at h
        injection h with hout; subst hout; rfl
      | some decl =>
        rw [hfind] at h
        dsimp at h ⊢
        cases hz : symIsZeroPaddedWrapper pc decl with
        | needSplit _ => rw [hz] at h; cases h
        | unknown => rw [hz] at h; cases h
        | val isZero =>
          rw [hz] at h
          rw [symIsZeroPaddedWrapper_sound hmatch decl hz]
          cases isZero with
          | false =>
            dsimp at h ⊢
            injection h with hout; subst hout; rfl
          | true =>
            dsimp at h ⊢
            cases hpay : decl.payloadTy with
            | none =>
              rw [hpay] at h
              injection h with hout; subst hout; rfl
            | some payload =>
              rw [hpay] at h
              exact symPeelTransparent_sound hmatch adts fuel payload inner h
  | _ + 1, .usize, _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .isize, _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .uint _, _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .int _, _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .bool, _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .char, _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .unit, _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .param _, _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .ref _, _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .rawPtr _ _, _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .array _ _, _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .arraySizeOf _ _, _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .float _, _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .str, _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .never, _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .refMut _, _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .slice _, _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .tuple _, _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .fnDef _, _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .fnPtr, _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .unmodeled, _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .adt _, .uninit, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .adt _, .usize _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .adt _, .bool _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .adt _, .unit, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .adt _, .fieldCons _ _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .adt _, .bytes _ _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .adt _, .ref _ _ _ _, _, h => by injection h with hout; subst hout; rfl
  | _ + 1, .adt _, .callerRef _ _, _, h => by injection h with hout; subst hout; rfl

/-- Symbolic `wrapTransparent` under `pc`. -/
def symWrapTransparent (adts : List AdtDecl) (pc : PathCond) :
    Nat → MirTy → MirTy → SymVal → SymEvalRes (Option SymVal)
  | 0, _, _, _ => .val none
  | fuel + 1, baseTy, dstTy, baseVal =>
    if MirTy.beq baseTy dstTy then
      .val (some baseVal)
    else
      match dstTy with
      | .adt id =>
        match findAdtDecl adts id with
        | none => .val none
        | some decl =>
          match symIsZeroPaddedWrapper pc decl with
          | .needSplit sp => .needSplit sp
          | .unknown => .unknown
          | .val isZero =>
            if decl.allFieldsPubSafe && isZero then
              match decl.payloadTy with
              | none => .val none
              | some payload =>
                match symWrapTransparent adts pc fuel baseTy payload baseVal with
                | .val opt => .val (opt.map (.adt id))
                | .needSplit sp => .needSplit sp
                | .unknown => .unknown
            else
              .val none
      | _ => .val none

theorem symWrapTransparent_sound {rootLC : Nat} {s₀ : MirState}
    {pc : PathCond} (hmatch : pc.Matches rootLC s₀) (adts : List AdtDecl) :
    ∀ (fuel : Nat) (baseTy dstTy : MirTy) (baseVal : SymVal)
      {outOpt : Option SymVal},
      symWrapTransparent adts pc fuel baseTy dstTy baseVal = .val outOpt →
      wrapTransparent adts s₀.adtPad fuel baseTy dstTy (baseVal.denote s₀) =
        outOpt.map (SymVal.denote s₀)
  | 0, _, _, _, _, h => by
    dsimp [symWrapTransparent] at h
    injection h with hout; subst hout; rfl
  | fuel + 1, baseTy, dstTy, baseVal, outOpt, h => by
    dsimp [symWrapTransparent] at h
    dsimp [wrapTransparent]
    cases hbeq : MirTy.beq baseTy dstTy with
    | true =>
      rw [hbeq] at h
      injection h with hout; subst hout; rfl
    | false =>
      rw [hbeq] at h
      dsimp at h ⊢
      cases dstTy <;> try (injection h with hout; subst hout; rfl)
      case adt id =>
        dsimp at h ⊢
        cases hfind : findAdtDecl adts id with
        | none =>
          rw [hfind] at h
          injection h with hout; subst hout; rfl
        | some decl =>
          rw [hfind] at h
          dsimp [Option.bind] at h ⊢
          cases hz : symIsZeroPaddedWrapper pc decl with
          | needSplit _ => rw [hz] at h; cases h
          | unknown => rw [hz] at h; cases h
          | val isZero =>
            rw [hz] at h
            dsimp at h
            rw [symIsZeroPaddedWrapper_sound hmatch decl hz]
            cases hcond : decl.allFieldsPubSafe && isZero with
            | false =>
              rw [hcond] at h
              injection h with hout; subst hout; rfl
            | true =>
              rw [hcond] at h
              dsimp at h ⊢
              cases hpay : decl.payloadTy with
              | none =>
                rw [hpay] at h
                injection h with hout; subst hout; rfl
              | some payload =>
                rw [hpay] at h
                dsimp [Option.bind] at h ⊢
                cases hw : symWrapTransparent adts pc fuel baseTy payload baseVal with
                | needSplit _ => rw [hw] at h; cases h
                | unknown => rw [hw] at h; cases h
                | val opt =>
                  rw [hw] at h
                  injection h with hout; subst hout
                  rw [symWrapTransparent_sound hmatch adts fuel baseTy payload
                        baseVal hw]
                  cases opt <;> rfl

/-- Symbolic `extractFieldBits` returning `(Nat × SymNat)`. -/
def symExtractFieldBits (extract : SymVal → MirTy → Option (Nat × SymNat)) :
    List FieldDecl → SymVal → Option (Nat × SymNat)
  | [], .unit => some (0, .const 0)
  | [f], v =>
    match v with
    | .fieldCons _ _ => none
    | _ => extract v f.ty
  | f :: rest, .fieldCons h t =>
    (extract h f.ty).bind fun (sz1, bits1) =>
      (symExtractFieldBits extract rest t).map fun (sz2, bits2) =>
        (sz1 + sz2, .bitPack bits1 bits2 sz1)
  | _, _ => none

theorem symExtractFieldBits_sound (s₀ : MirState)
    (extract : SymVal → MirTy → Option (Nat × SymNat))
    (cExtract : MirVal → MirTy → Option (Nat × Nat))
    (hext : ∀ v ty sz bits,
      extract v ty = some (sz, bits) →
      cExtract (v.denote s₀) ty = some (sz, bits.denote s₀)) :
    ∀ (fields : List FieldDecl) (v : SymVal) {outSz : Nat} {outBits : SymNat},
      symExtractFieldBits extract fields v = some (outSz, outBits) →
      extractFieldBits cExtract fields (v.denote s₀) =
        some (outSz, outBits.denote s₀)
  | [], v, _, _, h => by
    cases v <;> try (cases h; done)
    injection h with hp; injection hp with h1 h2; subst h1; subst h2; rfl
  | [f], v, outSz, outBits, h => by
    cases v <;> try (cases h; done)
    all_goals exact hext _ f.ty outSz outBits h
  | f1 :: f2 :: rest, v, outSz, outBits, h => by
    cases v <;> try (cases h; done)
    case fieldCons vh vt =>
      dsimp [symExtractFieldBits] at h
      dsimp [SymVal.denote, extractFieldBits]
      cases he1 : extract vh f1.ty with
      | none => rw [he1] at h; cases h
      | some p1 =>
        rcases p1 with ⟨sz1, bits1⟩
        rw [he1] at h
        dsimp [Option.bind] at h
        rw [hext vh f1.ty sz1 bits1 he1]
        dsimp [Option.bind]
        cases he2 : symExtractFieldBits extract (f2 :: rest) vt with
        | none => rw [he2] at h; cases h
        | some p2 =>
          rcases p2 with ⟨sz2, bits2⟩
          rw [he2] at h
          injection h with hp; injection hp with hsz hbits; subst hsz; subst hbits
          rw [symExtractFieldBits_sound s₀ extract cExtract hext (f2 :: rest)
                vt he2]
          rfl

/-- Symbolic `extractTransmuteBitsFuel`. -/
def symExtractTransmuteBitsFuel (adts : List AdtDecl) (pc : PathCond) :
    Nat → SymVal → MirTy → Option (Nat × SymNat)
  | 0, _, _ => none
  | _ + 1, .usize bits, ty =>
    match primitiveByteSize defaultTargetLayout ty with
    | some sz => some (sz, bits)
    | none => some (8, bits)
  | _ + 1, .bool b, _ =>
    match evalSymBool pc b with
    | .val b' => some (1, .const (if b' then 1 else 0))
    | _ => none
  | _ + 1, .unit, _ => some (0, .const 0)
  | _ + 1, .bytes sz bits, .array (.uint w) _ =>
    if w == 8 then
      match evalSymNatUnder pc sz with
      | .const csz => some (csz, bits)
      | _ => none
    else
      none
  | _ + 1, .bytes sz bits, .arraySizeOf (.uint w) _ =>
    if w == 8 then
      match evalSymNatUnder pc sz with
      | .const csz => some (csz, bits)
      | _ => none
    else
      none
  | fuel + 1, .adt adtId inner, _ =>
    (findAdtDecl adts adtId).bind fun decl =>
      if decl.repr == .unmodeled then
        none
      else
        symExtractFieldBits (symExtractTransmuteBitsFuel adts pc fuel)
          decl.fields inner
  | _, _, _ => none

theorem symExtractTransmuteBitsFuel_sound {rootLC : Nat} {s₀ : MirState}
    {pc : PathCond} (hmatch : pc.Matches rootLC s₀) (adts : List AdtDecl) :
    ∀ (fuel : Nat) (v : SymVal) (ty : MirTy) {outSz : Nat} {outBits : SymNat},
      symExtractTransmuteBitsFuel adts pc fuel v ty = some (outSz, outBits) →
      extractTransmuteBitsFuel adts fuel (v.denote s₀) ty =
        some (outSz, outBits.denote s₀)
  | 0, _, _, _, _, h => by cases h
  | _ + 1, .usize bits, ty, _, _, h => by
    dsimp [symExtractTransmuteBitsFuel, extractTransmuteBitsFuel,
           SymVal.denote] at h ⊢
    cases hp : primitiveByteSize defaultTargetLayout ty with
    | none =>
      rw [hp] at h
      injection h with hpair; injection hpair with h1 h2; subst h1; subst h2; rfl
    | some sz =>
      rw [hp] at h
      injection h with hpair; injection hpair with h1 h2; subst h1; subst h2; rfl
  | _ + 1, .bool b, ty, _, _, h => by
    dsimp [symExtractTransmuteBitsFuel] at h
    cases hb : evalSymBool pc b with
    | needSplit _ => rw [hb] at h; cases h
    | unknown => rw [hb] at h; cases h
    | val b' =>
      rw [hb] at h
      injection h with hpair; injection hpair with h1 h2; subst h1; subst h2
      dsimp [SymVal.denote, extractTransmuteBitsFuel, SymNat.denote]
      rw [evalSymBool_sound hmatch b hb]
  | _ + 1, .unit, _, _, _, h => by
    injection h with hpair; injection hpair with h1 h2; subst h1; subst h2; rfl
  | _ + 1, .bytes sz bits, ty, _, _, h => by
    cases ty <;> try (cases h; done)
    case array elem len =>
      cases elem <;> try (cases h; done)
      case uint w =>
        dsimp [symExtractTransmuteBitsFuel, extractTransmuteBitsFuel,
               SymVal.denote] at h ⊢
        cases hw : (w == 8) with
        | false => rw [hw] at h; cases h
        | true =>
          rw [hw] at h
          dsimp at h ⊢
          cases hsz : evalSymNatUnder pc sz <;>
            try (rw [hsz] at h; cases h; done)
          case const csz =>
            rw [hsz] at h
            injection h with hpair; injection hpair with h1 h2; subst h1; subst h2
            have hsz' : sz.denote s₀ = csz := by
              rw [← evalSymNatUnder_sound hmatch sz, hsz]; rfl
            rw [hsz']
    case arraySizeOf elem sizedTy =>
      cases elem <;> try (cases h; done)
      case uint w =>
        dsimp [symExtractTransmuteBitsFuel, extractTransmuteBitsFuel,
               SymVal.denote] at h ⊢
        cases hw : (w == 8) with
        | false => rw [hw] at h; cases h
        | true =>
          rw [hw] at h
          dsimp at h ⊢
          cases hsz : evalSymNatUnder pc sz <;>
            try (rw [hsz] at h; cases h; done)
          case const csz =>
            rw [hsz] at h
            injection h with hpair; injection hpair with h1 h2; subst h1; subst h2
            have hsz' : sz.denote s₀ = csz := by
              rw [← evalSymNatUnder_sound hmatch sz, hsz]; rfl
            rw [hsz']
  | fuel + 1, .adt adtId inner, ty, _, _, h => by
    dsimp [symExtractTransmuteBitsFuel, extractTransmuteBitsFuel,
           SymVal.denote] at h ⊢
    cases hfind : findAdtDecl adts adtId with
    | none => rw [hfind] at h; cases h
    | some decl =>
      rw [hfind] at h
      dsimp [Option.bind] at h ⊢
      cases hrepr : (decl.repr == .unmodeled) with
      | true => rw [hrepr] at h; cases h
      | false =>
        rw [hrepr] at h
        dsimp at h ⊢
        exact symExtractFieldBits_sound s₀
          (symExtractTransmuteBitsFuel adts pc fuel)
          (extractTransmuteBitsFuel adts fuel)
          (fun v' ty' s' b' he =>
            symExtractTransmuteBitsFuel_sound hmatch adts fuel v' ty' he)
          decl.fields inner h
  | _ + 1, .uninit, _, _, _, h => by cases h
  | _ + 1, .fieldCons _ _, _, _, _, h => by cases h
  | _ + 1, .ref _ _ _ _, _, _, _, h => by cases h
  | _ + 1, .callerRef _ _, _, _, _, h => by cases h

def symExtractTransmuteBits (adts : List AdtDecl) (pc : PathCond)
    (v : SymVal) (srcTy : MirTy := .unmodeled) : Option (Nat × SymNat) :=
  symExtractTransmuteBitsFuel adts pc (adts.length + 1) v srcTy

theorem symExtractTransmuteBits_sound {rootLC : Nat} {s₀ : MirState}
    {pc : PathCond} (hmatch : pc.Matches rootLC s₀) (adts : List AdtDecl)
    (v : SymVal) (srcTy : MirTy) {outSz : Nat} {outBits : SymNat}
    (h : symExtractTransmuteBits adts pc v srcTy = some (outSz, outBits)) :
    extractTransmuteBits adts (v.denote s₀) srcTy =
      some (outSz, outBits.denote s₀) :=
  symExtractTransmuteBitsFuel_sound hmatch adts (adts.length + 1) v srcTy h

/-- Symbolic `constructFieldVals`. -/
def symConstructFieldVals (construct : Nat → MirTy → Option SymVal) :
    List FieldDecl → Option (Nat × List SymVal)
  | [] => some (0, [])
  | f :: rest =>
    (primitiveByteSize defaultTargetLayout f.ty).bind fun fSz =>
      (construct fSz f.ty).bind fun v =>
        (symConstructFieldVals construct rest).map
          fun (restSz, vs) => (fSz + restSz, v :: vs)

theorem symConstructFieldVals_sound (s₀ : MirState)
    (construct : Nat → MirTy → Option SymVal)
    (cConstruct : Nat → MirTy → Option MirVal)
    (hcon : ∀ fSz ty sv,
      construct fSz ty = some sv →
      cConstruct fSz ty = some (sv.denote s₀)) :
    ∀ (fields : List FieldDecl) (bits : Nat)
      {outSz : Nat} {outVs : List SymVal},
      symConstructFieldVals construct fields = some (outSz, outVs) →
      constructFieldVals cConstruct bits fields =
        some (outSz, outVs.map (SymVal.denote s₀))
  | [], _, _, _, h => by
    injection h with hp; injection hp with h1 h2; subst h1; subst h2; rfl
  | f :: rest, bits, outSz, outVs, h => by
    dsimp [symConstructFieldVals, constructFieldVals] at h ⊢
    cases hpsz : primitiveByteSize defaultTargetLayout f.ty with
    | none => rw [hpsz] at h; cases h
    | some fSz =>
      rw [hpsz] at h
      dsimp [Option.bind] at h ⊢
      cases hc1 : construct fSz f.ty with
      | none => rw [hc1] at h; cases h
      | some v =>
        rw [hc1] at h
        dsimp [Option.bind] at h
        rw [hcon fSz f.ty v hc1]
        dsimp [Option.bind]
        cases hrest : symConstructFieldVals construct rest with
        | none => rw [hrest] at h; cases h
        | some pr =>
          rcases pr with ⟨restSz, vs⟩
          rw [hrest] at h
          injection h with hp; injection hp with hsz hvs; subst hsz; subst hvs
          have ih :=
            symConstructFieldVals_sound s₀ construct cConstruct hcon rest
              (Nat.div bits (Nat.pow 2 (8 * fSz))) hrest
          exact congrArg
            (Option.map fun (restSz, vs) => (fSz + restSz, v.denote s₀ :: vs))
            ih

/-- Symbolic `constructTransmuteVal`. -/
def symConstructTransmuteVal (adts : List AdtDecl)
    (dstSz : Nat) (bits : SymNat) : Nat → MirTy → Option SymVal
  | 0, _ => none
  | _ + 1, .usize | _ + 1, .isize =>
    if dstSz == 8 then some (.usize bits) else none
  | _ + 1, .uint w | _ + 1, .int w =>
    match intBitWidthLayout defaultTargetLayout w with
    | some (sz, _) => if dstSz == sz then some (.usize bits) else none
    | none => none
  | _ + 1, .bool | _ + 1, .char => none
  | _ + 1, .unit => if dstSz == 0 then some .unit else none
  | _ + 1, .array (.uint w) len =>
    if w == 8 && dstSz == len then some (.bytes (.const dstSz) bits) else none
  | _ + 1, .arraySizeOf (.uint w) _ =>
    if w == 8 then some (.bytes (.const dstSz) bits) else none
  | fuel + 1, .adt id =>
    (findAdtDecl adts id).bind fun decl =>
      if decl.allFieldsPubSafe && decl.repr != .unmodeled then
        match decl.fields with
        | [f] =>
          (symConstructTransmuteVal adts dstSz bits fuel f.ty).map
            (SymVal.adt id)
        | fields =>
          (symConstructFieldVals
            (fun fSz fTy => symConstructTransmuteVal adts fSz bits fuel fTy)
            fields).bind fun (sumSz, vs) =>
              if sumSz == dstSz then
                some (.adt id (symPackFields vs))
              else
                none
      else
        none
  | _ + 1, _ => none

theorem symConstructTransmuteVal_sound (s₀ : MirState)
    (adts : List AdtDecl) (bits : SymNat) :
    ∀ (fuel dstSz : Nat) (ty : MirTy) {outVal : SymVal},
      symConstructTransmuteVal adts dstSz bits fuel ty = some outVal →
      constructTransmuteVal adts dstSz (bits.denote s₀) fuel ty =
        some (outVal.denote s₀)
  | 0, _, _, _, h => by cases h
  | _ + 1, dstSz, .usize, _, h => by
    dsimp [symConstructTransmuteVal, constructTransmuteVal] at h ⊢
    cases heq : (dstSz == 8) with
    | false => rw [heq] at h; cases h
    | true => rw [heq] at h; injection h with hout; subst hout; rfl
  | _ + 1, dstSz, .isize, _, h => by
    dsimp [symConstructTransmuteVal, constructTransmuteVal] at h ⊢
    cases heq : (dstSz == 8) with
    | false => rw [heq] at h; cases h
    | true => rw [heq] at h; injection h with hout; subst hout; rfl
  | _ + 1, dstSz, .uint w, _, h => by
    dsimp [symConstructTransmuteVal, constructTransmuteVal] at h ⊢
    cases hl : intBitWidthLayout defaultTargetLayout w with
    | none => rw [hl] at h; cases h
    | some p =>
      rcases p with ⟨sz, align⟩
      rw [hl] at h
      dsimp at h ⊢
      cases heq : (dstSz == sz) with
      | false => rw [heq] at h; cases h
      | true => rw [heq] at h; injection h with hout; subst hout; rfl
  | _ + 1, dstSz, .int w, _, h => by
    dsimp [symConstructTransmuteVal, constructTransmuteVal] at h ⊢
    cases hl : intBitWidthLayout defaultTargetLayout w with
    | none => rw [hl] at h; cases h
    | some p =>
      rcases p with ⟨sz, align⟩
      rw [hl] at h
      dsimp at h ⊢
      cases heq : (dstSz == sz) with
      | false => rw [heq] at h; cases h
      | true => rw [heq] at h; injection h with hout; subst hout; rfl
  | _ + 1, _, .bool, _, h => by cases h
  | _ + 1, _, .char, _, h => by cases h
  | _ + 1, dstSz, .unit, _, h => by
    dsimp [symConstructTransmuteVal, constructTransmuteVal] at h ⊢
    cases heq : (dstSz == 0) with
    | false => rw [heq] at h; cases h
    | true => rw [heq] at h; injection h with hout; subst hout; rfl
  | _ + 1, dstSz, .array elem len, _, h => by
    cases elem <;> try (cases h; done)
    case uint w =>
      dsimp [symConstructTransmuteVal, constructTransmuteVal] at h ⊢
      cases hc : (w == 8 && dstSz == len) with
      | false => rw [hc] at h; cases h
      | true => rw [hc] at h; injection h with hout; subst hout; rfl
  | _ + 1, dstSz, .arraySizeOf elem sizedTy, _, h => by
    cases elem <;> try (cases h; done)
    case uint w =>
      dsimp [symConstructTransmuteVal, constructTransmuteVal] at h ⊢
      cases hc : (w == 8) with
      | false => rw [hc] at h; cases h
      | true => rw [hc] at h; injection h with hout; subst hout; rfl
  | fuel + 1, dstSz, .adt id, outVal, h => by
    dsimp [symConstructTransmuteVal, constructTransmuteVal] at h ⊢
    cases hfind : findAdtDecl adts id with
    | none => rw [hfind] at h; cases h
    | some decl =>
      rw [hfind] at h
      dsimp [Option.bind] at h ⊢
      cases hcond : (decl.allFieldsPubSafe && decl.repr != .unmodeled) with
      | false => rw [hcond] at h; cases h
      | true =>
        rw [hcond] at h
        dsimp at h ⊢
        cases hfields : decl.fields with
        | nil =>
          rw [hfields] at h
          dsimp [symConstructFieldVals, constructFieldVals, Option.bind] at h ⊢
          cases hsz : (0 == dstSz) with
          | false => rw [hsz] at h; cases h
          | true => rw [hsz] at h; injection h with hout; subst hout; rfl
        | cons f1 rest =>
          rw [hfields] at h
          cases rest with
          | nil =>
            dsimp at h ⊢
            cases hc : symConstructTransmuteVal adts dstSz bits fuel f1.ty with
            | none => rw [hc] at h; cases h
            | some inner =>
              rw [hc] at h
              injection h with hout; subst hout
              rw [symConstructTransmuteVal_sound s₀ adts bits fuel dstSz f1.ty hc]
              rfl
          | cons f2 rest' =>
            dsimp at h ⊢
            cases hcf :
                symConstructFieldVals
                  (fun fSz fTy => symConstructTransmuteVal adts fSz bits fuel fTy)
                  (f1 :: f2 :: rest') with
            | none => rw [hcf] at h; cases h
            | some p =>
              rcases p with ⟨sumSz, vs⟩
              rw [hcf] at h
              dsimp [Option.bind] at h
              rw [symConstructFieldVals_sound s₀
                    (fun fSz fTy => symConstructTransmuteVal adts fSz bits fuel fTy)
                    (fun fSz fTy =>
                      constructTransmuteVal adts fSz (bits.denote s₀) fuel fTy)
                    (fun fSz fTy sv h1 =>
                      symConstructTransmuteVal_sound s₀ adts bits fuel fSz fTy h1)
                    (f1 :: f2 :: rest') (bits.denote s₀) hcf]
              dsimp [Option.bind]
              cases hsz : (sumSz == dstSz) with
              | false => rw [hsz] at h; cases h
              | true =>
                rw [hsz] at h
                injection h with hout; subst hout
                simp [SymVal.denote, symPackFields_denote]
  | _ + 1, _, .param _, _, h => by cases h
  | _ + 1, _, .ref _, _, h => by cases h
  | _ + 1, _, .rawPtr _ _, _, h => by cases h
  | _ + 1, _, .float _, _, h => by cases h
  | _ + 1, _, .str, _, h => by cases h
  | _ + 1, _, .never, _, h => by cases h
  | _ + 1, _, .refMut _, _, h => by cases h
  | _ + 1, _, .slice _, _, h => by cases h
  | _ + 1, _, .tuple _, _, h => by cases h
  | _ + 1, _, .fnDef _, _, h => by cases h
  | _ + 1, _, .fnPtr, _, h => by cases h
  | _ + 1, _, .unmodeled, _, h => by cases h

/-- Bit-pattern fallback for `symEvalTransmuteVal`. -/
def symEvalTransmuteBitsFallback (adts : List AdtDecl) (pc : PathCond)
    (srcTy dstTy : MirTy) (srcVal : SymVal) (srcSz dstSz : SymNat)
    (fuel : Nat) : SymEvalRes SymVal :=
  match symExtractTransmuteBits adts pc srcVal srcTy,
        evalSymNatUnder pc srcSz,
        evalSymNatUnder pc dstSz with
  | some (vSz, bits), .const cSrcSz, .const cDstSz =>
    if decide (vSz = cSrcSz) then
      match symConstructTransmuteVal adts cDstSz bits fuel dstTy with
      | some constructed => .val constructed
      | none => .unknown
    else
      .unknown
  | _, _, _ => .unknown

theorem symEvalTransmuteBitsFallback_sound {rootLC : Nat} {s₀ : MirState}
    {pc : PathCond} (hmatch : pc.Matches rootLC s₀) (adts : List AdtDecl)
    (srcTy dstTy : MirTy) (srcVal : SymVal) (srcSz dstSz : SymNat)
    (fuel : Nat) {outVal : SymVal}
    (h : symEvalTransmuteBitsFallback adts pc srcTy dstTy srcVal srcSz dstSz
           fuel = .val outVal) :
    (match extractTransmuteBits adts (srcVal.denote s₀) srcTy with
     | some (vSz, bits) =>
       if decide (vSz = srcSz.denote s₀) then
         constructTransmuteVal adts (dstSz.denote s₀) bits fuel dstTy
       else
         none
     | none => none) = some (outVal.denote s₀) := by
  unfold symEvalTransmuteBitsFallback at h
  cases hex : symExtractTransmuteBits adts pc srcVal srcTy with
  | none => rw [hex] at h; cases h
  | some p =>
    rcases p with ⟨vSz, bits⟩
    rw [hex] at h
    cases hs : evalSymNatUnder pc srcSz <;>
      try (rw [hs] at h; cases h; done)
    case const cSrcSz =>
      rw [hs] at h
      cases hd : evalSymNatUnder pc dstSz <;>
        try (rw [hd] at h; cases h; done)
      case const cDstSz =>
        rw [hd] at h
        dsimp at h
        rw [symExtractTransmuteBits_sound hmatch adts srcVal srcTy hex]
        have hsrc : srcSz.denote s₀ = cSrcSz := by
          rw [← evalSymNatUnder_sound hmatch srcSz, hs]; rfl
        have hdst : dstSz.denote s₀ = cDstSz := by
          rw [← evalSymNatUnder_sound hmatch dstSz, hd]; rfl
        rw [hsrc, hdst]
        dsimp
        cases hdec : decide (vSz = cSrcSz) with
        | false => rw [hdec] at h; cases h
        | true =>
          rw [hdec] at h
          dsimp at h
          cases hc : symConstructTransmuteVal adts cDstSz bits fuel dstTy with
          | none => rw [hc] at h; cases h
          | some constructed =>
            rw [hc] at h
            injection h with hout; subst hout
            exact symConstructTransmuteVal_sound s₀ adts bits fuel cDstSz
              dstTy hc

/-- Symbolic `evalTransmuteVal` under `pc`. -/
def symEvalTransmuteVal (adts : List AdtDecl) (pc : PathCond)
    (srcTy dstTy : MirTy) (srcVal : SymVal)
    (target : TargetLayout := defaultTargetLayout) : SymEvalRes SymVal :=
  if !srcVal.isFullyInit then
    .unknown
  else
    match symEvalTyByteSize adts srcTy target,
          symEvalTyByteSize adts dstTy target with
    | some srcSz, some dstSz =>
      match evalSymNatEq pc srcSz dstSz with
      | .needSplit sp => .needSplit sp
      | .unknown => .unknown
      | .val false => .unknown
      | .val true =>
        let fuel := adts.length + 1
        match symPeelTransparent adts pc fuel srcTy srcVal with
        | .needSplit sp => .needSplit sp
        | .unknown => .unknown
        | .val peeledOpt =>
          match peeledOpt with
          | none =>
            symEvalTransmuteBitsFallback adts pc srcTy dstTy srcVal srcSz dstSz
              fuel
          | some (baseTy, baseVal) =>
            match symWrapTransparent adts pc fuel baseTy dstTy baseVal with
            | .needSplit sp => .needSplit sp
            | .unknown => .unknown
            | .val (some wrapped) => .val wrapped
            | .val none =>
              symEvalTransmuteBitsFallback adts pc srcTy dstTy srcVal srcSz
                dstSz fuel
    | _, _ => .unknown

theorem symEvalTransmuteVal_sound {rootLC : Nat} {s₀ : MirState}
    {pc : PathCond} (hmatch : pc.Matches rootLC s₀) (adts : List AdtDecl)
    (s : MirState) (hty : s.tySizes = s₀.tySizes) (hpad : s.adtPad = s₀.adtPad)
    (srcTy dstTy : MirTy) (srcVal : SymVal) (target : TargetLayout)
    {outVal : SymVal}
    (h : symEvalTransmuteVal adts pc srcTy dstTy srcVal target = .val outVal) :
    evalTransmuteVal adts s srcTy dstTy (srcVal.denote s₀) target =
      some (outVal.denote s₀) := by
  unfold symEvalTransmuteVal at h
  unfold evalTransmuteVal
  rw [SymVal.isFullyInit_denote s₀ srcVal, hty, hpad]
  cases hinit : (!srcVal.isFullyInit) with
  | true => rw [hinit] at h; cases h
  | false =>
    rw [hinit] at h
    dsimp at h ⊢
    cases hsrc : symEvalTyByteSize adts srcTy target with
    | none => rw [hsrc] at h; cases h
    | some srcSz =>
      rw [hsrc] at h
      cases hdst : symEvalTyByteSize adts dstTy target with
      | none => rw [hdst] at h; cases h
      | some dstSz =>
        rw [hdst] at h
        dsimp at h
        rw [symEvalTyByteSize_sound s₀ adts srcTy target hsrc,
            symEvalTyByteSize_sound s₀ adts dstTy target hdst]
        dsimp
        cases heq : evalSymNatEq pc srcSz dstSz with
        | needSplit _ => rw [heq] at h; cases h
        | unknown => rw [heq] at h; cases h
        | val b =>
          rw [heq] at h
          cases b with
          | false => dsimp at h; cases h
          | true =>
            dsimp at h
            have hbeq := evalSymNatEq_sound hmatch srcSz dstSz heq
            have hsz_eq : srcSz.denote s₀ = dstSz.denote s₀ :=
              beq_iff_eq.mp hbeq
            rw [decide_eq_true hsz_eq]
            dsimp
            cases hp :
                symPeelTransparent adts pc (adts.length + 1) srcTy srcVal with
            | needSplit _ => rw [hp] at h; cases h
            | unknown => rw [hp] at h; cases h
            | val peeledOpt =>
              rw [hp] at h
              dsimp at h
              rw [symPeelTransparent_sound hmatch adts (adts.length + 1) srcTy
                    srcVal hp]
              cases peeledOpt with
              | none =>
                dsimp [Option.bind] at h ⊢
                exact symEvalTransmuteBitsFallback_sound hmatch adts srcTy
                  dstTy srcVal srcSz dstSz (adts.length + 1) h
              | some bp =>
                rcases bp with ⟨baseTy, baseVal⟩
                dsimp [Option.bind] at h ⊢
                cases hw :
                    symWrapTransparent adts pc (adts.length + 1) baseTy dstTy
                      baseVal with
                | needSplit _ => rw [hw] at h; cases h
                | unknown => rw [hw] at h; cases h
                | val wopt =>
                  rw [hw] at h
                  rw [symWrapTransparent_sound hmatch adts (adts.length + 1)
                        baseTy dstTy baseVal hw]
                  cases wopt with
                  | some wrapped =>
                    dsimp at h ⊢
                    injection h with hout; subst hout
                    rfl
                  | none =>
                    dsimp at h ⊢
                    exact symEvalTransmuteBitsFallback_sound hmatch adts srcTy
                      dstTy srcVal srcSz dstSz (adts.length + 1) h

/-- Symbolic `evalTransmuteCopy` in state `st`. -/
def symEvalTransmuteCopy (rootLC : Nat) (adts : List AdtDecl) (st : SymState)
    (srcTy dstTy : MirTy) (argVal : SymVal)
    (target : TargetLayout := defaultTargetLayout) : SymEvalRes SymVal :=
  match argVal with
  | .ref frameId gen loc fieldDepth =>
    match symResolveFrameRef rootLC st frameId gen loc fieldDepth with
    | some pointee =>
      symEvalTransmuteVal adts st.pc srcTy dstTy pointee target
    | none => .unknown
  | .callerRef vid extraDepth =>
    match symResolveCallerRef st vid extraDepth with
    | some pointee =>
      symEvalTransmuteVal adts st.pc srcTy dstTy pointee target
    | none => .unknown
  | _ => .unknown

theorem symEvalTransmuteCopy_sound {rootLC : Nat} {s₀ : MirState}
    {st : SymState} (hmatch : st.pc.Matches rootLC s₀) (adts : List AdtDecl)
    (srcTy dstTy : MirTy) (argVal : SymVal) (target : TargetLayout)
    {outVal : SymVal}
    (h : symEvalTransmuteCopy rootLC adts st srcTy dstTy argVal target =
           .val outVal) :
    evalTransmuteCopy adts (st.toMirState rootLC s₀) srcTy dstTy
      (argVal.denote s₀) target = some (outVal.denote s₀) := by
  cases argVal <;> try (cases h; done)
  case ref frameId gen loc fieldDepth =>
    dsimp [symEvalTransmuteCopy] at h
    dsimp [SymVal.denote, evalTransmuteCopy]
    cases hr : symResolveFrameRef rootLC st frameId gen loc fieldDepth with
    | none => rw [hr] at h; cases h
    | some pointee =>
      rw [hr] at h
      dsimp at h
      rw [symResolveFrameRef_sound rootLC s₀ st frameId gen loc fieldDepth hr]
      dsimp
      exact symEvalTransmuteVal_sound hmatch adts (st.toMirState rootLC s₀)
        rfl rfl srcTy dstTy pointee target h
  case callerRef vid extraDepth =>
    dsimp [symEvalTransmuteCopy] at h
    dsimp [SymVal.denote, evalTransmuteCopy]
    cases hr : symResolveCallerRef st vid extraDepth with
    | none => rw [hr] at h; cases h
    | some pointee =>
      rw [hr] at h
      dsimp at h
      rw [(symResolveCallerRef_sound hmatch vid extraDepth hr).1]
      dsimp
      exact symEvalTransmuteVal_sound hmatch adts (st.toMirState rootLC s₀)
        rfl rfl srcTy dstTy pointee target h

/-- Symbolic `returnRefsStep`. -/
def symReturnRefsStep (rootLC : Nat) (st : SymState) (localCount : Nat)
    (follow : SymVal → Bool) : SymVal → Bool
  | .uninit => false
  | .usize _ | .bool _ | .unit | .bytes _ _ => true
  | .adt _ inner => symReturnRefsStep rootLC st localCount follow inner
  | .fieldCons h t =>
    symReturnRefsStep rootLC st localCount follow h &&
    symReturnRefsStep rootLC st localCount follow t
  | .ref frameId gen loc fieldDepth =>
    !(if st.frameId == 0 then
        decide (0 < frameId) || decide (loc.index < localCount)
      else
        decide (st.frameId ≤ frameId)) &&
    (symResolveFrameRef rootLC st frameId gen loc fieldDepth).any follow
  | .callerRef vid extraDepth =>
    (if st.frameId == 0 then decide (localCount ≤ rootLC) else true) &&
    (symResolveCallerRef st vid extraDepth).any follow

def symReturnRefsFuel (rootLC : Nat) (st : SymState) (localCount : Nat) :
    Nat → SymVal → Bool
  | 0 => fun _ => false
  | fuel + 1 =>
    symReturnRefsStep rootLC st localCount
      (symReturnRefsFuel rootLC st localCount fuel)

def symReturnRefsOk (rootLC : Nat) (st : SymState) (localCount : Nat)
    (v : SymVal) : Bool :=
  symReturnRefsFuel rootLC st localCount 5 v

theorem symReturnRefsStep_sound {rootLC : Nat} {s₀ : MirState} {st : SymState}
    (hmatch : st.pc.Matches rootLC s₀) (localCount : Nat)
    (follow : SymVal → Bool) (cFollow : MirVal → Bool)
    (hfol : ∀ sv, follow sv = true → cFollow (sv.denote s₀) = true) :
    ∀ (v : SymVal),
      symReturnRefsStep rootLC st localCount follow v = true →
      returnRefsStep (st.toMirState rootLC s₀) localCount cFollow
        (v.denote s₀) = true
  | .uninit, h => by cases h
  | .usize _, _ => rfl
  | .bool _, _ => rfl
  | .unit, _ => rfl
  | .bytes _ _, _ => rfl
  | .adt _ inner, h =>
    symReturnRefsStep_sound hmatch localCount follow cFollow hfol inner h
  | .fieldCons vh vt, h => by
    dsimp [symReturnRefsStep] at h
    rcases Bool.and_eq_true_iff.mp h with ⟨h1, h2⟩
    dsimp [SymVal.denote, returnRefsStep]
    rw [symReturnRefsStep_sound hmatch localCount follow cFollow hfol vh h1,
        symReturnRefsStep_sound hmatch localCount follow cFollow hfol vt h2]
    rfl
  | .ref frameId gen loc fieldDepth, h => by
    dsimp [symReturnRefsStep] at h
    rcases Bool.and_eq_true_iff.mp h with ⟨hcond, hany⟩
    dsimp [SymVal.denote, returnRefsStep]
    have hfid : (st.toMirState rootLC s₀).frameId = st.frameId := rfl
    rw [hfid, hcond, Bool.true_and]
    cases hr : symResolveFrameRef rootLC st frameId gen loc fieldDepth with
    | none => rw [hr] at hany; cases hany
    | some pv =>
      rw [hr] at hany
      dsimp [Option.any] at hany
      rw [symResolveFrameRef_sound rootLC s₀ st frameId gen loc fieldDepth hr]
      dsimp [Option.any]
      exact hfol pv hany
  | .callerRef vid extraDepth, h => by
    dsimp [symReturnRefsStep] at h
    rcases Bool.and_eq_true_iff.mp h with ⟨hcond, hany⟩
    cases hr : symResolveCallerRef st vid extraDepth with
    | none => rw [hr] at hany; cases hany
    | some pv =>
      rw [hr] at hany
      dsimp [Option.any] at hany
      rcases symResolveCallerRef_sound hmatch vid extraDepth hr with
        ⟨hres, href_ge⟩
      dsimp [SymVal.denote, returnRefsStep]
      rw [hres]
      dsimp [Option.any]
      rw [hfol pv hany, Bool.and_true]
      have hfid_to : (st.toMirState rootLC s₀).frameId = st.frameId := rfl
      rw [hfid_to]
      cases hfid : (st.frameId == 0) with
      | true =>
        rw [hfid] at hcond
        have hle : localCount ≤ rootLC := of_decide_eq_true hcond
        have hlt : decide ((evalInputRef s₀ vid).1.index < localCount) = false :=
          decide_eq_false (by omega)
        rw [hlt]
        rfl
      | false =>
        have hpos : ¬ (st.frameId ≤ 0) := by
          have hne : st.frameId ≠ 0 := beq_eq_false_iff_ne.mp hfid
          omega
        rw [decide_eq_false hpos]
        rfl

theorem symReturnRefsFuel_sound {rootLC : Nat} {s₀ : MirState} {st : SymState}
    (hmatch : st.pc.Matches rootLC s₀) (localCount : Nat) :
    ∀ (fuel : Nat) (v : SymVal),
      symReturnRefsFuel rootLC st localCount fuel v = true →
      returnRefsFuel (st.toMirState rootLC s₀) localCount fuel
        (v.denote s₀) = true
  | 0, _, h => by cases h
  | fuel + 1, v, h =>
    symReturnRefsStep_sound hmatch localCount
      (symReturnRefsFuel rootLC st localCount fuel)
      (returnRefsFuel (st.toMirState rootLC s₀) localCount fuel)
      (fun sv hf => symReturnRefsFuel_sound hmatch localCount fuel sv hf)
      v h

theorem symReturnRefsOk_sound {rootLC : Nat} {s₀ : MirState} {st : SymState}
    (hmatch : st.pc.Matches rootLC s₀) (localCount : Nat) (v : SymVal)
    (h : symReturnRefsOk rootLC st localCount v = true) :
    (v.denote s₀).returnRefsOk (st.toMirState rootLC s₀) localCount = true :=
  symReturnRefsFuel_sound hmatch localCount 5 v h

theorem validFields_mono {u1 u2 : MirTy → MirVal → Prop}
    (hu : ∀ ty v, u1 ty v → u2 ty v) :
    ∀ (fields : List FieldDecl) (v : MirVal),
      validFields u1 fields v → validFields u2 fields v
  | [], v, h => by
    cases v <;> try exact False.elim h
    trivial
  | [f], v, h => hu f.ty v h
  | f1 :: f2 :: rest, v, h => by
    cases v <;> try exact False.elim h
    case fieldCons vh vt =>
      exact ⟨hu f1.ty vh h.1, validFields_mono hu (f2 :: rest) vt h.2⟩

theorem validAdtDecl_mono {u1 u2 : MirTy → MirVal → Prop}
    (hu : ∀ ty v, u1 ty v → u2 ty v) (decl : AdtDecl) (v : MirVal)
    (h : validAdtDecl u1 decl v) : validAdtDecl u2 decl v := by
  unfold validAdtDecl at h ⊢
  cases hrepr : decl.repr with
  | unmodeled => rw [hrepr] at h; exact False.elim h
  | rust => rw [hrepr] at h; exact validFields_mono hu decl.fields v h
  | transparent => rw [hrepr] at h; exact validFields_mono hu decl.fields v h
  | c => rw [hrepr] at h; exact validFields_mono hu decl.fields v h

theorem validStep_mono (adts : List AdtDecl) {adtInv1 adtInv2 : AdtInv}
    (hinv : ∀ id inner, adtInv1 id inner → adtInv2 id inner)
    (s : MirState) (callerBase : Nat)
    {u1 u2 : MirTy → MirVal → Prop}
    (hu : ∀ ty v, u1 ty v → u2 ty v) :
    ∀ (ty : MirTy) (v : MirVal),
      validStep adts adtInv1 s callerBase u1 ty v →
      validStep adts adtInv2 s callerBase u2 ty v
  | .usize, v, h => by cases v <;> exact h
  | .isize, v, h => by cases v <;> exact h
  | .uint _, v, h => by cases v <;> exact h
  | .int _, v, h => by cases v <;> exact h
  | .char, v, h => by cases v <;> exact h
  | .bool, v, h => by cases v <;> exact h
  | .unit, v, h => by cases v <;> exact h
  | .param _, v, h => by cases v <;> exact h
  | .array _ _, v, h => by cases v <;> exact h
  | .arraySizeOf _ _, v, h => by cases v <;> exact h
  | .float _, v, h => by cases v <;> exact h
  | .str, v, h => by cases v <;> exact h
  | .never, v, h => by cases v <;> exact h
  | .refMut _, v, h => by cases v <;> exact h
  | .slice _, v, h => by cases v <;> exact h
  | .tuple _, v, h => by cases v <;> exact h
  | .fnDef _, v, h => by cases v <;> exact h
  | .fnPtr, v, h => by cases v <;> exact h
  | .unmodeled, v, h => by cases v <;> exact h
  | .adt id, v, h => by
    cases v <;> try exact False.elim h
    case adt vId inner =>
      rcases h with ⟨hvid, hi, hdecl⟩
      refine ⟨hvid, hinv id inner hi, ?_⟩
      cases hfind : findAdtDecl adts id with
      | none => rw [hfind] at hdecl; exact False.elim hdecl
      | some decl =>
        rw [hfind] at hdecl
        exact validAdtDecl_mono hu decl inner hdecl
  | .ref inner, v, h => by
    cases v <;> try exact False.elim h
    case ref frameId gen loc fieldDepth =>
      rcases h with ⟨hf, hc, hres⟩
      refine ⟨hf, hc, ?_⟩
      cases hr : resolveRef s frameId gen loc fieldDepth with
      | none => rw [hr] at hres; exact False.elim hres
      | some pointee =>
        rw [hr] at hres
        exact validStep_mono adts hinv s callerBase hu inner pointee hres
  | .rawPtr inner _, v, h => by
    cases v <;> try exact False.elim h
    case ref frameId gen loc fieldDepth =>
      rcases h with ⟨hf, hc, hres⟩
      refine ⟨hf, hc, ?_⟩
      cases hr : resolveRef s frameId gen loc fieldDepth with
      | none => rw [hr] at hres; exact False.elim hres
      | some pointee =>
        rw [hr] at hres
        exact validStep_mono adts hinv s callerBase hu inner pointee hres

theorem validFuel_succ (adts : List AdtDecl) (adtInv : AdtInv)
    (s : MirState) (callerBase : Nat) :
    ∀ (fuel : Nat) (ty : MirTy) (v : MirVal),
      MirVal.validFuel adts adtInv s callerBase fuel ty v →
      MirVal.validFuel adts adtInv s callerBase (fuel + 1) ty v
  | 0, _, _, h => False.elim h
  | fuel + 1, ty, v, h =>
    validStep_mono adts (fun _ _ hi => hi) s callerBase
      (validFuel_succ adts adtInv s callerBase fuel) ty v h

theorem validFuel_weaken_defaultAdtInv (adts : List AdtDecl) (adtInv : AdtInv)
    (s : MirState) (callerBase : Nat) :
    ∀ (fuel : Nat) (ty : MirTy) (v : MirVal),
      MirVal.validFuel adts adtInv s callerBase fuel ty v →
      MirVal.validFuel adts defaultAdtInv s callerBase fuel ty v
  | 0, _, _, h => False.elim h
  | fuel + 1, ty, v, h =>
    validStep_mono adts (fun _ _ _ => trivial) s callerBase
      (validFuel_weaken_defaultAdtInv adts adtInv s callerBase fuel) ty v h

theorem valid_weaken_defaultAdtInv (adts : List AdtDecl) (adtInv : AdtInv)
    (s : MirState) (callerBase : Nat) (ty : MirTy) (v : MirVal)
    (h : v.valid adts adtInv s callerBase ty) :
    v.valid adts defaultAdtInv s callerBase ty :=
  validFuel_weaken_defaultAdtInv adts adtInv s callerBase (adts.length + 1)
    ty v h

/-- Symbolic check of `denoteAdtInv adts id (inner.denote s₀)` under `pc`. -/
def symCheckAdtInv (adts : List AdtDecl) (pc : PathCond)
    (id : Nat) (inner : SymVal) : Bool :=
  if adts.all (·.invariant.isNone) then
    true
  else
    match findAdtDecl adts id with
    | some { invariant := some inv, .. } =>
      match inner with
      | .usize n => decide (evalSymNatEq pc n (.const inv.ne) = .val false)
      | _ => false
    | _ => true

theorem symCheckAdtInv_sound {rootLC : Nat} {s₀ : MirState} {pc : PathCond}
    (hmatch : pc.Matches rootLC s₀) (adts : List AdtDecl)
    (id : Nat) (inner : SymVal)
    (h : symCheckAdtInv adts pc id inner = true) :
    denoteAdtInv adts id (inner.denote s₀) := by
  unfold symCheckAdtInv at h
  unfold denoteAdtInv
  cases hall : adts.all (·.invariant.isNone) with
  | true => trivial
  | false =>
    rw [hall] at h
    dsimp at h ⊢
    cases hfind : findAdtDecl adts id with
    | none => trivial
    | some decl =>
      rw [hfind] at h
      rcases decl with ⟨did, dfields, drepr, none | inv⟩
      · trivial
      · dsimp at h ⊢
        cases inner <;> try (cases h; done)
        case usize n =>
          dsimp [SymVal.denote, denoteInvariant]
          have heval : evalSymNatEq pc n (.const inv.ne) = .val false :=
            of_decide_eq_true h
          have hbeq := evalSymNatEq_sound hmatch n (.const inv.ne) heval
          exact beq_eq_false_iff_ne.mp hbeq

def symCheckValidFields (unfold : MirTy → SymVal → Bool) :
    List FieldDecl → SymVal → Bool
  | [], .unit => true
  | [], _ => false
  | [f], v => unfold f.ty v
  | f :: rest, .fieldCons h t => unfold f.ty h && symCheckValidFields unfold rest t
  | _ :: _, _ => false

theorem symCheckValidFields_sound (s₀ : MirState)
    (unfold : MirTy → SymVal → Bool)
    (cUnfold : MirTy → MirVal → Prop)
    (hunfold : ∀ ty sv, unfold ty sv = true → cUnfold ty (sv.denote s₀)) :
    ∀ (fields : List FieldDecl) (v : SymVal),
      symCheckValidFields unfold fields v = true →
      validFields cUnfold fields (v.denote s₀)
  | [], v, h => by
    cases v <;> try (cases h; done)
    trivial
  | [f], v, h => hunfold f.ty v h
  | f1 :: f2 :: rest, v, h => by
    cases v <;> try (cases h; done)
    case fieldCons vh vt =>
      dsimp [symCheckValidFields] at h
      rcases Bool.and_eq_true_iff.mp h with ⟨h1, h2⟩
      exact ⟨hunfold f1.ty vh h1,
             symCheckValidFields_sound s₀ unfold cUnfold hunfold (f2 :: rest)
               vt h2⟩

def symCheckValidAdtDecl (unfold : MirTy → SymVal → Bool) (decl : AdtDecl)
    (inner : SymVal) : Bool :=
  match decl.repr with
  | .unmodeled => false
  | .rust | .transparent | .c => symCheckValidFields unfold decl.fields inner

theorem symCheckValidAdtDecl_sound (s₀ : MirState)
    (unfold : MirTy → SymVal → Bool)
    (cUnfold : MirTy → MirVal → Prop)
    (hunfold : ∀ ty sv, unfold ty sv = true → cUnfold ty (sv.denote s₀))
    (decl : AdtDecl) (inner : SymVal)
    (h : symCheckValidAdtDecl unfold decl inner = true) :
    validAdtDecl cUnfold decl (inner.denote s₀) := by
  unfold symCheckValidAdtDecl at h
  unfold validAdtDecl
  cases hrepr : decl.repr with
  | unmodeled => rw [hrepr] at h; cases h
  | rust =>
    rw [hrepr] at h
    exact symCheckValidFields_sound s₀ unfold cUnfold hunfold decl.fields
      inner h
  | transparent =>
    rw [hrepr] at h
    exact symCheckValidFields_sound s₀ unfold cUnfold hunfold decl.fields
      inner h
  | c =>
    rw [hrepr] at h
    exact symCheckValidFields_sound s₀ unfold cUnfold hunfold decl.fields
      inner h

def symCheckValidStep (rootLC : Nat) (adts : List AdtDecl) (st : SymState)
    (unfold : MirTy → SymVal → Bool) : MirTy → SymVal → Bool
  | .usize, .usize _ => true
  | .isize, .usize _ => true
  | .uint _, .usize _ => true
  | .int _, .usize _ => true
  | .char, .usize _ => true
  | .bool, .bool _ => true
  | .unit, .unit => true
  | .adt id, .adt vId inner =>
    (vId == id) &&
    symCheckAdtInv adts st.pc id inner &&
    match findAdtDecl adts id with
    | some decl => symCheckValidAdtDecl unfold decl inner
    | none => false
  | .param idx, .bytes sz _ =>
    decide (evalSymNatEq st.pc sz (.tySize idx) = .val true)
  | .array elem len, .bytes sz _ =>
    match symEvalTyByteSize adts (.array elem len) with
    | some arrSz => decide (evalSymNatEq st.pc sz arrSz = .val true)
    | none => false
  | .arraySizeOf elem sizedTy, .bytes sz _ =>
    match symEvalTyByteSize adts (.arraySizeOf elem sizedTy) with
    | some arrSz => decide (evalSymNatEq st.pc sz arrSz = .val true)
    | none => false
  | .ref inner, .ref frameId gen loc fieldDepth =>
    (frameId == 0) &&
    decide (rootLC ≤ loc.index) &&
    match symResolveFrameRef rootLC st frameId gen loc fieldDepth with
    | some pointee => unfold inner pointee
    | none => false
  | .ref inner, .callerRef vid extraDepth =>
    match symResolveCallerRef st vid extraDepth with
    | some pointee => unfold inner pointee
    | none => false
  | .rawPtr inner _, .ref frameId gen loc fieldDepth =>
    (frameId == 0) &&
    decide (rootLC ≤ loc.index) &&
    match symResolveFrameRef rootLC st frameId gen loc fieldDepth with
    | some pointee => unfold inner pointee
    | none => false
  | .rawPtr inner _, .callerRef vid extraDepth =>
    match symResolveCallerRef st vid extraDepth with
    | some pointee => unfold inner pointee
    | none => false
  | _, _ => false

def symCheckValidFuel (rootLC : Nat) (adts : List AdtDecl) (st : SymState) :
    Nat → MirTy → SymVal → Bool
  | 0, _, _ => false
  | fuel + 1, ty, v =>
    symCheckValidStep rootLC adts st
      (symCheckValidFuel rootLC adts st fuel) ty v

def symCheckValid (rootLC : Nat) (adts : List AdtDecl) (st : SymState)
    (ty : MirTy) (v : SymVal) : Bool :=
  symCheckValidFuel rootLC adts st (adts.length + 1) ty v

theorem symCheckValidStep_sound {rootLC : Nat} {s₀ : MirState} {st : SymState}
    (hmatch : st.pc.Matches rootLC s₀) (adts : List AdtDecl)
    (unfold : MirTy → SymVal → Bool)
    (cUnfold : MirTy → MirVal → Prop)
    (hunfold : ∀ ty sv, unfold ty sv = true → cUnfold ty (sv.denote s₀))
    (href_step : ∀ ty mv,
      cUnfold ty mv →
      validStep adts (denoteAdtInv adts) (st.toMirState rootLC s₀) rootLC
        cUnfold ty mv) :
    ∀ (ty : MirTy) (v : SymVal),
      symCheckValidStep rootLC adts st unfold ty v = true →
      validStep adts (denoteAdtInv adts) (st.toMirState rootLC s₀) rootLC
        cUnfold ty (v.denote s₀)
  | .usize, v, h => by (cases v <;> try (cases h; done)); trivial
  | .isize, v, h => by (cases v <;> try (cases h; done)); trivial
  | .uint _, v, h => by (cases v <;> try (cases h; done)); trivial
  | .int _, v, h => by (cases v <;> try (cases h; done)); trivial
  | .char, v, h => by (cases v <;> try (cases h; done)); trivial
  | .bool, v, h => by (cases v <;> try (cases h; done)); trivial
  | .unit, v, h => by (cases v <;> try (cases h; done)); trivial
  | .adt id, v, h => by
    cases v <;> try (cases h; done)
    case adt vId inner =>
      dsimp [symCheckValidStep] at h
      rcases Bool.and_eq_true_iff.mp h with ⟨h12, hdecl⟩
      rcases Bool.and_eq_true_iff.mp h12 with ⟨hvid, hinv⟩
      refine ⟨beq_iff_eq.mp hvid, symCheckAdtInv_sound hmatch adts id inner hinv, ?_⟩
      cases hfind : findAdtDecl adts id with
      | none => rw [hfind] at hdecl; cases hdecl
      | some decl =>
        rw [hfind] at hdecl
        exact symCheckValidAdtDecl_sound s₀ unfold cUnfold hunfold decl
          inner hdecl
  | .param idx, v, h => by
    cases v <;> try (cases h; done)
    case bytes sz data =>
      dsimp [symCheckValidStep] at h
      have heval : evalSymNatEq st.pc sz (.tySize idx) = .val true :=
        of_decide_eq_true h
      have hbeq := evalSymNatEq_sound hmatch sz (.tySize idx) heval
      exact beq_iff_eq.mp hbeq
  | .array elem len, v, h => by
    cases v <;> try (cases h; done)
    case bytes sz data =>
      dsimp [symCheckValidStep] at h
      dsimp [SymVal.denote, validStep, SymState.toMirState]
      cases hsz : symEvalTyByteSize adts (.array elem len) with
      | none => rw [hsz] at h; cases h
      | some arrSz =>
        rw [hsz] at h
        rw [symEvalTyByteSize_sound s₀ adts (.array elem len)
              defaultTargetLayout hsz]
        have heval : evalSymNatEq st.pc sz arrSz = .val true :=
          of_decide_eq_true h
        exact beq_iff_eq.mp (evalSymNatEq_sound hmatch sz arrSz heval)
  | .arraySizeOf elem sizedTy, v, h => by
    cases v <;> try (cases h; done)
    case bytes sz data =>
      dsimp [symCheckValidStep] at h
      dsimp [SymVal.denote, validStep, SymState.toMirState]
      cases hsz : symEvalTyByteSize adts (.arraySizeOf elem sizedTy) with
      | none => rw [hsz] at h; cases h
      | some arrSz =>
        rw [hsz] at h
        rw [symEvalTyByteSize_sound s₀ adts (.arraySizeOf elem sizedTy)
              defaultTargetLayout hsz]
        have heval : evalSymNatEq st.pc sz arrSz = .val true :=
          of_decide_eq_true h
        exact beq_iff_eq.mp (evalSymNatEq_sound hmatch sz arrSz heval)
  | .ref inner, v, h => by
    cases v <;> try (cases h; done)
    case ref frameId gen loc fieldDepth =>
      dsimp [symCheckValidStep] at h
      rcases Bool.and_eq_true_iff.mp h with ⟨h12, hres⟩
      rcases Bool.and_eq_true_iff.mp h12 with ⟨hfid, hloc⟩
      refine ⟨beq_iff_eq.mp hfid, of_decide_eq_true hloc, ?_⟩
      cases hr : symResolveFrameRef rootLC st frameId gen loc fieldDepth with
      | none => rw [hr] at hres; cases hres
      | some pointee =>
        rw [hr] at hres
        rw [symResolveFrameRef_sound rootLC s₀ st frameId gen loc fieldDepth hr]
        exact href_step inner (pointee.denote s₀) (hunfold inner pointee hres)
    case callerRef vid extraDepth =>
      dsimp [symCheckValidStep] at h
      cases hr : symResolveCallerRef st vid extraDepth with
      | none => rw [hr] at h; cases h
      | some pointee =>
        rw [hr] at h
        rcases symResolveCallerRef_sound hmatch vid extraDepth hr with
          ⟨hres, hge⟩
        dsimp [SymVal.denote, validStep]
        refine ⟨rfl, hge, ?_⟩
        rw [hres]
        exact href_step inner (pointee.denote s₀) (hunfold inner pointee h)
  | .rawPtr inner m, v, h => by
    cases v <;> try (cases h; done)
    case ref frameId gen loc fieldDepth =>
      dsimp [symCheckValidStep] at h
      rcases Bool.and_eq_true_iff.mp h with ⟨h12, hres⟩
      rcases Bool.and_eq_true_iff.mp h12 with ⟨hfid, hloc⟩
      refine ⟨beq_iff_eq.mp hfid, of_decide_eq_true hloc, ?_⟩
      cases hr : symResolveFrameRef rootLC st frameId gen loc fieldDepth with
      | none => rw [hr] at hres; cases hres
      | some pointee =>
        rw [hr] at hres
        rw [symResolveFrameRef_sound rootLC s₀ st frameId gen loc fieldDepth hr]
        exact href_step inner (pointee.denote s₀) (hunfold inner pointee hres)
    case callerRef vid extraDepth =>
      dsimp [symCheckValidStep] at h
      cases hr : symResolveCallerRef st vid extraDepth with
      | none => rw [hr] at h; cases h
      | some pointee =>
        rw [hr] at h
        rcases symResolveCallerRef_sound hmatch vid extraDepth hr with
          ⟨hres, hge⟩
        dsimp [SymVal.denote, validStep]
        refine ⟨rfl, hge, ?_⟩
        rw [hres]
        exact href_step inner (pointee.denote s₀) (hunfold inner pointee h)
  | .float _, _, h => by cases h
  | .str, _, h => by cases h
  | .never, _, h => by cases h
  | .refMut _, _, h => by cases h
  | .slice _, _, h => by cases h
  | .tuple _, _, h => by cases h
  | .fnDef _, _, h => by cases h
  | .fnPtr, _, h => by cases h
  | .unmodeled, _, h => by cases h

theorem symCheckValidFuel_sound {rootLC : Nat} {s₀ : MirState} {st : SymState}
    (hmatch : st.pc.Matches rootLC s₀) (adts : List AdtDecl) :
    ∀ (fuel : Nat) (ty : MirTy) (v : SymVal),
      symCheckValidFuel rootLC adts st fuel ty v = true →
      MirVal.validFuel adts (denoteAdtInv adts) (st.toMirState rootLC s₀)
        rootLC fuel ty (v.denote s₀)
  | 0, _, _, h => by cases h
  | fuel + 1, ty, v, h =>
    symCheckValidStep_sound hmatch adts
      (symCheckValidFuel rootLC adts st fuel)
      (MirVal.validFuel adts (denoteAdtInv adts) (st.toMirState rootLC s₀)
        rootLC fuel)
      (fun t sv hf => symCheckValidFuel_sound hmatch adts fuel t sv hf)
      (fun t mv hf =>
        validFuel_succ adts (denoteAdtInv adts) (st.toMirState rootLC s₀)
          rootLC fuel t mv hf)
      ty v h

theorem symCheckValid_sound {rootLC : Nat} {s₀ : MirState} {st : SymState}
    (hmatch : st.pc.Matches rootLC s₀) (adts : List AdtDecl)
    (ty : MirTy) (v : SymVal)
    (h : symCheckValid rootLC adts st ty v = true) :
    (v.denote s₀).valid adts (denoteAdtInv adts) (st.toMirState rootLC s₀)
      rootLC ty :=
  symCheckValidFuel_sound hmatch adts (adts.length + 1) ty v h

/-- Decide equality of two `SymVal`s under `pc`. -/
def symValEqUnder (pc : PathCond) : SymVal → SymVal → Bool
  | .uninit, .uninit => true
  | .usize a, .usize b => decide (evalSymNatEq pc a b = .val true)
  | .bool a, .bool b => decide (a = b)
  | .unit, .unit => true
  | .adt id1 v1, .adt id2 v2 => (id1 == id2) && symValEqUnder pc v1 v2
  | .fieldCons h1 t1, .fieldCons h2 t2 =>
    symValEqUnder pc h1 h2 && symValEqUnder pc t1 t2
  | .bytes sz1 d1, .bytes sz2 d2 =>
    decide (evalSymNatEq pc sz1 sz2 = .val true) &&
    decide (evalSymNatEq pc d1 d2 = .val true)
  | .ref f1 g1 l1 d1, .ref f2 g2 l2 d2 =>
    (f1 == f2) && (g1 == g2) && decide (l1 = l2) && (d1 == d2)
  | .callerRef v1 d1, .callerRef v2 d2 =>
    decide (v1 = v2) && (d1 == d2)
  | _, _ => false

theorem symValEqUnder_sound {rootLC : Nat} {s₀ : MirState} {pc : PathCond}
    (hmatch : pc.Matches rootLC s₀) :
    ∀ (v1 v2 : SymVal),
      symValEqUnder pc v1 v2 = true →
      v1.denote s₀ = v2.denote s₀
  | v1, v2, h => by
    cases v1 <;> cases v2 <;> try (cases h; done)
    case uninit.uninit => rfl
    case usize.usize a b =>
      have heval : evalSymNatEq pc a b = .val true := of_decide_eq_true h
      exact congrArg MirVal.usize
        (beq_iff_eq.mp (evalSymNatEq_sound hmatch a b heval))
    case bool.bool a b =>
      rw [of_decide_eq_true h]
    case unit.unit => rfl
    case adt.adt id1 v1 id2 v2 =>
      dsimp [symValEqUnder] at h
      rcases Bool.and_eq_true_iff.mp h with ⟨hid, hv⟩
      dsimp [SymVal.denote]
      rw [beq_iff_eq.mp hid, symValEqUnder_sound hmatch v1 v2 hv]
    case fieldCons.fieldCons h1 t1 h2 t2 =>
      dsimp [symValEqUnder] at h
      rcases Bool.and_eq_true_iff.mp h with ⟨hh, ht⟩
      dsimp [SymVal.denote]
      rw [symValEqUnder_sound hmatch h1 h2 hh,
          symValEqUnder_sound hmatch t1 t2 ht]
    case bytes.bytes sz1 d1 sz2 d2 =>
      dsimp [symValEqUnder] at h
      rcases Bool.and_eq_true_iff.mp h with ⟨hsz, hd⟩
      have h1 :=
        beq_iff_eq.mp (evalSymNatEq_sound hmatch sz1 sz2 (of_decide_eq_true hsz))
      have h2 :=
        beq_iff_eq.mp (evalSymNatEq_sound hmatch d1 d2 (of_decide_eq_true hd))
      dsimp [SymVal.denote]
      rw [h1, h2]
    case ref.ref f1 g1 l1 d1 f2 g2 l2 d2 =>
      dsimp [symValEqUnder] at h
      rcases Bool.and_eq_true_iff.mp h with ⟨h123, hd⟩
      rcases Bool.and_eq_true_iff.mp h123 with ⟨h12, hl⟩
      rcases Bool.and_eq_true_iff.mp h12 with ⟨hf, hg⟩
      have hl' : l1 = l2 := of_decide_eq_true hl
      dsimp [SymVal.denote]
      rw [beq_iff_eq.mp hf, beq_iff_eq.mp hg, hl', beq_iff_eq.mp hd]
    case callerRef.callerRef v1 d1 v2 d2 =>
      dsimp [symValEqUnder] at h
      rcases Bool.and_eq_true_iff.mp h with ⟨hv, hd⟩
      have hv' : v1 = v2 := of_decide_eq_true hv
      dsimp [SymVal.denote]
      rw [hv', beq_iff_eq.mp hd]

/-- Check `fn.specs` against the returned value `retVal` using `pc.initArgs`. -/
def symCheckSpecs (pc : PathCond) (specs : List PostSpec)
    (retVal : SymVal) : Bool :=
  specs.all fun
    | .ensuresEqArg argLocal =>
      match pc.initArgs.find? (fun p => decide (p.1 = argLocal)) with
      | some (_, initVal) => symValEqUnder pc initVal retVal
      | none => false

theorem symCheckSpecs_sound {rootLC : Nat} {s₀ : MirState} {pc : PathCond}
    (hmatch : pc.Matches rootLC s₀) (specs : List PostSpec) (retVal : SymVal)
    (h : symCheckSpecs pc specs retVal = true) :
    ∀ spec ∈ specs,
      match spec with
      | .ensuresEqArg argLocal =>
        s₀.locals argLocal = some (retVal.denote s₀) := by
  intro spec hmem
  have hspec := list_all_mem h hmem
  cases spec with
  | ensuresEqArg argLocal =>
    dsimp at hspec ⊢
    cases hfind : pc.initArgs.find? (fun p => decide (p.1 = argLocal)) with
    | none => rw [hfind] at hspec; cases hspec
    | some p =>
      rw [hfind] at hspec
      rcases list_find_some_mem hfind with ⟨hpmem, hpdec⟩
      rcases p with ⟨k, initVal⟩
      have hk : k = argLocal := of_decide_eq_true hpdec
      subst hk
      have hloc := hmatch.2.2.2.2.2.2.2.2 (k, initVal) hpmem
      rw [hloc]
      exact congrArg some (symValEqUnder_sound hmatch initVal retVal hspec)

/-!
## Section 5: Symbolic Small-Step Engine (`symStep`), Entry Initialization (`initSymState`), and Multi-Step Verification (`symExecBody`)
-/

/-- Result of a single symbolic step (or compile-time constant evaluation):
either a deterministic silent step, a normal return, a clean panic (`.unwind`),
an `.abort`, a compile-time error (`.compileTimeError`), a finite branch split
(`.split sp`), or `.failed`. -/
inductive SymStepOut where
  | silent (st' : SymState)
  | returned (retVal : SymVal) (stTerm : SymState)
  | unwind
  | abort
  | compileTimeError
  | split (sp : SymSplit)
  | failed

/-- Agreement between a non-splitting, non-failing `SymStepOut` and a concrete
`RawStep MirState MirReturn` in initial state `s₀`. -/
def SymStepOut.Agrees (rootLC : Nat) (s₀ : MirState) (pc : PathCond)
    (out : SymStepOut) (raw : RawStep MirState MirReturn) : Prop :=
  match out with
  | .silent st' =>
    st'.pc = pc ∧ raw = .silent (st'.toMirState rootLC s₀)
  | .returned retVal stTerm =>
    stTerm.pc = pc ∧
    raw = .terminated (.normal ⟨retVal.denote s₀, stTerm.toMirState rootLC s₀⟩)
  | .unwind =>
    raw = .terminated .unwind
  | .abort =>
    raw = .terminated .abort
  | .compileTimeError =>
    raw = .terminated .compileTimeError
  | .split _ | .failed =>
    True

/-- Advance to the next statement in the current basic block with `locals'`. -/
def SymState.nextStmt (st : SymState) (locals' : Nat → Option SymVal) :
    SymStepOut :=
  .silent { st with locals := locals', stmtIdx := st.stmtIdx + 1 }

/-- Advance to the next statement updating both `locals'` and `localGens'`. -/
def SymState.nextStmtGen (st : SymState) (locals' : Nat → Option SymVal)
    (localGens' : Nat → Nat) : SymStepOut :=
  .silent { st with
    locals := locals'
    localGens := localGens'
    stmtIdx := st.stmtIdx + 1
  }

/-- Jump to statement `0` of basic block `target` in the current frame. -/
def SymState.gotoBlock (st : SymState) (locals' : Nat → Option SymVal)
    (target : Nat) : SymStepOut :=
  .silent { st with locals := locals', block := target, stmtIdx := 0 }

/-- Symbolic `evalRepeatElem`. -/
def symEvalRepeatElem (pc : PathCond) : SymVal → Option SymNat
  | .usize bits => some bits
  | .bool b =>
    match evalSymBool pc b with
    | .val bv => some (.const (if bv then 1 else 0))
    | _ => none
  | _ => none

theorem symEvalRepeatElem_sound {rootLC : Nat} {s₀ : MirState} {pc : PathCond}
    (hmatch : pc.Matches rootLC s₀) (v : SymVal) {bits : SymNat}
    (h : symEvalRepeatElem pc v = some bits) :
    evalRepeatElem (v.denote s₀) = some (bits.denote s₀) := by
  cases v <;> try (cases h; done)
  case usize b =>
    injection h with hb; subst hb; rfl
  case bool b =>
    dsimp [symEvalRepeatElem] at h
    cases hb : evalSymBool pc b <;> try (rw [hb] at h; cases h; done)
    case val bv =>
      rw [hb] at h
      injection h with hbits; subst hbits
      dsimp [SymVal.denote, evalRepeatElem, SymNat.denote]
      rw [evalSymBool_sound hmatch b hb]

/-- Project `pc` to the layout/type-size constraints visible inside a
zero-argument compile-time constant evaluation (`constEntryState`). -/
def PathCond.forConstEval (pc : PathCond) : PathCond where
  varEq := []
  varNe := []
  boolEq := []
  adtPadZero := pc.adtPadZero
  tySizeEq := pc.tySizeEq
  tySizeNe := pc.tySizeNe
  ubChecks := some true
  callerRefs := []
  initArgs := []

theorem forConstEval_matches {rootLC : Nat} {s₀ : MirState} {pc : PathCond}
    (hmatch : pc.Matches rootLC s₀) (cLC : Nat) :
    (pc.forConstEval).Matches cLC (constEntryState s₀.tySizes s₀.adtPad) := by
  rcases hmatch with ⟨_, _, _, hpad, hteq, htne, _, _, _⟩
  refine ⟨?_, ?_, ?_, hpad, hteq, htne, rfl, ?_, ?_⟩
  · intro _ h; cases h
  · intro _ h; cases h
  · intro _ h; cases h
  · intro _ h; cases h
  · intro _ h; cases h

/-- Canonical initial `SymState` for a zero-argument compile-time constant
evaluation under `pc`. -/
def symConstEntryState (pc : PathCond) : SymState where
  locals := fun _ => none
  localGens := fun _ => 0
  block := 0
  stmtIdx := 0
  curBody := none
  stack := []
  frameId := 0
  nextFrameId := 1
  pc := pc.forConstEval

theorem symConstEntryState_toMirState (s₀ : MirState) (pc : PathCond)
    (cLC : Nat) :
    (symConstEntryState pc).toMirState cLC
      (constEntryState s₀.tySizes s₀.adtPad) =
    constEntryState s₀.tySizes s₀.adtPad := by
  unfold symConstEntryState SymState.toMirState constEntryState
  dsimp
  have hloc :
      denoteLocals
        { locals := fun _ => none, block := 0, stmtIdx := 0,
          tySizes := s₀.tySizes, adtPad := s₀.adtPad }
        true cLC (fun _ => none) = (fun _ => none) := by
    funext i
    unfold denoteLocals
    cases decide (cLC ≤ i) <;> rfl
  have hgen :
      denoteLocalGens true cLC (fun _ => 0) = (fun _ => 0) := by
    funext i
    unfold denoteLocalGens
    cases decide (cLC ≤ i) <;> rfl
  rw [hloc, hgen]
  try rfl

/-- Normalize a compile-time constant return value into a context-free constant
scalar (`MirVal.isConstScalar`). -/
def symNormalizeConstVal (pc : PathCond) : SymVal → Option SymVal
  | .usize n =>
    match evalSymNatUnder pc n with
    | .const c => some (.usize (.const c))
    | _ => none
  | .bool b =>
    match evalSymBool pc b with
    | .val bv => some (.bool (.const bv))
    | _ => none
  | .unit => some .unit
  | _ => none

theorem symNormalizeConstVal_sound {cLC : Nat} {sConst₀ s₀ : MirState}
    {pc : PathCond} (hmatch : pc.Matches cLC sConst₀)
    (retVal : SymVal) {normVal : SymVal}
    (h : symNormalizeConstVal pc retVal = some normVal) :
    retVal.denote sConst₀ = normVal.denote s₀ ∧
      (retVal.denote sConst₀).isConstScalar = true := by
  cases retVal <;> try (cases h; done)
  case usize n =>
    dsimp [symNormalizeConstVal] at h
    cases hn : evalSymNatUnder pc n <;> try (rw [hn] at h; cases h; done)
    case const c =>
      rw [hn] at h
      injection h with hnorm; subst hnorm
      have hn' : n.denote sConst₀ = c := by
        rw [← evalSymNatUnder_sound hmatch n, hn]; rfl
      dsimp [SymVal.denote, SymNat.denote, MirVal.isConstScalar]
      exact ⟨congrArg MirVal.usize hn', rfl⟩
  case bool b =>
    dsimp [symNormalizeConstVal] at h
    cases hb : evalSymBool pc b <;> try (rw [hb] at h; cases h; done)
    case val bv =>
      rw [hb] at h
      injection h with hnorm; subst hnorm
      have hb' := evalSymBool_sound hmatch b hb
      dsimp [SymVal.denote, SymBool.denote, MirVal.isConstScalar]
      exact ⟨congrArg MirVal.bool hb', rfl⟩
  case unit =>
    injection h with hnorm; subst hnorm
    exact ⟨rfl, rfl⟩

theorem denoteLocalGens_bump_lt (isRootFrame : Bool) (rootLC : Nat)
    (symGens : Nat → Nat) {idx : Nat}
    (hidx : ¬ (isRootFrame = true ∧ rootLC ≤ idx)) :
    denoteLocalGens isRootFrame rootLC (bumpGen symGens idx) =
      bumpGen (denoteLocalGens isRootFrame rootLC symGens) idx := by
  funext i
  unfold bumpGen denoteLocalGens
  cases h : isRootFrame && decide (rootLC ≤ i) with
  | false => rfl
  | true =>
    rcases Bool.and_eq_true_iff.mp h with ⟨hr, hle⟩
    have hne : (i == idx) = false := by
      have hle' := of_decide_eq_true hle
      exact beq_eq_false_iff_ne.mpr (fun heq => by subst heq; exact hidx ⟨hr, hle'⟩)
    rw [hne]
    rfl

/-- Symbolic evaluation of `Stmt.assign dst rv`. -/
def symEvalRvalue (rootLC : Nat) (activeBody : MirBody) (st : SymState)
    (dst : Place) (rv : Rvalue) (adts : List AdtDecl)
    (target : TargetLayout := defaultTargetLayout) : SymStepOut :=
  match rv with
  | .use op =>
    match symEvalOperand rootLC activeBody.localCount st op with
    | .needSplit sp => .split sp
    | .unknown => .failed
    | .val (v, locals') =>
      match symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
          locals' dst v with
      | some locals'' => st.nextStmt locals''
      | none => .failed
  | .repeat op len =>
    match symEvalOperand rootLC activeBody.localCount st op with
    | .needSplit sp => .split sp
    | .unknown => .failed
    | .val (v, locals') =>
      match symEvalRepeatElem st.pc v with
      | some bits =>
        match symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
            locals' dst (.bytes (.const len) bits) with
        | some locals'' => st.nextStmt locals''
        | none => .failed
      | none => .failed
  | .repeatSizeOf op sizedTy =>
    match symEvalOperand rootLC activeBody.localCount st op,
          symEvalTyByteSize adts sizedTy target with
    | .needSplit sp, _ => .split sp
    | .val (v, locals'), some sz =>
      match symEvalRepeatElem st.pc v with
      | some bits =>
        match symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
            locals' dst (.bytes sz bits) with
        | some locals'' => st.nextStmt locals''
        | none => .failed
      | none => .failed
    | _, _ => .failed
  | .binaryOp op lhs rhs =>
    match symEvalOperand rootLC activeBody.localCount st lhs with
    | .needSplit sp => .split sp
    | .unknown => .failed
    | .val (v1, locals1) =>
      match symEvalOperand rootLC activeBody.localCount
          { st with locals := locals1 } rhs with
      | .needSplit sp => .split sp
      | .unknown => .failed
      | .val (v2, locals2) =>
        match symEvalBinOp st.pc op v1 v2 with
        | some outVal =>
          match symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
              locals2 dst outVal with
          | some locals3 => st.nextStmt locals3
          | none => .failed
        | none =>
          match v1, v2 with
          | .bool a, .bool b =>
            match evalSymBool st.pc a, evalSymBool st.pc b with
            | .needSplit sp, _ => .split sp
            | _, .needSplit sp => .split sp
            | _, _ => .failed
          | _, _ => .failed
  | .unaryOp op src =>
    match symEvalOperand rootLC activeBody.localCount st src with
    | .needSplit sp => .split sp
    | .unknown => .failed
    | .val (v, locals') =>
      match symEvalUnOp op v with
      | some outVal =>
        match symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
            locals' dst outVal with
        | some locals'' => st.nextStmt locals''
        | none => .failed
      | none => .failed
  | .aggregate adtId op =>
    if (findAdtDecl adts adtId).any
        (fun d => d.fields.length == 1 && d.repr != .unmodeled) then
      match symEvalOperand rootLC activeBody.localCount st op with
      | .needSplit sp => .split sp
      | .unknown => .failed
      | .val (v, locals') =>
        match symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
            locals' dst (.adt adtId v) with
        | some locals'' => st.nextStmt locals''
        | none => .failed
    else
      .failed
  | .aggregateFields ops adtIdOpt =>
    match symEvalOperandList rootLC activeBody.localCount st ops with
    | .needSplit sp => .split sp
    | .unknown => .failed
    | .val (vs, locals') =>
      match adtIdOpt with
      | some adtId =>
        if (findAdtDecl adts adtId).any
            (fun d => d.fields.length == vs.length && d.repr != .unmodeled) then
          match symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
              locals' dst (.adt adtId (symPackFields vs)) with
          | some locals'' => st.nextStmt locals''
          | none => .failed
        else
          .failed
      | none =>
        match symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
            locals' dst (symPackFields vs) with
        | some locals'' => st.nextStmt locals''
        | none => .failed
  | .ref src | .rawPtr _ src =>
    match symEvalRefPlace rootLC activeBody.localCount st src with
    | some refVal =>
      match symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
          st.locals dst refVal with
      | some locals' => st.nextStmt locals'
      | none => .failed
    | none => .failed
  | .cast (.transmute srcTy) op dstTy =>
    match symEvalOperand rootLC activeBody.localCount st op with
    | .needSplit sp => .split sp
    | .unknown => .failed
    | .val (v, locals') =>
      match symEvalTransmuteVal adts st.pc srcTy dstTy v target with
      | .needSplit sp => .split sp
      | .unknown => .failed
      | .val outVal =>
        match symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
            locals' dst outVal with
        | some locals'' => st.nextStmt locals''
        | none => .failed
  | .cast .intToInt op dstTy | .cast .ptrToPtr op dstTy =>
    if (symEvalTyByteSize adts dstTy target).isSome then
      match symEvalOperand rootLC activeBody.localCount st op with
      | .needSplit sp => .split sp
      | .unknown => .failed
      | .val (v, locals') =>
        match symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
            locals' dst v with
        | some locals'' => st.nextStmt locals''
        | none => .failed
    else
      .failed
  | _ =>
    .failed

theorem symEvalRvalue_sound {rootLC : Nat} {s₀ : MirState} {st : SymState}
    (hmatch : st.pc.Matches rootLC s₀) (activeBody : MirBody)
    (dst : Place) (rv : Rvalue) (adts : List AdtDecl)
    (bodies : List BodyDecl)
    (evalConstBody : MirBody → MirState → RawStep MirState MirReturn)
    (target : TargetLayout) :
    SymStepOut.Agrees rootLC s₀ st.pc
      (symEvalRvalue rootLC activeBody st dst rv adts target)
      (evalMirStmt activeBody (st.toMirState rootLC s₀) (.assign dst rv)
        adts bodies evalConstBody target) := by
  cases rv with
  | use op =>
    dsimp [symEvalRvalue, evalMirStmt]
    cases hop : symEvalOperand rootLC activeBody.localCount st op with
    | needSplit _ => trivial
    | unknown => trivial
    | val p =>
      rcases p with ⟨v, locals'⟩
      dsimp
      rw [symEvalOperand_sound hmatch op hop]
      dsimp
      cases hasg :
          symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
            locals' dst v with
      | none => trivial
      | some locals'' =>
        rw [symAssignPlace_sound s₀ (st.frameId == 0) rootLC
              activeBody.localCount locals' dst v hasg]
        exact ⟨rfl, rfl⟩
  | «repeat» op len =>
    dsimp [symEvalRvalue, evalMirStmt]
    cases hop : symEvalOperand rootLC activeBody.localCount st op with
    | needSplit _ => trivial
    | unknown => trivial
    | val p =>
      rcases p with ⟨v, locals'⟩
      dsimp
      rw [symEvalOperand_sound hmatch op hop]
      dsimp
      cases hrep : symEvalRepeatElem st.pc v with
      | none => trivial
      | some bits =>
        rw [symEvalRepeatElem_sound hmatch v hrep]
        dsimp
        cases hasg :
            symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
              locals' dst (.bytes (.const len) bits) with
        | none => trivial
        | some locals'' =>
          have hasg_sound :=
            symAssignPlace_sound s₀ (st.frameId == 0) rootLC
              activeBody.localCount locals' dst
              (.bytes (.const len) bits) hasg
          dsimp [SymVal.denote, SymNat.denote] at hasg_sound
          rw [hasg_sound]
          exact ⟨rfl, rfl⟩
  | repeatSizeOf op sizedTy =>
    dsimp [symEvalRvalue, evalMirStmt]
    cases hop : symEvalOperand rootLC activeBody.localCount st op with
    | needSplit _ => trivial
    | unknown => trivial
    | val p =>
      rcases p with ⟨v, locals'⟩
      cases hsz : symEvalTyByteSize adts sizedTy target with
      | none => trivial
      | some sz =>
        dsimp
        have hty : (st.toMirState rootLC s₀).tySizes = s₀.tySizes := rfl
        have hpad : (st.toMirState rootLC s₀).adtPad = s₀.adtPad := rfl
        rw [symEvalOperand_sound hmatch op hop, hty, hpad,
            symEvalTyByteSize_sound s₀ adts sizedTy target hsz]
        dsimp
        cases hrep : symEvalRepeatElem st.pc v with
        | none => trivial
        | some bits =>
          rw [symEvalRepeatElem_sound hmatch v hrep]
          dsimp
          cases hasg :
              symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
                locals' dst (.bytes sz bits) with
          | none => trivial
          | some locals'' =>
            have hasg_sound :=
              symAssignPlace_sound s₀ (st.frameId == 0) rootLC
                activeBody.localCount locals' dst (.bytes sz bits) hasg
            dsimp [SymVal.denote] at hasg_sound
            rw [hasg_sound]
            exact ⟨rfl, rfl⟩
  | binaryOp op lhs rhs =>
    dsimp [symEvalRvalue, evalMirStmt]
    cases hl : symEvalOperand rootLC activeBody.localCount st lhs with
    | needSplit _ => trivial
    | unknown => trivial
    | val p1 =>
      rcases p1 with ⟨v1, locals1⟩
      dsimp
      rw [symEvalOperand_sound hmatch lhs hl]
      dsimp
      cases hr :
          symEvalOperand rootLC activeBody.localCount
            { st with locals := locals1 } rhs with
      | needSplit _ => trivial
      | unknown => trivial
      | val p2 =>
        rcases p2 with ⟨v2, locals2⟩
        dsimp
        have hr_sound :=
          symEvalOperand_sound (st := { st with locals := locals1 }) hmatch
            rhs hr
        dsimp [SymState.toMirState] at hr_sound ⊢
        rw [hr_sound]
        dsimp
        cases hb : symEvalBinOp st.pc op v1 v2 with
        | none =>
          dsimp
          cases v1 <;> cases v2 <;> try trivial
          case bool.bool a b =>
            dsimp
            cases evalSymBool st.pc a <;> cases evalSymBool st.pc b <;> trivial
        | some outVal =>
          rw [symEvalBinOp_sound hmatch op v1 v2 hb]
          dsimp
          cases hasg :
              symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
                locals2 dst outVal with
          | none => trivial
          | some locals3 =>
            rw [symAssignPlace_sound s₀ (st.frameId == 0) rootLC
                  activeBody.localCount locals2 dst outVal hasg]
            exact ⟨rfl, rfl⟩
  | unaryOp op src =>
    dsimp [symEvalRvalue, evalMirStmt]
    cases hop : symEvalOperand rootLC activeBody.localCount st src with
    | needSplit _ => trivial
    | unknown => trivial
    | val p =>
      rcases p with ⟨v, locals'⟩
      dsimp
      rw [symEvalOperand_sound hmatch src hop]
      dsimp
      cases hu : symEvalUnOp op v with
      | none => trivial
      | some outVal =>
        rw [symEvalUnOp_sound s₀ op v hu]
        dsimp
        cases hasg :
            symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
              locals' dst outVal with
        | none => trivial
        | some locals'' =>
          rw [symAssignPlace_sound s₀ (st.frameId == 0) rootLC
                activeBody.localCount locals' dst outVal hasg]
          exact ⟨rfl, rfl⟩
  | aggregate adtId op =>
    dsimp [symEvalRvalue, evalMirStmt]
    cases hany :
        (findAdtDecl adts adtId).any
          (fun d => d.fields.length == 1 && d.repr != .unmodeled) with
    | false => trivial
    | true =>
      dsimp
      cases hop : symEvalOperand rootLC activeBody.localCount st op with
      | needSplit _ => trivial
      | unknown => trivial
      | val p =>
        rcases p with ⟨v, locals'⟩
        dsimp
        rw [symEvalOperand_sound hmatch op hop]
        dsimp
        cases hasg :
            symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
              locals' dst (.adt adtId v) with
        | none => trivial
        | some locals'' =>
          have hasg_sound :=
            symAssignPlace_sound s₀ (st.frameId == 0) rootLC
              activeBody.localCount locals' dst (.adt adtId v) hasg
          dsimp [SymVal.denote] at hasg_sound
          rw [hasg_sound]
          exact ⟨rfl, rfl⟩
  | aggregateFields ops adtIdOpt =>
    dsimp [symEvalRvalue, evalMirStmt]
    cases hops : symEvalOperandList rootLC activeBody.localCount st ops with
    | needSplit _ => trivial
    | unknown => trivial
    | val p =>
      rcases p with ⟨vs, locals'⟩
      dsimp
      rw [symEvalOperandList_sound ops st hmatch hops]
      dsimp
      cases adtIdOpt with
      | some adtId =>
        dsimp
        rw [List.length_map]
        cases hany :
            (findAdtDecl adts adtId).any
              (fun d => d.fields.length == vs.length && d.repr != .unmodeled) with
        | false => trivial
        | true =>
          dsimp
          cases hasg :
              symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
                locals' dst (.adt adtId (symPackFields vs)) with
          | none => trivial
          | some locals'' =>
            have hasg_sound :=
              symAssignPlace_sound s₀ (st.frameId == 0) rootLC
                activeBody.localCount locals' dst
                (.adt adtId (symPackFields vs)) hasg
            dsimp [SymVal.denote] at hasg_sound
            rw [symPackFields_denote] at hasg_sound
            rw [hasg_sound]
            exact ⟨rfl, rfl⟩
      | none =>
        dsimp
        cases hasg :
            symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
              locals' dst (symPackFields vs) with
        | none => trivial
        | some locals'' =>
          have hasg_sound :=
            symAssignPlace_sound s₀ (st.frameId == 0) rootLC
              activeBody.localCount locals' dst (symPackFields vs) hasg
          rw [symPackFields_denote] at hasg_sound
          rw [hasg_sound]
          exact ⟨rfl, rfl⟩
  | ref src =>
    dsimp [symEvalRvalue, evalMirStmt]
    cases hr : symEvalRefPlace rootLC activeBody.localCount st src with
    | none => trivial
    | some refVal =>
      rw [symEvalRefPlace_sound hmatch src hr]
      dsimp [SymState.toMirState]
      cases hasg :
          symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
            st.locals dst refVal with
      | none => trivial
      | some locals' =>
        rw [symAssignPlace_sound s₀ (st.frameId == 0) rootLC
              activeBody.localCount st.locals dst refVal hasg]
        exact ⟨rfl, rfl⟩
  | rawPtr kind src =>
    dsimp [symEvalRvalue, evalMirStmt]
    cases hr : symEvalRefPlace rootLC activeBody.localCount st src with
    | none => trivial
    | some refVal =>
      rw [symEvalRefPlace_sound hmatch src hr]
      dsimp [SymState.toMirState]
      cases hasg :
          symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
            st.locals dst refVal with
      | none => trivial
      | some locals' =>
        rw [symAssignPlace_sound s₀ (st.frameId == 0) rootLC
              activeBody.localCount st.locals dst refVal hasg]
        exact ⟨rfl, rfl⟩
  | cast kind op dstTy =>
    cases kind with
    | transmute srcTy =>
      dsimp [symEvalRvalue, evalMirStmt]
      cases hop : symEvalOperand rootLC activeBody.localCount st op with
      | needSplit _ => trivial
      | unknown => trivial
      | val p =>
        rcases p with ⟨v, locals'⟩
        dsimp
        rw [symEvalOperand_sound hmatch op hop]
        dsimp
        cases htr : symEvalTransmuteVal adts st.pc srcTy dstTy v target with
        | needSplit _ => trivial
        | unknown => trivial
        | val outVal =>
          dsimp
          rw [symEvalTransmuteVal_sound hmatch adts
                { (st.toMirState rootLC s₀) with
                  locals := denoteLocals s₀ (st.frameId == 0) rootLC locals' }
                rfl rfl srcTy dstTy v target htr]
          dsimp
          cases hasg :
              symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
                locals' dst outVal with
          | none => trivial
          | some locals'' =>
            rw [symAssignPlace_sound s₀ (st.frameId == 0) rootLC
                  activeBody.localCount locals' dst outVal hasg]
            exact ⟨rfl, rfl⟩
    | intToInt =>
      dsimp [symEvalRvalue, evalMirStmt]
      cases hsz : symEvalTyByteSize adts dstTy target with
      | none => trivial
      | some sz =>
        have hty : (st.toMirState rootLC s₀).tySizes = s₀.tySizes := rfl
        have hpad : (st.toMirState rootLC s₀).adtPad = s₀.adtPad := rfl
        rw [hty, hpad, symEvalTyByteSize_sound s₀ adts dstTy target hsz]
        dsimp [SymState.toMirState]
        cases hop : symEvalOperand rootLC activeBody.localCount st op with
        | needSplit _ => trivial
        | unknown => trivial
        | val p =>
          rcases p with ⟨v, locals'⟩
          dsimp
          have hop_sound := symEvalOperand_sound hmatch op hop
          dsimp [SymState.toMirState] at hop_sound
          rw [hop_sound]
          dsimp
          cases hasg :
              symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
                locals' dst v with
          | none => trivial
          | some locals'' =>
            rw [symAssignPlace_sound s₀ (st.frameId == 0) rootLC
                  activeBody.localCount locals' dst v hasg]
            exact ⟨rfl, rfl⟩
    | ptrToPtr =>
      dsimp [symEvalRvalue, evalMirStmt]
      cases hsz : symEvalTyByteSize adts dstTy target with
      | none => trivial
      | some sz =>
        have hty : (st.toMirState rootLC s₀).tySizes = s₀.tySizes := rfl
        have hpad : (st.toMirState rootLC s₀).adtPad = s₀.adtPad := rfl
        rw [hty, hpad, symEvalTyByteSize_sound s₀ adts dstTy target hsz]
        dsimp [SymState.toMirState]
        cases hop : symEvalOperand rootLC activeBody.localCount st op with
        | needSplit _ => trivial
        | unknown => trivial
        | val p =>
          rcases p with ⟨v, locals'⟩
          dsimp
          have hop_sound := symEvalOperand_sound hmatch op hop
          dsimp [SymState.toMirState] at hop_sound
          rw [hop_sound]
          dsimp
          cases hasg :
              symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
                locals' dst v with
          | none => trivial
          | some locals'' =>
            rw [symAssignPlace_sound s₀ (st.frameId == 0) rootLC
                  activeBody.localCount locals' dst v hasg]
            exact ⟨rfl, rfl⟩
    | pointerExposeProvenance | pointerWithExposedProvenance
    | pointerCoercion | floatToInt | floatToFloat | intToFloat
    | fnPtrToPtr | subtype =>
      trivial
  | refMut _ | refFake _ | threadLocalRef _ | discriminant _
  | copyForDeref _ | wrapUnsafeBinder _ _ | reborrow _ _ _ =>
    trivial

/-- Symbolic single-step evaluation of a MIR `Stmt`. -/
def symEvalStmt (rootLC : Nat) (activeBody : MirBody) (st : SymState)
    (stmt : Stmt) (adts : List AdtDecl)
    (bodies : List BodyDecl := [])
    (symEvalConstBody : MirBody → SymState → SymStepOut := fun _ _ => .failed)
    (target : TargetLayout := defaultTargetLayout) : SymStepOut :=
  match stmt with
  | .assign dst rv =>
    symEvalRvalue rootLC activeBody st dst rv adts target
  | .evalConst dst constId typeArgs =>
    match (findBody bodies constId).bind (MirBody.subst typeArgs) with
    | some cBody =>
      if cBody.argTys.isEmpty then
        match symEvalConstBody cBody (symConstEntryState st.pc) with
        | .split sp => .split sp
        | .returned retVal _ =>
          match symNormalizeConstVal (st.pc.forConstEval) retVal with
          | some normVal =>
            match symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
                st.locals dst normVal with
            | some locals' => st.nextStmt locals'
            | none => .failed
          | none => .failed
        | .unwind | .abort | .compileTimeError =>
          .compileTimeError
        | _ => .failed
      else
        .failed
    | none => .failed
  | .placeMention p =>
    match p.projection with
    | [] =>
      if p.loc.index < activeBody.localCount then
        st.nextStmt st.locals
      else
        .failed
    | _ =>
      match symEvalPlace rootLC activeBody.localCount st p with
      | some _ => st.nextStmt st.locals
      | none => .failed
  | .storageLive loc | .storageDead loc =>
    if !((st.frameId == 0) && decide (rootLC ≤ loc.index)) &&
       decide (loc.index < activeBody.localCount) then
      st.nextStmtGen (updateSymLocal st.locals loc.index none)
        (bumpGen st.localGens loc.index)
    else
      .failed
  | .nop | .constEvalCounter =>
    st.nextStmt st.locals
  | _ =>
    .failed

theorem symEvalStmt_sound {rootLC : Nat} {s₀ : MirState} {st : SymState}
    (hmatch : st.pc.Matches rootLC s₀) (activeBody : MirBody) (stmt : Stmt)
    (adts : List AdtDecl) (bodies : List BodyDecl)
    (symEvalConstBody : MirBody → SymState → SymStepOut)
    (evalConstBody : MirBody → MirState → RawStep MirState MirReturn)
    (hconst : ∀ cBody,
      SymStepOut.Agrees cBody.localCount
        (constEntryState s₀.tySizes s₀.adtPad)
        (st.pc.forConstEval)
        (symEvalConstBody cBody (symConstEntryState st.pc))
        (evalConstBody cBody (constEntryState s₀.tySizes s₀.adtPad)))
    (target : TargetLayout) :
    SymStepOut.Agrees rootLC s₀ st.pc
      (symEvalStmt rootLC activeBody st stmt adts bodies symEvalConstBody
        target)
      (evalMirStmt activeBody (st.toMirState rootLC s₀) stmt adts bodies
        evalConstBody target) := by
  cases stmt with
  | assign dst rv =>
    exact symEvalRvalue_sound hmatch activeBody dst rv adts bodies
      evalConstBody target
  | evalConst dst constId typeArgs =>
    dsimp [symEvalStmt, evalMirStmt]
    cases hcb : (findBody bodies constId).bind (MirBody.subst typeArgs) with
    | none => trivial
    | some cBody =>
      dsimp
      cases harg : cBody.argTys.isEmpty with
      | false => trivial
      | true =>
        dsimp [SymState.toMirState]
        have hc := hconst cBody
        cases hres : symEvalConstBody cBody (symConstEntryState st.pc) with
        | silent _ => trivial
        | split _ => trivial
        | failed => trivial
        | unwind =>
          rw [hres] at hc
          dsimp [SymStepOut.Agrees] at hc
          rw [hc]
          rfl
        | abort =>
          rw [hres] at hc
          dsimp [SymStepOut.Agrees] at hc
          rw [hc]
          rfl
        | compileTimeError =>
          rw [hres] at hc
          dsimp [SymStepOut.Agrees] at hc
          rw [hc]
          rfl
        | returned retVal csTerm =>
          rw [hres] at hc
          dsimp [SymStepOut.Agrees] at hc
          rw [hc.2]
          dsimp
          cases hnorm : symNormalizeConstVal (st.pc.forConstEval) retVal with
          | none => trivial
          | some normVal =>
            rcases symNormalizeConstVal_sound (s₀ := s₀)
                (forConstEval_matches hmatch cBody.localCount) retVal hnorm with
              ⟨hden, hscal⟩
            rw [hscal, hden]
            dsimp
            cases hasg :
                symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
                  st.locals dst normVal with
            | none => trivial
            | some locals' =>
              rw [symAssignPlace_sound s₀ (st.frameId == 0) rootLC
                    activeBody.localCount st.locals dst normVal hasg]
              exact ⟨rfl, rfl⟩
  | placeMention p =>
    rcases p with ⟨loc, proj⟩
    dsimp [symEvalStmt, evalMirStmt]
    cases proj with
    | nil =>
      dsimp
      by_cases hlt : loc.index < activeBody.localCount
      · rw [if_pos hlt, if_pos hlt]
        exact ⟨rfl, rfl⟩
      · rw [if_neg hlt, if_neg hlt]
        trivial
    | cons e es =>
      dsimp
      cases hp :
          symEvalPlace rootLC activeBody.localCount st
            { loc := loc, projection := e :: es } with
      | none => trivial
      | some sv =>
        have hp_sound :=
          symEvalPlace_sound hmatch { loc := loc, projection := e :: es } hp
        rw [hp_sound]
        exact ⟨rfl, rfl⟩
  | storageLive loc =>
    dsimp [symEvalStmt, evalMirStmt]
    cases hguard :
        (!((st.frameId == 0) && decide (rootLC ≤ loc.index)) &&
         decide (loc.index < activeBody.localCount)) with
    | false => trivial
    | true =>
      rcases Bool.and_eq_true_iff.mp hguard with ⟨hnot, hlt⟩
      have hidx : ¬ ((st.frameId == 0) = true ∧ rootLC ≤ loc.index) := by
        intro ⟨hf, hle⟩
        have htrue : ((st.frameId == 0) && decide (rootLC ≤ loc.index)) = true :=
          Bool.and_eq_true_iff.mpr ⟨hf, decide_eq_true hle⟩
        rw [htrue] at hnot
        cases hnot
      rw [if_pos (of_decide_eq_true hlt)]
      dsimp [SymStepOut.Agrees, SymState.nextStmtGen, MirState.nextStmtGen,
             SymState.toMirState]
      refine ⟨rfl, ?_⟩
      rw [denoteLocals_update_lt s₀ (st.frameId == 0) rootLC st.locals none hidx,
          denoteLocalGens_bump_lt (st.frameId == 0) rootLC st.localGens hidx]
      rfl
  | storageDead loc =>
    dsimp [symEvalStmt, evalMirStmt]
    cases hguard :
        (!((st.frameId == 0) && decide (rootLC ≤ loc.index)) &&
         decide (loc.index < activeBody.localCount)) with
    | false => trivial
    | true =>
      rcases Bool.and_eq_true_iff.mp hguard with ⟨hnot, hlt⟩
      have hidx : ¬ ((st.frameId == 0) = true ∧ rootLC ≤ loc.index) := by
        intro ⟨hf, hle⟩
        have htrue : ((st.frameId == 0) && decide (rootLC ≤ loc.index)) = true :=
          Bool.and_eq_true_iff.mpr ⟨hf, decide_eq_true hle⟩
        rw [htrue] at hnot
        cases hnot
      rw [if_pos (of_decide_eq_true hlt)]
      dsimp [SymStepOut.Agrees, SymState.nextStmtGen, MirState.nextStmtGen,
             SymState.toMirState]
      refine ⟨rfl, ?_⟩
      rw [denoteLocals_update_lt s₀ (st.frameId == 0) rootLC st.locals none hidx,
          denoteLocalGens_bump_lt (st.frameId == 0) rootLC st.localGens hidx]
      rfl
  | nop => exact ⟨rfl, rfl⟩
  | constEvalCounter => exact ⟨rfl, rfl⟩
  | fakeRead _ | setDiscriminant _ _ | ascribeUserType _ | coverage
  | intrinsic _ | backwardIncompatibleDropHint _ =>
    trivial

/-- Symbolic single-step evaluation of a MIR `Terminator`. -/
def symEvalTerminator (rootLC : Nat) (adts : List AdtDecl)
    (bodies : List BodyDecl) (activeBody : MirBody) (st : SymState)
    (term : Terminator) (targetLayout : TargetLayout := defaultTargetLayout) :
    SymStepOut :=
  match term with
  | .return_ =>
    if decide (0 < activeBody.localCount) &&
       !((st.frameId == 0) && decide (rootLC ≤ 0)) then
      match st.locals 0 with
      | none => .failed
      | some retVal =>
        if retVal.isFullyInit &&
           symReturnRefsOk rootLC st activeBody.localCount retVal then
          match st.stack with
          | [] => .returned retVal st
          | frame :: restStack =>
            if frame.retBlock < frame.callerBody.blocks.length then
              match symAssignPlace (frame.callerFrameId == 0) rootLC
                  frame.callerBody.localCount frame.callerLocals frame.retDst
                  retVal with
              | some callerLocals' =>
                .silent {
                  locals := callerLocals'
                  localGens := frame.callerLocalGens
                  block := frame.retBlock
                  stmtIdx := 0
                  curBody :=
                    if restStack.isEmpty then none else some frame.callerBody
                  stack := restStack
                  frameId := frame.callerFrameId
                  nextFrameId := st.nextFrameId
                  pc := st.pc
                }
              | none => .failed
            else
              .failed
        else
          .failed
    else
      .failed
  | .goto target =>
    if target.index < activeBody.blocks.length then
      st.gotoBlock st.locals target.index
    else
      .failed
  | .unreachable =>
    .failed
  | .panic hasCleanup =>
    if hasCleanup || !st.stack.isEmpty then
      .failed
    else
      .unwind
  | .assert cond expected target onFail hasCleanup =>
    match symEvalOperand rootLC activeBody.localCount st cond with
    | .needSplit sp => .split sp
    | .unknown => .failed
    | .val (.bool b, locals') =>
      match evalSymBool st.pc b with
      | .needSplit sp => .split sp
      | .unknown => .failed
      | .val bv =>
        if bv == expected then
          if target.index < activeBody.blocks.length then
            st.gotoBlock locals' target.index
          else
            .failed
        else
          match onFail with
          | .unwind =>
            if hasCleanup || !st.stack.isEmpty then
              .failed
            else
              .unwind
          | .abort => .abort
          | .ub => .failed
    | .val _ => .failed
  | .switchInt discr falseTarget trueTarget =>
    match symEvalOperand rootLC activeBody.localCount st discr with
    | .needSplit sp => .split sp
    | .unknown => .failed
    | .val (.bool b, locals') =>
      match evalSymBool st.pc b with
      | .needSplit sp => .split sp
      | .unknown => .failed
      | .val false =>
        if falseTarget.index < activeBody.blocks.length then
          st.gotoBlock locals' falseTarget.index
        else
          .failed
      | .val true =>
        if trueTarget.index < activeBody.blocks.length then
          st.gotoBlock locals' trueTarget.index
        else
          .failed
    | .val _ => .failed
  | .callLayout dst query target =>
    if target.index < activeBody.blocks.length then
      match symEvalLayoutQuery adts st.pc query targetLayout with
      | .needSplit sp => .split sp
      | .unknown => .failed
      | .val val =>
        match symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
            st.locals dst (.usize val) with
        | some locals' => st.gotoBlock locals' target.index
        | none => .failed
    else
      .failed
  | .callTransmuteCopy dst srcTy dstTy op target =>
    if target.index < activeBody.blocks.length then
      match symEvalOperand rootLC activeBody.localCount st op with
      | .needSplit sp => .split sp
      | .unknown => .failed
      | .val (argVal, locals') =>
        match symEvalTransmuteCopy rootLC adts { st with locals := locals' }
            srcTy dstTy argVal targetLayout with
        | .needSplit sp => .split sp
        | .unknown => .failed
        | .val outVal =>
          match symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
              locals' dst outVal with
          | some locals'' => st.gotoBlock locals'' target.index
          | none => .failed
    else
      .failed
  | .call1 dst calleeId arg target typeArgs =>
    match (findBody bodies calleeId).bind (MirBody.subst typeArgs) with
    | none => .failed
    | some instCallee =>
      if dst.loc.index < activeBody.localCount &&
         target.index < activeBody.blocks.length &&
         instCallee.argTys.length == 1 &&
         2 ≤ instCallee.localCount &&
         0 < instCallee.blocks.length &&
         0 < st.nextFrameId then
        match symEvalOperand rootLC activeBody.localCount st arg with
        | .needSplit sp => .split sp
        | .unknown => .failed
        | .val (argVal, callerLocals') =>
          let calleeLocals : Nat → Option SymVal :=
            updateSymLocal (fun _ => none) 1 (some argVal)
          let frame : SymStackFrame := {
            callerBody := activeBody
            callerLocals := callerLocals'
            callerLocalGens := st.localGens
            retDst := dst
            retBlock := target.index
            callerFrameId := st.frameId
          }
          .silent {
            locals := calleeLocals
            localGens := fun _ => 0
            block := 0
            stmtIdx := 0
            curBody := some instCallee
            stack := frame :: st.stack
            frameId := st.nextFrameId
            nextFrameId := st.nextFrameId + 1
            pc := st.pc
          }
      else
        .failed
  | _ =>
    .failed

theorem list_map_isEmpty {α β : Type} (f : α → β) (xs : List α) :
    (xs.map f).isEmpty = xs.isEmpty := by
  cases xs <;> rfl

theorem symEvalTerminator_sound {rootLC : Nat} {s₀ : MirState} {st : SymState}
    (hmatch : st.pc.Matches rootLC s₀) (adts : List AdtDecl)
    (bodies : List BodyDecl) (activeBody : MirBody) (term : Terminator)
    (targetLayout : TargetLayout) :
    SymStepOut.Agrees rootLC s₀ st.pc
      (symEvalTerminator rootLC adts bodies activeBody st term targetLayout)
      (evalMirTerminator adts bodies activeBody (st.toMirState rootLC s₀)
        term targetLayout) := by
  cases term with
  | return_ =>
    dsimp [symEvalTerminator, evalMirTerminator]
    cases hguard :
        (decide (0 < activeBody.localCount) &&
         !((st.frameId == 0) && decide (rootLC ≤ 0))) with
    | false => trivial
    | true =>
      rcases Bool.and_eq_true_iff.mp hguard with ⟨hlt, hnot⟩
      have hidx : ¬ ((st.frameId == 0) = true ∧ rootLC ≤ 0) := by
        intro ⟨hf, hle⟩
        have htrue : ((st.frameId == 0) && decide (rootLC ≤ 0)) = true :=
          Bool.and_eq_true_iff.mpr ⟨hf, decide_eq_true hle⟩
        rw [htrue] at hnot
        cases hnot
      rw [if_pos (of_decide_eq_true hlt)]
      dsimp
      have hloc0 :
          (st.toMirState rootLC s₀).locals 0 =
            (st.locals 0).map (SymVal.denote s₀) :=
        denoteLocals_lt s₀ (st.frameId == 0) rootLC st.locals hidx
      rw [hloc0]
      cases hr0 : st.locals 0 with
      | none => trivial
      | some retVal =>
        dsimp [Option.map]
        cases hok :
            (retVal.isFullyInit &&
             symReturnRefsOk rootLC st activeBody.localCount retVal) with
        | false => trivial
        | true =>
          rcases Bool.and_eq_true_iff.mp hok with ⟨hinit, hrefs⟩
          rw [SymVal.isFullyInit_denote s₀ retVal, hinit,
              symReturnRefsOk_sound hmatch activeBody.localCount retVal hrefs]
          dsimp
          cases hstk : st.stack with
          | nil =>
            dsimp [SymStepOut.Agrees]
            refine ⟨rfl, ?_⟩
            have hstk' : (st.toMirState rootLC s₀).stack = [] := by
              dsimp [SymState.toMirState]
              rw [hstk]
              rfl
            rw [hstk']
          | cons frame restStack =>
            dsimp
            by_cases hretb : frame.retBlock < frame.callerBody.blocks.length
            · rw [if_pos hretb]
              cases hasg :
                  symAssignPlace (frame.callerFrameId == 0) rootLC
                    frame.callerBody.localCount frame.callerLocals frame.retDst
                    retVal with
              | none => trivial
              | some callerLocals' =>
                dsimp [SymStepOut.Agrees]
                refine ⟨rfl, ?_⟩
                have hstk' :
                    (st.toMirState rootLC s₀).stack =
                      frame.toStackFrame rootLC s₀ ::
                        restStack.map (SymStackFrame.toStackFrame rootLC s₀) := by
                  dsimp [SymState.toMirState]
                  rw [hstk]
                  rfl
                rw [hstk']
                dsimp [SymStackFrame.toStackFrame]
                rw [if_pos hretb]
                rw [symAssignPlace_sound s₀ (frame.callerFrameId == 0) rootLC
                      frame.callerBody.localCount frame.callerLocals
                      frame.retDst retVal hasg]
                dsimp [SymState.toMirState]
                rw [list_map_isEmpty]
            · rw [if_neg hretb]
              trivial
  | goto target =>
    dsimp [symEvalTerminator, evalMirTerminator]
    by_cases ht : target.index < activeBody.blocks.length
    · rw [if_pos ht, if_pos ht]
      exact ⟨rfl, rfl⟩
    · rw [if_neg ht]
      trivial
  | unreachable => trivial
  | panic hasCleanup =>
    dsimp [symEvalTerminator, evalMirTerminator, SymState.toMirState]
    rw [list_map_isEmpty]
    cases (hasCleanup || !st.stack.isEmpty) with
    | true => trivial
    | false => rfl
  | assert cond expected target onFail hasCleanup =>
    dsimp [symEvalTerminator, evalMirTerminator]
    cases hop : symEvalOperand rootLC activeBody.localCount st cond with
    | needSplit _ => trivial
    | unknown => trivial
    | val p =>
      rcases p with ⟨v, locals'⟩
      cases v <;> try trivial
      case bool b =>
        dsimp
        rw [symEvalOperand_sound hmatch cond hop]
        dsimp [SymVal.denote]
        cases hb : evalSymBool st.pc b with
        | needSplit _ => trivial
        | unknown => trivial
        | val bv =>
          dsimp
          rw [evalSymBool_sound hmatch b hb]
          cases heq : (bv == expected) with
          | true =>
            dsimp
            by_cases ht : target.index < activeBody.blocks.length
            · rw [if_pos ht, if_pos ht]
              exact ⟨rfl, rfl⟩
            · rw [if_neg ht]
              trivial
          | false =>
            dsimp
            cases onFail with
            | unwind =>
              have hstk : (st.toMirState rootLC s₀).stack =
                  st.stack.map (SymStackFrame.toStackFrame rootLC s₀) := rfl
              rw [hstk, list_map_isEmpty]
              dsimp [SymState.toMirState]
              cases (hasCleanup || !st.stack.isEmpty) with
              | true => trivial
              | false => rfl
            | abort => rfl
            | ub => trivial
  | switchInt discr falseTarget trueTarget =>
    dsimp [symEvalTerminator, evalMirTerminator]
    cases hop : symEvalOperand rootLC activeBody.localCount st discr with
    | needSplit _ => trivial
    | unknown => trivial
    | val p =>
      rcases p with ⟨v, locals'⟩
      cases v <;> try trivial
      case bool b =>
        dsimp
        rw [symEvalOperand_sound hmatch discr hop]
        dsimp [SymVal.denote]
        cases hb : evalSymBool st.pc b with
        | needSplit _ => trivial
        | unknown => trivial
        | val bv =>
          rw [evalSymBool_sound hmatch b hb]
          cases bv with
          | false =>
            dsimp
            by_cases ht : falseTarget.index < activeBody.blocks.length
            · rw [if_pos ht, if_pos ht]
              exact ⟨rfl, rfl⟩
            · rw [if_neg ht]
              trivial
          | true =>
            dsimp
            by_cases ht : trueTarget.index < activeBody.blocks.length
            · rw [if_pos ht, if_pos ht]
              exact ⟨rfl, rfl⟩
            · rw [if_neg ht]
              trivial
  | callLayout dst query target =>
    dsimp [symEvalTerminator, evalMirTerminator]
    by_cases ht : target.index < activeBody.blocks.length
    · rw [if_pos ht, if_pos ht]
      cases hq : symEvalLayoutQuery adts st.pc query targetLayout with
      | needSplit _ => trivial
      | unknown => trivial
      | val val =>
        dsimp [SymState.toMirState]
        rw [symEvalLayoutQuery_sound hmatch adts query targetLayout hq]
        dsimp
        cases hasg :
            symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
              st.locals dst (.usize val) with
        | none => trivial
        | some locals' =>
          have hasg_sound :=
            symAssignPlace_sound s₀ (st.frameId == 0) rootLC
              activeBody.localCount st.locals dst (.usize val) hasg
          dsimp [SymVal.denote] at hasg_sound
          rw [hasg_sound]
          exact ⟨rfl, rfl⟩
    · rw [if_neg ht]
      trivial
  | callTransmuteCopy dst srcTy dstTy op target =>
    dsimp [symEvalTerminator, evalMirTerminator]
    by_cases ht : target.index < activeBody.blocks.length
    · rw [if_pos ht, if_pos ht]
      cases hop : symEvalOperand rootLC activeBody.localCount st op with
      | needSplit _ => trivial
      | unknown => trivial
      | val p =>
        rcases p with ⟨argVal, locals'⟩
        dsimp
        rw [symEvalOperand_sound hmatch op hop]
        dsimp
        cases htc :
            symEvalTransmuteCopy rootLC adts { st with locals := locals' }
              srcTy dstTy argVal targetLayout with
        | needSplit _ => trivial
        | unknown => trivial
        | val outVal =>
          dsimp
          have htc_sound :=
            symEvalTransmuteCopy_sound (st := { st with locals := locals' })
              hmatch adts srcTy dstTy argVal targetLayout htc
          dsimp [SymState.toMirState] at htc_sound ⊢
          rw [htc_sound]
          dsimp
          cases hasg :
              symAssignPlace (st.frameId == 0) rootLC activeBody.localCount
                locals' dst outVal with
          | none => trivial
          | some locals'' =>
            rw [symAssignPlace_sound s₀ (st.frameId == 0) rootLC
                  activeBody.localCount locals' dst outVal hasg]
            exact ⟨rfl, rfl⟩
    · rw [if_neg ht]
      trivial
  | call1 dst calleeId arg target typeArgs =>
    dsimp [symEvalTerminator, evalMirTerminator]
    cases hfind : (findBody bodies calleeId).bind (MirBody.subst typeArgs) with
    | none => trivial
    | some instCallee =>
      dsimp [Option.elim]
      cases hcond :
          (decide (dst.loc.index < activeBody.localCount) &&
           decide (target.index < activeBody.blocks.length) &&
           (instCallee.argTys.length == 1) &&
           decide (2 ≤ instCallee.localCount) &&
           decide (0 < instCallee.blocks.length) &&
           decide (0 < st.nextFrameId)) with
      | false => trivial
      | true =>
        rcases Bool.and_eq_true_iff.mp hcond with ⟨hcond5, hfid_pos⟩
        rcases Bool.and_eq_true_iff.mp hcond5 with ⟨hcond4, hblks⟩
        rcases Bool.and_eq_true_iff.mp hcond4 with ⟨hcond3, hlc2⟩
        rcases Bool.and_eq_true_iff.mp hcond3 with ⟨hcond2, harg1⟩
        rcases Bool.and_eq_true_iff.mp hcond2 with ⟨hdst, htarget⟩
        cases hop : symEvalOperand rootLC activeBody.localCount st arg with
        | needSplit _ => trivial
        | unknown => trivial
        | val p =>
          rcases p with ⟨argVal, callerLocals'⟩
          dsimp [SymStepOut.Agrees]
          refine ⟨rfl, ?_⟩
          have hd_dst := of_decide_eq_true hdst
          have hd_tgt := of_decide_eq_true htarget
          have hd_lc2 := of_decide_eq_true hlc2
          have hd_blks := of_decide_eq_true hblks
          have h_if :
              (decide (dst.loc.index < activeBody.localCount) &&
               decide (target.index < activeBody.blocks.length) &&
               (instCallee.argTys.length == 1) &&
               decide (2 ≤ instCallee.localCount) &&
               decide (0 < instCallee.blocks.length)) = true := hcond5
          rw [h_if]
          dsimp
          rw [symEvalOperand_sound hmatch arg hop]
          dsimp [SymState.toMirState, SymStackFrame.toStackFrame]
          have hfid_ne : (st.nextFrameId == 0) = false := by
            have hpos := of_decide_eq_true hfid_pos
            exact beq_eq_false_iff_ne.mpr (by omega)
          rw [hfid_ne]
          have hidx : ¬ (false = true ∧ rootLC ≤ 1) := by
            intro ⟨hf, _⟩; cases hf
          have hcallee_loc :
              denoteLocals s₀ false rootLC
                (updateSymLocal (fun _ => none) 1 (some argVal)) =
              updateLocal (fun _ => none) 1 (some (argVal.denote s₀)) := by
            rw [denoteLocals_update_lt s₀ false rootLC (fun _ => none)
                  (some argVal) hidx]
            rfl
          rw [hcallee_loc]
          rfl
  | unwindResume | unwindTerminate | drop _ _ | switchIntGeneral _ _ _
  | call _ _ _ | tailCall _ | yield _ _ _ | coroutineDrop
  | falseEdge _ _ | falseUnwind _ | inlineAsm =>
    trivial

/-- Symbolic single-step transition of `rootBody` parameterized by
`symEvalConstBody`. -/
def symStepWith (rootLC : Nat) (adts : List AdtDecl) (bodies : List BodyDecl)
    (symEvalConstBody : MirBody → SymState → SymStepOut)
    (target : TargetLayout) (rootBody : MirBody) (st : SymState) :
    SymStepOut :=
  let active := st.curBody.getD rootBody
  match lookupAt active.blocks st.block with
  | none => .failed
  | some bb =>
    match lookupAt bb.stmts st.stmtIdx with
    | some stmt =>
      symEvalStmt rootLC active st stmt adts bodies symEvalConstBody target
    | none =>
      if st.stmtIdx == bb.stmts.length then
        symEvalTerminator rootLC adts bodies active st bb.terminator target
      else
        .failed

theorem symStepWith_sound {rootLC : Nat} {s₀ : MirState} {st : SymState}
    (hmatch : st.pc.Matches rootLC s₀) (adts : List AdtDecl)
    (bodies : List BodyDecl)
    (symEvalConstBody : MirBody → SymState → SymStepOut)
    (evalConstBody : MirBody → MirState → RawStep MirState MirReturn)
    (hconst : ∀ cBody,
      SymStepOut.Agrees cBody.localCount
        (constEntryState s₀.tySizes s₀.adtPad)
        (st.pc.forConstEval)
        (symEvalConstBody cBody (symConstEntryState st.pc))
        (evalConstBody cBody (constEntryState s₀.tySizes s₀.adtPad)))
    (target : TargetLayout) (rootBody : MirBody) :
    SymStepOut.Agrees rootLC s₀ st.pc
      (symStepWith rootLC adts bodies symEvalConstBody target rootBody st)
      (evalMirStepWith adts bodies evalConstBody target rootBody
        (st.toMirState rootLC s₀)) := by
  dsimp only [symStepWith, evalMirStepWith]
  have hcur : (st.toMirState rootLC s₀).curBody = st.curBody := rfl
  have hblk : (st.toMirState rootLC s₀).block = st.block := rfl
  have hidx : (st.toMirState rootLC s₀).stmtIdx = st.stmtIdx := rfl
  rw [hcur, hblk, hidx]
  cases hbb : lookupAt (st.curBody.getD rootBody).blocks st.block with
  | none => trivial
  | some bb =>
    dsimp
    cases hst : lookupAt bb.stmts st.stmtIdx with
    | some stmt =>
      dsimp
      exact symEvalStmt_sound hmatch (st.curBody.getD rootBody) stmt adts
        bodies symEvalConstBody evalConstBody hconst target
    | none =>
      dsimp
      cases heq : (st.stmtIdx == bb.stmts.length) with
      | false => trivial
      | true =>
        dsimp
        exact symEvalTerminator_sound hmatch adts bodies
          (st.curBody.getD rootBody) bb.terminator target

/-- Run `symStepFn` for at most `fuel` silent steps on `cBody` starting from
`cs`. -/
def symRunConstSteps (symStepFn : MirBody → SymState → SymStepOut) :
    Nat → MirBody → SymState → SymStepOut
  | 0, _, _ => .failed
  | fuel + 1, cBody, cs =>
    match symStepFn cBody cs with
    | .silent cs' => symRunConstSteps symStepFn fuel cBody cs'
    | out => out

theorem symRunConstSteps_sound {cLC : Nat} {sConst₀ : MirState} {pc₀ : PathCond}
    (symStepFn : MirBody → SymState → SymStepOut)
    (stepFn : MirBody → MirState → RawStep MirState MirReturn)
    (cBody : MirBody)
    (hstep : ∀ cs : SymState,
      cs.pc = pc₀ →
      SymStepOut.Agrees cLC sConst₀ pc₀
        (symStepFn cBody cs)
        (stepFn cBody (cs.toMirState cLC sConst₀))) :
    ∀ (fuel : Nat) (cs : SymState),
      cs.pc = pc₀ →
      SymStepOut.Agrees cLC sConst₀ pc₀
        (symRunConstSteps symStepFn fuel cBody cs)
        (runConstSteps stepFn fuel cBody (cs.toMirState cLC sConst₀))
  | 0, _, _ => trivial
  | fuel + 1, cs, hpc => by
    dsimp [symRunConstSteps, runConstSteps]
    have hs := hstep cs hpc
    cases hout : symStepFn cBody cs with
    | silent cs' =>
      rw [hout] at hs
      dsimp [SymStepOut.Agrees] at hs
      rw [hs.2]
      dsimp
      exact symRunConstSteps_sound symStepFn stepFn cBody hstep fuel cs' hs.1
    | returned retVal csTerm =>
      rw [hout] at hs
      dsimp [SymStepOut.Agrees] at hs ⊢
      refine ⟨hs.1, ?_⟩
      rw [hs.2]
    | unwind =>
      rw [hout] at hs
      dsimp [SymStepOut.Agrees] at hs ⊢
      rw [hs]
    | abort =>
      rw [hout] at hs
      dsimp [SymStepOut.Agrees] at hs ⊢
      rw [hs]
    | compileTimeError =>
      rw [hout] at hs
      dsimp [SymStepOut.Agrees] at hs ⊢
      rw [hs]
    | split _ => trivial
    | failed => trivial

/-- Symbolic `evalMirStepDepth` supporting up to `depth` nested constant
evaluations. Notice that each recursive constant body `cBody` runs with its own
`rootLC := cBody.localCount`. -/
def symStepDepth (adts : List AdtDecl) (bodies : List BodyDecl)
    (target : TargetLayout) :
    Nat → Nat → MirBody → SymState → SymStepOut
  | 0, rootLC, rootBody, st =>
    symStepWith rootLC adts bodies (fun _ _ => .failed) target rootBody st
  | depth + 1, rootLC, rootBody, st =>
    let symStepFn := fun cBody cs =>
      symStepDepth adts bodies target depth cBody.localCount cBody cs
    symStepWith rootLC adts bodies
      (symRunConstSteps symStepFn defaultConstFuel) target rootBody st

theorem symStepDepth_sound (adts : List AdtDecl) (bodies : List BodyDecl)
    (target : TargetLayout) :
    ∀ (depth rootLC : Nat) (s₀ : MirState) (rootBody : MirBody)
      (st : SymState),
      st.pc.Matches rootLC s₀ →
      SymStepOut.Agrees rootLC s₀ st.pc
        (symStepDepth adts bodies target depth rootLC rootBody st)
        (evalMirStepDepth adts bodies target depth rootBody
          (st.toMirState rootLC s₀))
  | 0, rootLC, s₀, rootBody, st, hmatch =>
    symStepWith_sound hmatch adts bodies
      (fun _ _ => .failed) (fun _ _ => .failed)
      (fun _ => trivial) target rootBody
  | depth + 1, rootLC, s₀, rootBody, st, hmatch => by
    dsimp [symStepDepth, evalMirStepDepth]
    refine symStepWith_sound hmatch adts bodies
      (symRunConstSteps
        (fun cBody cs =>
          symStepDepth adts bodies target depth cBody.localCount cBody cs)
        defaultConstFuel)
      (runConstSteps (evalMirStepDepth adts bodies target depth)
        defaultConstFuel)
      ?_ target rootBody
    intro cBody
    have hmatch_c :
        (st.pc.forConstEval).Matches cBody.localCount
          (constEntryState s₀.tySizes s₀.adtPad) :=
      forConstEval_matches hmatch cBody.localCount
    have hrun :=
      symRunConstSteps_sound
        (symStepFn := fun cb cs =>
          symStepDepth adts bodies target depth cb.localCount cb cs)
        (stepFn := evalMirStepDepth adts bodies target depth)
        cBody
        (fun cs hpc => by
          have hm :
              cs.pc.Matches cBody.localCount
                (constEntryState s₀.tySizes s₀.adtPad) := by
            rw [hpc]; exact hmatch_c
          have hd :=
            symStepDepth_sound adts bodies target depth cBody.localCount
              (constEntryState s₀.tySizes s₀.adtPad) cBody cs hm
          rw [hpc] at hd
          exact hd)
        defaultConstFuel
        (symConstEntryState st.pc)
        rfl
    rw [symConstEntryState_toMirState s₀ st.pc cBody.localCount] at hrun
    exact hrun

/-- Symbolic single-step transition function of a `MirBody` under `adts`,
`bodies`, and `target`. -/
def symStep (rootLC : Nat) (adts : List AdtDecl)
    (bodies : List BodyDecl := []) (rootBody : MirBody) (st : SymState)
    (target : TargetLayout := defaultTargetLayout) : SymStepOut :=
  symStepDepth adts bodies target 2 rootLC rootBody st

theorem symStep_sound {rootLC : Nat} {s₀ : MirState} {st : SymState}
    (hmatch : st.pc.Matches rootLC s₀) (adts : List AdtDecl)
    (bodies : List BodyDecl) (rootBody : MirBody)
    (target : TargetLayout := defaultTargetLayout) :
    SymStepOut.Agrees rootLC s₀ st.pc
      (symStep rootLC adts bodies rootBody st target)
      (evalMirStep adts bodies rootBody (st.toMirState rootLC s₀) target) :=
  symStepDepth_sound adts bodies target 2 rootLC s₀ rootBody st hmatch

/-- Fuel-bounded reflective symbolic execution engine over `symStep` and
`applySplit`. -/
def symExecFuel (rootLC : Nat) (adts : List AdtDecl) (bodies : List BodyDecl)
    (rootBody : MirBody) (specs : List PostSpec) (allowGuard : Bool)
    (target : TargetLayout := defaultTargetLayout) :
    Nat → SymState → Bool
  | 0, _ => false
  | fuel + 1, st =>
    match symStep rootLC adts bodies rootBody st target with
    | .silent st' =>
      symExecFuel rootLC adts bodies rootBody specs allowGuard target fuel st'
    | .returned retVal stTerm =>
      symCheckValid rootLC adts stTerm rootBody.retTy retVal &&
      symCheckSpecs stTerm.pc specs retVal
    | .unwind | .abort => true
    | .compileTimeError =>
      allowGuard && st.pc.refutesPinnedWorld
    | .split sp =>
      let p := applySplit st.pc sp
      symExecFuel rootLC adts bodies rootBody specs allowGuard target fuel
        { st with pc := p.1 } &&
      symExecFuel rootLC adts bodies rootBody specs allowGuard target fuel
        { st with pc := p.2 }
    | .failed => false

theorem holdsPostSpecs_of_symCheckSpecs {rootLC : Nat} {s₀ : MirState}
    {pc : PathCond} (hmatch : pc.Matches rootLC s₀) (specs : List PostSpec)
    (retVal : SymVal) (sTerm : MirState)
    (h : symCheckSpecs pc specs retVal = true) :
    HoldsPostSpecs specs s₀ ⟨retVal.denote s₀, sTerm⟩ := by
  unfold HoldsPostSpecs
  induction specs with
  | nil => exact True.intro
  | cons spec rest ih =>
    have hall := symCheckSpecs_sound hmatch (spec :: rest) retVal h
    dsimp [symCheckSpecs, List.all] at h
    rcases Bool.and_eq_true_iff.mp h with ⟨_, hrest⟩
    cases spec with
    | ensuresEqArg argLocal =>
      dsimp [List.map, AllHold]
      exact ⟨hall (.ensuresEqArg argLocal) (.head _), ih hrest⟩

theorem symExecFuel_sound (rootLC : Nat) (adts : List AdtDecl)
    (bodies : List BodyDecl) (rootBody : MirBody) (specs : List PostSpec)
    (allowGuard : Bool) (s₀ : MirState) :
    ∀ (fuel : Nat) (st : SymState),
      st.pc.Matches rootLC s₀ →
      symExecFuel rootLC adts bodies rootBody specs allowGuard
        defaultTargetLayout fuel st = true →
      ExecSafePost adts bodies rootBody
        (allowGuard = true ∧
          ¬ (s₀.adtPad = (fun _ => 0) ∧ s₀.tySizes = (fun _ => 8)))
        (fun r =>
          r.value.valid adts (denoteAdtInv adts) r.state rootLC rootBody.retTy ∧
          HoldsPostSpecs specs s₀ r)
        (st.toMirState rootLC s₀)
  | 0, _, _, h => by cases h
  | fuel + 1, st, hmatch, h => by
    dsimp [symExecFuel] at h
    have hs := symStep_sound hmatch adts bodies rootBody defaultTargetLayout
    cases hout : symStep rootLC adts bodies rootBody st defaultTargetLayout with
    | silent st' =>
      rw [hout] at hs h
      dsimp [SymStepOut.Agrees] at hs
      have hmatch' : st'.pc.Matches rootLC s₀ := by
        rw [hs.1]; exact hmatch
      exact .step hs.2
        (symExecFuel_sound rootLC adts bodies rootBody specs allowGuard s₀
          fuel st' hmatch' h)
    | returned retVal stTerm =>
      rw [hout] at hs h
      dsimp [SymStepOut.Agrees] at hs
      rcases Bool.and_eq_true_iff.mp h with ⟨hval, hsp⟩
      have hmatchTerm : stTerm.pc.Matches rootLC s₀ := by
        rw [hs.1]; exact hmatch
      exact .normal hs.2
        ⟨symCheckValid_sound hmatchTerm adts rootBody.retTy retVal hval,
         holdsPostSpecs_of_symCheckSpecs hmatchTerm specs retVal
           (stTerm.toMirState rootLC s₀) hsp⟩
    | unwind =>
      rw [hout] at hs
      dsimp [SymStepOut.Agrees] at hs
      exact .unwind hs
    | abort =>
      rw [hout] at hs
      dsimp [SymStepOut.Agrees] at hs
      exact .abort hs
    | compileTimeError =>
      rw [hout] at hs h
      dsimp [SymStepOut.Agrees] at hs
      rcases Bool.and_eq_true_iff.mp h with ⟨hallow, href⟩
      exact .compileTimeError hs ⟨hallow, refutesPinnedWorld_sound hmatch href⟩
    | split sp =>
      rw [hout] at h
      dsimp at h
      rcases Bool.and_eq_true_iff.mp h with ⟨h1, h2⟩
      cases applySplit_complete rootLC s₀ st.pc sp hmatch with
      | inl hm1 =>
        exact symExecFuel_sound rootLC adts bodies rootBody specs allowGuard s₀
          fuel { st with pc := (applySplit st.pc sp).1 } hm1 h1
      | inr hm2 =>
        exact symExecFuel_sound rootLC adts bodies rootBody specs allowGuard s₀
          fuel { st with pc := (applySplit st.pc sp).2 } hm2 h2
    | failed =>
      rw [hout] at h
      cases h

/-!
## Section 6: Reflective Symbolic Verification Canaries (Replacing Hardcoded AST Templates)
-/

/-- Helper to build an initial symbolic state for a 1-argument `usize` function
(`_1 = .usize (.var (1, []))`). -/
def initSymStateUsize1 : SymState where
  block := 0
  stmtIdx := 0
  locals := updateSymLocal (fun _ => none) 1 (some (.usize (.var (1, []))))
  curBody := none
  stack := []
  frameId := 0
  nextFrameId := 1
  localGens := fun _ => 0
  pc := { initArgs := [(1, .usize (.var (1, [])))] }

/-- **Test 1**: `pub fn id(x: usize) -> usize { x }` with `EnsuresEqArg 1`,
verified by reflective symbolic execution (`rfl`) without any hardcoded AST
equality template. -/
def bodyIdUsize : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, []⟩))]
      terminator := .return_ }
  ]

theorem test1_id_usize_sym_verified :
    symExecFuel 2 [] [] bodyIdUsize [.ensuresEqArg 1] false
      defaultTargetLayout 4 initSymStateUsize1 = true := rfl

theorem test1_id_usize_execSafePost (s₀ : MirState)
    (hmatch : initSymStateUsize1.pc.Matches 2 s₀) :
    ExecSafePost [] [] bodyIdUsize
      (false = true ∧ ¬ (s₀.adtPad = (fun _ => 0) ∧ s₀.tySizes = (fun _ => 8)))
      (fun r =>
        r.value.valid [] (denoteAdtInv []) r.state 2 bodyIdUsize.retTy ∧
        HoldsPostSpecs [.ensuresEqArg 1] s₀ r)
      (initSymStateUsize1.toMirState 2 s₀) :=
  symExecFuel_sound 2 [] [] bodyIdUsize [.ensuresEqArg 1] false s₀ 4
    initSymStateUsize1 hmatch test1_id_usize_sym_verified

/-- **Test 2**: `#[repr(Rust)] struct Wrapper(usize)` transmuted to `usize` via
`callTransmuteCopy` after a compile-time `Stmt.evalConst` layout guard
(`const { assert!(size_of::<Wrapper>() == 8) }`). The symbolic evaluator
automatically case-splits on `adtPad 0`:
- On the `adtPad 0 = 0` branch, the `const` guard returns `.unit` and
  `callTransmuteCopy` succeeds.
- On the `adtPad 0 > 0` branch, the `const` guard panics cleanly, stepping the
  enclosing function to `.compileTimeError` with `refutesPinnedWorld = true`. -/
def adtWrapper : AdtDecl where
  id := 0
  fields := [{ ty := .usize, access := .pubSafe }]
  repr := .rust
  invariant := none

def constSizeGuardBody : MirBody where
  argTys := []
  retTy := .unit
  localCount := 3
  blocks := [
    { stmts := []
      terminator := .callLayout ⟨⟨1⟩, []⟩ (.sizeOf (.adt 0)) ⟨1⟩ },
    { stmts := [
        .assign ⟨⟨2⟩, []⟩
          (.binaryOp .eq (.copy ⟨⟨1⟩, []⟩) (.constVal (.usize 8))),
        .assign ⟨⟨0⟩, []⟩ (.use (.constVal .unit))
      ]
      terminator := .assert (.copy ⟨⟨2⟩, []⟩) true ⟨2⟩ .unwind false },
    { stmts := []
      terminator := .return_ }
  ]

def bodyGuardedTransmute : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 5
  blocks := [
    { stmts := [
        .evalConst ⟨⟨2⟩, []⟩ ⟨0⟩ [],
        .assign ⟨⟨3⟩, []⟩ (.aggregate 0 (.copy ⟨⟨1⟩, []⟩)),
        .assign ⟨⟨4⟩, []⟩ (.ref ⟨⟨3⟩, []⟩)
      ]
      terminator :=
        .callTransmuteCopy ⟨⟨0⟩, []⟩ (.adt 0) .usize
          (.move ⟨⟨4⟩, []⟩) ⟨1⟩ },
    { stmts := []
      terminator := .return_ }
  ]

theorem test2_guarded_transmute_sym_verified :
    symExecFuel 5 [adtWrapper] [{ id := ⟨0⟩, body := constSizeGuardBody }]
      bodyGuardedTransmute [.ensuresEqArg 1] true
      defaultTargetLayout 12 initSymStateUsize1 = true := rfl

theorem test2_guarded_transmute_execSafePost (s₀ : MirState)
    (hmatch : initSymStateUsize1.pc.Matches 5 s₀) :
    ExecSafePost [adtWrapper] [{ id := ⟨0⟩, body := constSizeGuardBody }]
      bodyGuardedTransmute
      (true = true ∧ ¬ (s₀.adtPad = (fun _ => 0) ∧ s₀.tySizes = (fun _ => 8)))
      (fun r =>
        r.value.valid [adtWrapper] (denoteAdtInv [adtWrapper]) r.state 5
          bodyGuardedTransmute.retTy ∧
        HoldsPostSpecs [.ensuresEqArg 1] s₀ r)
      (initSymStateUsize1.toMirState 5 s₀) :=
  symExecFuel_sound 5 [adtWrapper] [{ id := ⟨0⟩, body := constSizeGuardBody }]
    bodyGuardedTransmute [.ensuresEqArg 1] true s₀ 12
    initSymStateUsize1 hmatch test2_guarded_transmute_sym_verified

/-- **Test 3**: Multi-block diamond branching CFG (`bb0 -> bb1 / bb2 -> bb3`)
that branches on `x == 0`, assigns `_0` in both arms, joins at `bb3`, and
returns `_0`. Verified by `rfl` on `symExecFuel` via automatic `.varVal`
splitting. -/
def bodyDiamondCfg : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 3
  blocks := [
    { stmts := [
        .assign ⟨⟨2⟩, []⟩
          (.binaryOp .eq (.copy ⟨⟨1⟩, []⟩) (.constVal (.usize 0)))
      ]
      terminator := .switchInt (.copy ⟨⟨2⟩, []⟩) ⟨1⟩ ⟨2⟩ },
    { stmts := [.assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨1⟩, []⟩))]
      terminator := .goto ⟨3⟩ },
    { stmts := [.assign ⟨⟨0⟩, []⟩ (.use (.constVal (.usize 42)))]
      terminator := .goto ⟨3⟩ },
    { stmts := [.nop]
      terminator := .return_ }
  ]

theorem test3_diamond_cfg_sym_verified :
    symExecFuel 3 [] [] bodyDiamondCfg [] false
      defaultTargetLayout 10 initSymStateUsize1 = true := rfl

/-- **Test 4**: `NonZeroUsize` constructor (`assert!(x != 0); NonZeroUsize(x)`)
with library representation invariant `x != 0`:
- When `x == 0`, the assertion fails and unwinds cleanly (`.unwind`).
- When `x != 0`, `pc.varNe` records `((1, []), 0)`, and `symCheckValid` uses
  `symCheckAdtInv` to discharge the non-zero representation invariant on the
  returned `.adt 1 (.usize (.var (1, [])))`! -/
def adtNonZeroUsize : AdtDecl where
  id := 1
  fields := [{ ty := .usize, access := .priv }]
  repr := .transparent
  invariant := some { ne := 0 }

def bodyNonZeroNewChecked : MirBody where
  argTys := [.usize]
  retTy := .adt 1
  localCount := 3
  blocks := [
    { stmts := [
        .assign ⟨⟨2⟩, []⟩
          (.binaryOp .ne (.copy ⟨⟨1⟩, []⟩) (.constVal (.usize 0)))
      ]
      terminator := .assert (.copy ⟨⟨2⟩, []⟩) true ⟨1⟩ .unwind false },
    { stmts := [
        .assign ⟨⟨0⟩, []⟩ (.aggregate 1 (.copy ⟨⟨1⟩, []⟩))
      ]
      terminator := .return_ }
  ]

theorem test4_nonZero_new_sym_verified :
    symExecFuel 3 [adtNonZeroUsize] [] bodyNonZeroNewChecked [] false
      defaultTargetLayout 10 initSymStateUsize1 = true := rfl

theorem test4_nonZero_new_execSafePost (s₀ : MirState)
    (hmatch : initSymStateUsize1.pc.Matches 3 s₀) :
    ExecSafePost [adtNonZeroUsize] [] bodyNonZeroNewChecked
      (false = true ∧ ¬ (s₀.adtPad = (fun _ => 0) ∧ s₀.tySizes = (fun _ => 8)))
      (fun r =>
        r.value.valid [adtNonZeroUsize] (denoteAdtInv [adtNonZeroUsize])
          r.state 3 bodyNonZeroNewChecked.retTy ∧
        HoldsPostSpecs [] s₀ r)
      (initSymStateUsize1.toMirState 3 s₀) :=
  symExecFuel_sound 3 [adtNonZeroUsize] [] bodyNonZeroNewChecked [] false s₀ 10
    initSymStateUsize1 hmatch test4_nonZero_new_sym_verified

/-- **Test 5**: Interprocedural `Terminator.call1` stepping into a helper
function `bodyIdUsize` on the symbolic call stack (`SymStackFrame`), returning
to the caller's continuation block, and satisfying `EnsuresEqArg 1`. -/
def bodyCallerWithHelper : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 3
  blocks := [
    { stmts := []
      terminator := .call1 ⟨⟨2⟩, []⟩ ⟨0⟩ (.copy ⟨⟨1⟩, []⟩) ⟨1⟩ [] },
    { stmts := [.assign ⟨⟨0⟩, []⟩ (.use (.copy ⟨⟨2⟩, []⟩))]
      terminator := .return_ }
  ]

theorem test5_interprocedural_call1_sym_verified :
    symExecFuel 3 [] [{ id := ⟨0⟩, body := bodyIdUsize }] bodyCallerWithHelper
      [.ensuresEqArg 1] false defaultTargetLayout 10 initSymStateUsize1 =
      true := rfl

theorem test5_interprocedural_call1_execSafePost (s₀ : MirState)
    (hmatch : initSymStateUsize1.pc.Matches 3 s₀) :
    ExecSafePost [] [{ id := ⟨0⟩, body := bodyIdUsize }] bodyCallerWithHelper
      (false = true ∧ ¬ (s₀.adtPad = (fun _ => 0) ∧ s₀.tySizes = (fun _ => 8)))
      (fun r =>
        r.value.valid [] (denoteAdtInv []) r.state 3
          bodyCallerWithHelper.retTy ∧
        HoldsPostSpecs [.ensuresEqArg 1] s₀ r)
      (initSymStateUsize1.toMirState 3 s₀) :=
  symExecFuel_sound 3 [] [{ id := ⟨0⟩, body := bodyIdUsize }] bodyCallerWithHelper
    [.ensuresEqArg 1] false s₀ 10 initSymStateUsize1 hmatch
    test5_interprocedural_call1_sym_verified

end Anneal.SymEval

#print axioms Anneal.SymEval.symStep_sound
#print axioms Anneal.SymEval.symExecFuel_sound
#print axioms Anneal.SymEval.test1_id_usize_execSafePost
#print axioms Anneal.SymEval.test2_guarded_transmute_execSafePost
#print axioms Anneal.SymEval.test3_diamond_cfg_sym_verified
#print axioms Anneal.SymEval.test4_nonZero_new_execSafePost
#print axioms Anneal.SymEval.test5_interprocedural_call1_execSafePost
