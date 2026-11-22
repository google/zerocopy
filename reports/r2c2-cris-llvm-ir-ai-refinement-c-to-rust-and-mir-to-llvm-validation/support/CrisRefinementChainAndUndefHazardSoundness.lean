/-
CrisRefinementChainAndUndefHazardSoundness.lean

A self-contained Lean 4 model written for one reference report.  It mechanizes
three things about refinement-based translation validation at the LLVM IR level:

  Part 1-2  a trace-set semantics for a finite fragment of event trees with the
            `Choose` / `Take` / `Assume` / `Guarantee` / `UB` / `NB` events, the
            cancellation of a caller-side `Guarantee` against a callee-side
            `Assume`, inlining of library calls (`Hide`), and the composition of
            the four-step refinement chain into one remaining obligation;
  Part 3    why rewriting `undef` to `poison` on the source side, or to zero on
            the target side, can validate a wrong translation, and why rewriting
            it to an explicit choice cannot;
  Part 4    why validating against compiled source IR is sound but incomplete
            for source-level correctness, and why ignoring `noundef` is harmless
            on the source side and unsound on the target side.

Scope and honesty notes.

* This is an abstract model.  It imports nothing from Vellvm, CRIS, Interaction
  Trees, R2C2, or Anneal, and it is not a port of any Rocq development.  Its
  theorems are statements about the definitions in this file.
* Event trees here are inductive (well-founded), so they describe terminating
  computations only.  The coinductive trees of the modelled systems also
  describe divergence; nothing here speaks about divergence.
* Module linking is modelled for a layered, non-recursive fragment: a context
  calls a module `M`, `M` calls a library `L`, and no body calls itself.
* `import Lean` is needed only by the audit command at the end of the file.
  Every definition and theorem in namespace `CrisModel` uses core `Init` only.
* Every `def` in namespace `CrisModel` is marked `noncomputable`.  With Lean
  4.34.1 a compiled structurally recursive definition, including a `Prop`-valued
  one, comes with an `unsafe` code-generation helper named `<name>._unsafe_rec`.
  Suppressing code generation keeps the environment free of such helpers; the
  audit at the end of the file fails if one is present.
-/
import Lean

set_option autoImplicit false

namespace CrisModel

/-! ## Part 0.  Traces and behaviors -/

/-- A finite trace: a sequence of observable interactions ending in a result.
`interact f a r rest` records a call to environment operation `f` with argument
`a` and response `r`. -/
inductive Trace (V : Type) : Type where
  | done : V → Trace V
  | interact : Nat → V → V → Trace V → Trace V

/-- A behavior is a set of traces. -/
noncomputable def Beh (V : Type) : Type := Trace V → Prop

/-- Behavioral refinement: every trace on the left is a trace on the right. -/
noncomputable def Beh.le {V : Type} (A B : Beh V) : Prop := ∀ t : Trace V, A t → B t

/-- The behavior of undefined behavior: every trace. -/
noncomputable def Beh.top (V : Type) : Beh V := fun _ => True

/-- The behavior of "no behavior": no trace. -/
noncomputable def Beh.bot (V : Type) : Beh V := fun _ => False

theorem Beh.le_refl {V : Type} (A : Beh V) : Beh.le A A := fun _ h => h

theorem Beh.le_trans {V : Type} {A B C : Beh V}
    (h₁ : Beh.le A B) (h₂ : Beh.le B C) : Beh.le A C :=
  fun t h => h₂ t (h₁ t h)

theorem Beh.le_top {V : Type} (A : Beh V) : Beh.le A (Beh.top V) :=
  fun _ _ => True.intro

theorem Beh.bot_le {V : Type} (A : Beh V) : Beh.le (Beh.bot V) A :=
  fun _ h => False.elim h

/-! ## Part 1.  Event trees and their trace sets -/

/-- A finite event tree over values `V`.

* `io f a k`      observable interaction; the environment answers with any value.
* `choose X k`    demonic choice of a value satisfying `X` (union of behaviors).
* `take X k`      angelic choice of a value satisfying `X` (intersection).
* `ub`            undefined behavior (every trace).
* `nb`            no behavior (no trace).
* `assume Q p`    continue if `Q`, otherwise behave as `ub`.
* `guarantee Q p` continue if `Q`, otherwise behave as `nb`.
* `call f a k`    call to a named function; left unresolved it behaves as `ub`.
-/
inductive Prog (V : Type) : Type where
  | ret : V → Prog V
  | tau : Prog V → Prog V
  | io : Nat → V → (V → Prog V) → Prog V
  | choose : (V → Prop) → (V → Prog V) → Prog V
  | take : (V → Prop) → (V → Prog V) → Prog V
  | ub : Prog V
  | nb : Prog V
  | assume : Prop → Prog V → Prog V
  | guarantee : Prop → Prog V → Prog V
  | call : Nat → V → (V → Prog V) → Prog V

/-- The set of traces of an event tree.

`assume Q p` is rendered as `Q → …` and `guarantee Q p` as `Q ∧ …`.  For a
decidable `Q` these agree with "if `Q` then the continuation, else every trace"
and "if `Q` then the continuation, else no trace" respectively. -/
noncomputable def beh {V : Type} : Prog V → Trace V → Prop
  | Prog.ret v, t => t = Trace.done v
  | Prog.tau p, t => beh p t
  | Prog.io f a k, t => ∃ r rest, t = Trace.interact f a r rest ∧ beh (k r) rest
  | Prog.choose X k, t => ∃ x, X x ∧ beh (k x) t
  | Prog.take X k, t => ∀ x, X x → beh (k x) t
  | Prog.ub, _ => True
  | Prog.nb, _ => False
  | Prog.assume Q p, t => Q → beh p t
  | Prog.guarantee Q p, t => Q ∧ beh p t
  | Prog.call _ _ _, _ => True

/-- Sequential composition of event trees. -/
noncomputable def bind {V : Type} : Prog V → (V → Prog V) → Prog V
  | Prog.ret v, k => k v
  | Prog.tau p, k => Prog.tau (bind p k)
  | Prog.io f a h, k => Prog.io f a (fun r => bind (h r) k)
  | Prog.choose X h, k => Prog.choose X (fun x => bind (h x) k)
  | Prog.take X h, k => Prog.take X (fun x => bind (h x) k)
  | Prog.ub, _ => Prog.ub
  | Prog.nb, _ => Prog.nb
  | Prog.assume Q p, k => Prog.assume Q (bind p k)
  | Prog.guarantee Q p, k => Prog.guarantee Q (bind p k)
  | Prog.call f a h, k => Prog.call f a (fun r => bind (h r) k)

/-- `beh` is monotone in the continuation of a `bind`. -/
theorem beh_bind_mono {V : Type} (p : Prog V) (k₁ k₂ : V → Prog V)
    (h : ∀ v, Beh.le (beh (k₁ v)) (beh (k₂ v))) :
    Beh.le (beh (bind p k₁)) (beh (bind p k₂)) := by
  induction p with
  | ret v => exact h v
  | tau p ih => exact ih
  | io f a g ih =>
      intro t ht
      obtain ⟨r, rest, hEq, hB⟩ := ht
      exact ⟨r, rest, hEq, ih r rest hB⟩
  | choose X g ih =>
      intro t ht
      obtain ⟨x, hx, hB⟩ := ht
      exact ⟨x, hx, ih x t hB⟩
  | take X g ih =>
      intro t ht x hx
      exact ih x t (ht x hx)
  | ub => intro _ _; exact True.intro
  | nb => intro _ ht; exact ht
  | assume Q p ih =>
      intro t ht hQ
      exact ih t (ht hQ)
  | guarantee Q p ih =>
      intro t ht
      exact ⟨ht.1, ih t ht.2⟩
  | call f a g _ => intro _ _; exact True.intro

/-- Associativity of `bind`. -/
theorem bind_assoc {V : Type} (p : Prog V) (g k : V → Prog V) :
    bind (bind p g) k = bind p (fun v => bind (g v) k) := by
  induction p with
  | ret v => rfl
  | tau p ih => exact congrArg Prog.tau ih
  | io f a h ih => exact congrArg (Prog.io f a) (funext ih)
  | choose X h ih => exact congrArg (Prog.choose X) (funext ih)
  | take X h ih => exact congrArg (Prog.take X) (funext ih)
  | ub => rfl
  | nb => rfl
  | assume Q p ih => exact congrArg (Prog.assume Q) ih
  | guarantee Q p ih => exact congrArg (Prog.guarantee Q) ih
  | call f a h ih => exact congrArg (Prog.call f a) (funext ih)

/-! ### The `Assume` / `Guarantee` algebra -/

/-- A `Guarantee` immediately followed by an `Assume` of the same assertion
cancels: the pair adds no behavior. -/
theorem guarantee_assume_cancel {V : Type} (Q : Prop) (p : Prog V) :
    Beh.le (beh (Prog.guarantee Q (Prog.assume Q p))) (beh p) :=
  fun _ ht => ht.2 ht.1

/-- Inserting an `Assume` can only add behaviors. -/
theorem assume_weakens {V : Type} (Q : Prop) (p : Prog V) :
    Beh.le (beh p) (beh (Prog.assume Q p)) :=
  fun _ ht _ => ht

/-- Inserting a `Guarantee` can only remove behaviors. -/
theorem guarantee_strengthens {V : Type} (Q : Prop) (p : Prog V) :
    Beh.le (beh (Prog.guarantee Q p)) (beh p) :=
  fun _ ht => ht.2

/-- An `Assume` whose assertion holds is transparent.  This is the shape of the
side condition "the precondition of the entry holds at the start". -/
theorem assume_of_holds {V : Type} (Q : Prop) (p : Prog V) (hQ : Q) :
    Beh.le (beh (Prog.assume Q p)) (beh p) :=
  fun _ ht => ht hQ

/-- A `Guarantee` whose assertion holds is transparent. -/
theorem guarantee_of_holds {V : Type} (Q : Prop) (p : Prog V) (hQ : Q) :
    Beh.le (beh p) (beh (Prog.guarantee Q p)) :=
  fun _ ht => ⟨hQ, ht⟩

/-- A `Guarantee` that cannot be met has no behavior at all, so it refines every
program.  A target containing such a `Guarantee` would refine any source
vacuously; this is why the direction in which wrappers are inserted matters. -/
theorem guarantee_unmet_refines_anything {V : Type} (Q : Prop) (p q : Prog V)
    (hQ : ¬ Q) : Beh.le (beh (Prog.guarantee Q p)) (beh q) :=
  fun _ ht => False.elim (hQ ht.1)

/-- An `Assume` that fails is undefined behavior, so every program refines it. -/
theorem anything_refines_assume_unmet {V : Type} (Q : Prop) (p q : Prog V)
    (hQ : ¬ Q) : Beh.le (beh q) (beh (Prog.assume Q p)) :=
  fun _ _ hq => False.elim (hQ hq)

/-- One call boundary after both wrappers are applied and the callee is inlined.

The caller side (the wrapper around a call) chooses a ghost value `x`,
guarantees the callee's precondition `P x a`, and after the call assumes the
postcondition `Q x r`.  The callee side (the wrapper around a function body)
takes a ghost value `x'`, assumes `P x' a`, runs the body, and guarantees
`Q x' r`.  `G` restricts the ghost values. -/
noncomputable def wrappedCall {V : Type} (G : V → Prop) (P : V → V → Prop) (Q : V → V → Prop)
    (a : V) (body : Prog V) (k : V → Prog V) : Prog V :=
  Prog.choose G (fun x =>
  Prog.guarantee (P x a) (
  Prog.take G (fun x' =>
  Prog.assume (P x' a) (
  bind body (fun r =>
  Prog.guarantee (Q x' r) (
  Prog.assume (Q x r) (
  k r)))))))

/-- Cancellation at one call boundary: the doubly wrapped call refines the
unwrapped call.  The caller's `Guarantee` meets the callee's `Assume` for the
precondition, and the callee's `Guarantee` meets the caller's `Assume` for the
postcondition. -/
theorem wrapper_cancellation_at_call {V : Type} (G : V → Prop)
    (P : V → V → Prop) (Q : V → V → Prop) (a : V) (body : Prog V)
    (k : V → Prog V) :
    Beh.le (beh (wrappedCall G P Q a body k)) (beh (bind body k)) := by
  intro t ht
  obtain ⟨x, hG, hP, hTake⟩ := ht
  have hInner : beh (bind body (fun r =>
      Prog.guarantee (Q x r) (Prog.assume (Q x r) (k r)))) t := hTake x hG hP
  exact beh_bind_mono body _ k
    (fun r => guarantee_assume_cancel (Q x r) (k r)) t hInner

/-- If no ghost value satisfies the precondition, the wrapped call has no
behavior: the caller's `Guarantee` cannot be met. -/
theorem wrappedCall_unsatisfiable_pre_is_nb {V : Type} (G : V → Prop)
    (P : V → V → Prop) (Q : V → V → Prop) (a : V) (body : Prog V)
    (k : V → Prog V) (hNo : ∀ x, G x → ¬ P x a) :
    Beh.le (beh (wrappedCall G P Q a body k)) (Beh.bot V) := by
  intro t ht
  obtain ⟨x, hG, hP, _⟩ := ht
  exact hNo x hG hP

/-! ## Part 2.  Modules, inlining, and the four-step chain -/

/-- A module is a partial map from function names to bodies. -/
noncomputable def Mod (V : Type) : Type := Nat → Option (V → Prog V)

/-- Linking: the union of two modules, the left one taking precedence. -/
noncomputable def Mod.link {V : Type} (M L : Mod V) : Mod V :=
  fun f => match M f with
    | some b => some b
    | none => L f

/-- Replace every call to a function defined in `L` by the body of that function. -/
noncomputable def inline {V : Type} (L : Mod V) : Prog V → Prog V
  | Prog.ret v => Prog.ret v
  | Prog.tau p => Prog.tau (inline L p)
  | Prog.io f a k => Prog.io f a (fun r => inline L (k r))
  | Prog.choose X k => Prog.choose X (fun x => inline L (k x))
  | Prog.take X k => Prog.take X (fun x => inline L (k x))
  | Prog.ub => Prog.ub
  | Prog.nb => Prog.nb
  | Prog.assume Q p => Prog.assume Q (inline L p)
  | Prog.guarantee Q p => Prog.guarantee Q (inline L p)
  | Prog.call f a k =>
      match L f with
      | some body => bind (body a) (fun r => inline L (k r))
      | none => Prog.call f a (fun r => inline L (k r))

/-- `hide M L`: keep only the functions of `M`, with every call into `L`
replaced by the callee's body. -/
noncomputable def hide {V : Type} (M L : Mod V) : Mod V :=
  fun f => match M f with
    | some b => some (fun a => inline L (b a))
    | none => none

/-- `inline` at a call whose callee is defined in `L`. -/
theorem inline_call_some {V : Type} (L : Mod V) (f : Nat) (a : V) (k : V → Prog V)
    (body : V → Prog V) (h : L f = some body) :
    inline L (Prog.call f a k) = bind (body a) (fun r => inline L (k r)) := by
  rw [inline, h]

/-- `inline` at a call whose callee is not defined in `L`. -/
theorem inline_call_none {V : Type} (L : Mod V) (f : Nat) (a : V) (k : V → Prog V)
    (h : L f = none) :
    inline L (Prog.call f a k) = Prog.call f a (fun r => inline L (k r)) := by
  rw [inline, h]

/-- Inlining commutes with sequential composition. -/
theorem inline_bind {V : Type} (L : Mod V) (p : Prog V) (k : V → Prog V) :
    inline L (bind p k) = bind (inline L p) (fun v => inline L (k v)) := by
  induction p with
  | ret v => rfl
  | tau p ih => exact congrArg Prog.tau ih
  | io f a h ih => exact congrArg (Prog.io f a) (funext ih)
  | choose X h ih => exact congrArg (Prog.choose X) (funext ih)
  | take X h ih => exact congrArg (Prog.take X) (funext ih)
  | ub => rfl
  | nb => rfl
  | assume Q p ih => exact congrArg (Prog.assume Q) ih
  | guarantee Q p ih => exact congrArg (Prog.guarantee Q) ih
  | call f a h ih =>
      have hStep : bind (Prog.call f a h) k = Prog.call f a (fun r => bind (h r) k) := rfl
      rw [hStep]
      cases hL : L f with
      | none =>
          rw [inline_call_none L f a (fun r => bind (h r) k) hL, inline_call_none L f a h hL]
          exact congrArg (Prog.call f a) (funext ih)
      | some body =>
          rw [inline_call_some L f a (fun r => bind (h r) k) body hL,
            inline_call_some L f a h body hL, bind_assoc]
          exact congrArg (bind (body a)) (funext ih)

/-- Inlining (step 1 of the chain) for the layered fragment.

A context `c` may call functions of `M` and of `L`.  On the left the context is
linked with both: calls into `M` are resolved, then calls into `L`.  On the
right the context is linked with `hide M L` only, so a direct call from the
context into `L` stays unresolved and is undefined behavior, which admits every
trace.  Hence the left side refines the right side for every context. -/
theorem inlining_refines_hide {V : Type} (M L : Mod V) (c : Prog V) :
    Beh.le (beh (inline L (inline M c))) (beh (inline (hide M L) c)) := by
  induction c with
  | ret v => exact Beh.le_refl _
  | tau p ih => exact ih
  | io f a g ih =>
      intro t ht
      obtain ⟨r, rest, hEq, hB⟩ := ht
      exact ⟨r, rest, hEq, ih r rest hB⟩
  | choose X g ih =>
      intro t ht
      obtain ⟨x, hx, hB⟩ := ht
      exact ⟨x, hx, ih x t hB⟩
  | take X g ih =>
      intro t ht x hx
      exact ih x t (ht x hx)
  | ub => exact Beh.le_refl _
  | nb => exact Beh.le_refl _
  | assume Q p ih =>
      intro t ht hQ
      exact ih t (ht hQ)
  | guarantee Q p ih =>
      intro t ht
      exact ⟨ht.1, ih t ht.2⟩
  | call f a g ih =>
      cases hM : M f with
      | none =>
          have hH : hide M L f = none := by
            unfold hide
            rw [hM]
          rw [inline_call_none (hide M L) f a g hH]
          intro _ _
          exact True.intro
      | some b =>
          have hH : hide M L f = some (fun x => inline L (b x)) := by
            unfold hide
            rw [hM]
          rw [inline_call_some (hide M L) f a g (fun x => inline L (b x)) hH,
            inline_call_some M f a g b hM, inline_bind]
          exact beh_bind_mono (inline L (b a)) _ _ ih

/-- No call in the tree targets a function defined in `M`. -/
noncomputable def noCallsTo {V : Type} (M : Mod V) : Prog V → Prop
  | Prog.ret _ => True
  | Prog.tau p => noCallsTo M p
  | Prog.io _ _ k => ∀ r, noCallsTo M (k r)
  | Prog.choose _ k => ∀ x, noCallsTo M (k x)
  | Prog.take _ k => ∀ x, noCallsTo M (k x)
  | Prog.ub => True
  | Prog.nb => True
  | Prog.assume _ p => noCallsTo M p
  | Prog.guarantee _ p => noCallsTo M p
  | Prog.call f _ k => M f = none ∧ ∀ r, noCallsTo M (k r)

/-- For a body that calls only library functions, resolving calls against the
linked module `M ⋆ L` is the same as resolving them against `L` alone. -/
theorem inline_link_eq_of_noCalls {V : Type} (M L : Mod V) (p : Prog V)
    (hp : noCallsTo M p) : inline (Mod.link M L) p = inline L p := by
  induction p with
  | ret v => rfl
  | tau p ih => exact congrArg Prog.tau (ih hp)
  | io f a h ih => exact congrArg (Prog.io f a) (funext (fun r => ih r (hp r)))
  | choose X h ih => exact congrArg (Prog.choose X) (funext (fun x => ih x (hp x)))
  | take X h ih => exact congrArg (Prog.take X) (funext (fun x => ih x (hp x)))
  | ub => rfl
  | nb => rfl
  | assume Q p ih => exact congrArg (Prog.assume Q) (ih hp)
  | guarantee Q p ih => exact congrArg (Prog.guarantee Q) (ih hp)
  | call f a h ih =>
      have hLink : Mod.link M L f = L f := by
        unfold Mod.link
        rw [hp.1]
      have hK : (fun r => inline (Mod.link M L) (h r)) = (fun r => inline L (h r)) :=
        funext (fun r => ih r (hp.2 r))
      cases hL : L f with
      | none =>
          rw [inline_call_none (Mod.link M L) f a h (hLink.trans hL),
            inline_call_none L f a h hL, hK]
      | some body =>
          rw [inline_call_some (Mod.link M L) f a h body (hLink.trans hL),
            inline_call_some L f a h body hL, hK]

/-- Uninlining (step 3 of the chain) for the layered fragment: when the entry
body of `M` calls only library functions, the entry of `hide M L` behaves
exactly as the entry of `M ⋆ L`.  In this fragment the step is an equality of
programs; the modelled systems prove an inclusion for recursive modules. -/
theorem uninlining_layered {V : Type} (M L : Mod V) (entryBody : Prog V)
    (hp : noCallsTo M entryBody) :
    Beh.le (beh (inline L entryBody)) (beh (inline (Mod.link M L) entryBody)) := by
  rw [inline_link_eq_of_noCalls M L entryBody hp]
  exact Beh.le_refl _

/-! ### The four-step chain as a composition theorem

The statement below is deliberately abstract.  It says: *given* the three
program-independent facts (inlining, uninlining, cancellation), the refinement
of the linked target program by the linked source program follows from one
remaining obligation, the simulation between the two `hide`-inlined modules.
It does not prove the three facts for any concrete system. -/

/-- The laws assumed of a refinement framework by the four-step chain. -/
structure ChainLaws (Module : Type) where
  /-- linking of modules -/
  link : Module → Module → Module
  /-- `hide M L`: `M` with calls into `L` inlined -/
  hide : Module → Module → Module
  /-- wrapper around every function body -/
  wfun : Module → Module
  /-- wrapper around every call site -/
  wcall : Module → Module
  /-- contextual refinement -/
  ctxRef : Module → Module → Prop
  /-- behavioral refinement -/
  behRef : Module → Module → Prop
  /-- side condition: the module defines the program entry -/
  definesEntry : Module → Prop
  /-- side condition: the module is a stateless library without an entry -/
  isLibrary : Module → Prop
  /-- side condition: the entry precondition holds initially -/
  entryPreHolds : Module → Prop
  behRef_trans : ∀ a b c, behRef a b → behRef b c → behRef a c
  ctxRef_behRef : ∀ a b, ctxRef a b → behRef a b
  /-- step 1 -/
  inlining : ∀ m l, ctxRef (link m l) (hide m l)
  /-- step 3 -/
  uninlining : ∀ m l, definesEntry m → isLibrary l → behRef (hide m l) (link m l)
  /-- step 4 -/
  cancellation : ∀ m, definesEntry m → entryPreHolds m → behRef (wfun (wcall m)) m

/-- **Single-simulation reduction.**  Under `ChainLaws`, refinement of the
linked target program by the linked source program reduces to the one
program-specific obligation `simulation`.

`mainT` / `libT` are the target-side main module and library (already wrapped
where the framework requires it), `mainS` / `libS` the source-side ones, and
`libShared` the library shared by both sides.  `wrap_distrib` is the bookkeeping
fact that the wrappers distribute over linking for the given source modules. -/
theorem cris_four_step_chain_sound {Module : Type} (A : ChainLaws Module)
    (mainT libT mainS libS libShared : Module)
    (hEntryW : A.definesEntry (A.wfun (A.wcall mainS)))
    (hLib : A.isLibrary (A.link (A.wfun libS) libShared))
    (hEntry : A.definesEntry (A.link mainS (A.link libS libShared)))
    (hPre : A.entryPreHolds (A.link mainS (A.link libS libShared)))
    (wrap_distrib :
      A.link (A.wfun (A.wcall mainS)) (A.link (A.wfun libS) libShared)
        = A.wfun (A.wcall (A.link mainS (A.link libS libShared))))
    (simulation :
      A.ctxRef (A.hide mainT (A.link libT libShared))
               (A.hide (A.wfun (A.wcall mainS)) (A.link (A.wfun libS) libShared))) :
    A.behRef (A.link mainT (A.link libT libShared))
             (A.link mainS (A.link libS libShared)) := by
  -- (1) inlining on the target side
  have s1 : A.behRef (A.link mainT (A.link libT libShared))
      (A.hide mainT (A.link libT libShared)) :=
    A.ctxRef_behRef _ _ (A.inlining _ _)
  -- (2) the program-specific simulation
  have s2 : A.behRef (A.hide mainT (A.link libT libShared))
      (A.hide (A.wfun (A.wcall mainS)) (A.link (A.wfun libS) libShared)) :=
    A.ctxRef_behRef _ _ simulation
  -- (3) uninlining on the wrapped source side
  have s3 : A.behRef
      (A.hide (A.wfun (A.wcall mainS)) (A.link (A.wfun libS) libShared))
      (A.link (A.wfun (A.wcall mainS)) (A.link (A.wfun libS) libShared)) :=
    A.uninlining _ _ hEntryW hLib
  -- (4) cancellation of the wrappers
  have s4 : A.behRef
      (A.link (A.wfun (A.wcall mainS)) (A.link (A.wfun libS) libShared))
      (A.link mainS (A.link libS libShared)) := by
    rw [wrap_distrib]
    exact A.cancellation _ hEntry hPre
  exact A.behRef_trans _ _ _ s1 (A.behRef_trans _ _ _ s2 (A.behRef_trans _ _ _ s3 s4))

/-- The assumptions of `ChainLaws` are jointly satisfiable.  This instance is a
consistency witness only (every relation is trivially true); it says nothing
about any real framework. -/
noncomputable def trivialChainLaws : ChainLaws Unit where
  link := fun _ _ => ()
  hide := fun _ _ => ()
  wfun := fun _ => ()
  wcall := fun _ => ()
  ctxRef := fun _ _ => True
  behRef := fun _ _ => True
  definesEntry := fun _ => True
  isLibrary := fun _ => True
  entryPreHolds := fun _ => True
  behRef_trans := fun _ _ _ _ _ => True.intro
  ctxRef_behRef := fun _ _ _ => True.intro
  inlining := fun _ _ => True.intro
  uninlining := fun _ _ _ _ => True.intro
  cancellation := fun _ _ _ => True.intro

/-- The chain is only as strong as its one obligation: if the simulation
obligation is replaced by a weaker source-side model that has more behaviors
than the real source, the conclusion is about that weaker model, not about the
real source.  `model_refinement_transfer` states exactly which approximations
are allowed on which side. -/
theorem model_refinement_transfer {V : Type} {T T' S' S : Beh V}
    (hTarget : Beh.le T T') (hSource : Beh.le S' S) (hChecked : Beh.le T' S') :
    Beh.le T S :=
  Beh.le_trans hTarget (Beh.le_trans hChecked hSource)

/-! ## Part 3.  `undef`, `poison`, and explicit choice -/

/-- A two-bit value domain with `poison`.  Bit 0 plays the role of a one-bit
bit-field `a`; bit 1 stands for the remaining bits of the same storage unit. -/
inductive Val : Type where
  | poison : Val
  | bits : Bool → Bool → Val

/-- Value refinement: equal, or the right-hand side is `poison`. -/
noncomputable def Val.refines (v v' : Val) : Prop := v = v' ∨ v' = Val.poison

theorem Val.refines_refl (v : Val) : Val.refines v v := Or.inl rfl

theorem Val.refines_trans {a b c : Val}
    (h₁ : Val.refines a b) (h₂ : Val.refines b c) : Val.refines a c := by
  cases h₁ with
  | inl hab =>
      cases h₂ with
      | inl hbc => exact Or.inl (hab.trans hbc)
      | inr hc => exact Or.inr hc
  | inr hb =>
      cases h₂ with
      | inl hbc => exact Or.inr (hbc ▸ hb)
      | inr hc => exact Or.inr hc

/-- Bitwise `and`; `poison` in either operand makes the result `poison`. -/
noncomputable def Val.and : Val → Val → Val
  | Val.bits a0 a1, Val.bits b0 b1 => Val.bits (a0 && b0) (a1 && b1)
  | Val.bits _ _, Val.poison => Val.poison
  | Val.poison, _ => Val.poison

/-- Bitwise `or`; `poison` in either operand makes the result `poison`. -/
noncomputable def Val.or : Val → Val → Val
  | Val.bits a0 a1, Val.bits b0 b1 => Val.bits (a0 || b0) (a1 || b1)
  | Val.bits _ _, Val.poison => Val.poison
  | Val.poison, _ => Val.poison

/-- Bitwise `xor`; `poison` in either operand makes the result `poison`. -/
noncomputable def Val.xor : Val → Val → Val
  | Val.bits a0 a1, Val.bits b0 b1 => Val.bits (Bool.xor a0 b0) (Bool.xor a1 b1)
  | Val.bits _ _, Val.poison => Val.poison
  | Val.poison, _ => Val.poison

theorem Val.and_poison_right (a : Val) : Val.and a Val.poison = Val.poison := by
  cases a with
  | poison => rfl
  | bits _ _ => rfl

theorem Val.or_poison_right (a : Val) : Val.or a Val.poison = Val.poison := by
  cases a with
  | poison => rfl
  | bits _ _ => rfl

/-- `and` is monotone for value refinement. -/
theorem Val.and_mono {a a' b b' : Val}
    (ha : Val.refines a a') (hb : Val.refines b b') :
    Val.refines (Val.and a b) (Val.and a' b') := by
  cases ha with
  | inr hp => subst hp; exact Or.inr rfl
  | inl hEq =>
      subst hEq
      cases hb with
      | inr hp => subst hp; exact Or.inr (Val.and_poison_right a)
      | inl hEq' => subst hEq'; exact Or.inl rfl

/-- `or` is monotone for value refinement. -/
theorem Val.or_mono {a a' b b' : Val}
    (ha : Val.refines a a') (hb : Val.refines b b') :
    Val.refines (Val.or a b) (Val.or a' b') := by
  cases ha with
  | inr hp => subst hp; exact Or.inr rfl
  | inl hEq =>
      subst hEq
      cases hb with
      | inr hp => subst hp; exact Or.inr (Val.or_poison_right a)
      | inl hEq' => subst hEq'; exact Or.inl rfl

/-- Straight-line expressions over one argument.

* `undef`   each evaluation may yield any defined bit pattern;
* `poison`  the poison value;
* `choice`  an explicit nondeterministic choice of a defined bit pattern, the
            meaning of freezing an indeterminate value. -/
inductive Expr : Type where
  | lit : Bool → Bool → Expr
  | arg : Expr
  | undef : Expr
  | poison : Expr
  | choice : Expr
  | and : Expr → Expr → Expr
  | or : Expr → Expr → Expr

/-- The set of values an expression may evaluate to, for argument value `x`. -/
noncomputable def den (x : Val) : Expr → Val → Prop
  | Expr.lit a b, v => v = Val.bits a b
  | Expr.arg, v => v = x
  | Expr.undef, v => ∃ a b, v = Val.bits a b
  | Expr.poison, v => v = Val.poison
  | Expr.choice, v => ∃ a b, v = Val.bits a b
  | Expr.and e₁ e₂, v => ∃ v₁ v₂, den x e₁ v₁ ∧ den x e₂ v₂ ∧ v = Val.and v₁ v₂
  | Expr.or e₁ e₂, v => ∃ v₁ v₂, den x e₁ v₁ ∧ den x e₂ v₂ ∧ v = Val.or v₁ v₂

/-- Replace every `undef` leaf by the expression `r`. -/
noncomputable def subst (r : Expr) : Expr → Expr
  | Expr.lit a b => Expr.lit a b
  | Expr.arg => Expr.arg
  | Expr.undef => r
  | Expr.poison => Expr.poison
  | Expr.choice => Expr.choice
  | Expr.and e₁ e₂ => Expr.and (subst r e₁) (subst r e₂)
  | Expr.or e₁ e₂ => Expr.or (subst r e₁) (subst r e₂)

/-- What a validation driver records for a result set: any non-`poison` value
that refines a possible result.  A `poison` result is observed as every value. -/
noncomputable def observe (S : Val → Prop) : Val → Prop :=
  fun o => ∃ v, S v ∧ Val.refines o v ∧ o ≠ Val.poison

/-- Refinement of a target result set by a source result set, as observed. -/
noncomputable def Refines (T S : Val → Prop) : Prop := ∀ o, observe T o → observe S o

theorem Refines.trans {A B C : Val → Prop}
    (h₁ : Refines A B) (h₂ : Refines B C) : Refines A C :=
  fun o h => h₂ o (h₁ o h)

/-- Rewriting `undef` to an explicit choice is exact: it neither adds nor
removes a possible value, for every expression. -/
theorem subst_choice_exact (x : Val) (e : Expr) (v : Val) :
    den x (subst Expr.choice e) v ↔ den x e v := by
  induction e generalizing v with
  | lit a b => exact Iff.rfl
  | arg => exact Iff.rfl
  | undef => exact Iff.rfl
  | poison => exact Iff.rfl
  | choice => exact Iff.rfl
  | and e₁ e₂ ih₁ ih₂ =>
      constructor
      · intro h
        obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h
        exact ⟨v₁, v₂, (ih₁ v₁).mp h₁, (ih₂ v₂).mp h₂, hv⟩
      · intro h
        obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h
        exact ⟨v₁, v₂, (ih₁ v₁).mpr h₁, (ih₂ v₂).mpr h₂, hv⟩
  | or e₁ e₂ ih₁ ih₂ =>
      constructor
      · intro h
        obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h
        exact ⟨v₁, v₂, (ih₁ v₁).mp h₁, (ih₂ v₂).mp h₂, hv⟩
      · intro h
        obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h
        exact ⟨v₁, v₂, (ih₁ v₁).mpr h₁, (ih₂ v₂).mpr h₂, hv⟩

/-- **Sound lowering.**  Checking refinement after rewriting `undef` to an
explicit choice on both sides is equivalent to checking it on the original
expressions. -/
theorem freeze_undef_set_refinement (x : Val) (t s : Expr) :
    Refines (den x (subst Expr.choice t)) (den x (subst Expr.choice s))
      ↔ Refines (den x t) (den x s) := by
  constructor
  · intro h o ho
    obtain ⟨v, hv, hr, hne⟩ := ho
    have h' := h o ⟨v, (subst_choice_exact x t v).mpr hv, hr, hne⟩
    obtain ⟨w, hw, hr', hne'⟩ := h'
    exact ⟨w, (subst_choice_exact x s w).mp hw, hr', hne'⟩
  · intro h o ho
    obtain ⟨v, hv, hr, hne⟩ := ho
    have h' := h o ⟨v, (subst_choice_exact x t v).mp hv, hr, hne⟩
    obtain ⟨w, hw, hr', hne'⟩ := h'
    exact ⟨w, (subst_choice_exact x s w).mpr hw, hr', hne'⟩

/-- Every value of the original expression is refined by some value of the
`undef → poison` rewrite. -/
theorem subst_poison_covers (x : Val) (e : Expr) (v : Val) (h : den x e v) :
    ∃ v', den x (subst Expr.poison e) v' ∧ Val.refines v v' := by
  induction e generalizing v with
  | lit a b => exact ⟨v, h, Val.refines_refl v⟩
  | arg => exact ⟨v, h, Val.refines_refl v⟩
  | undef => exact ⟨Val.poison, rfl, Or.inr rfl⟩
  | poison => exact ⟨v, h, Val.refines_refl v⟩
  | choice => exact ⟨v, h, Val.refines_refl v⟩
  | and e₁ e₂ ih₁ ih₂ =>
      obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h
      obtain ⟨w₁, hw₁, hr₁⟩ := ih₁ v₁ h₁
      obtain ⟨w₂, hw₂, hr₂⟩ := ih₂ v₂ h₂
      exact ⟨Val.and w₁ w₂, ⟨w₁, w₂, hw₁, hw₂, rfl⟩, hv ▸ Val.and_mono hr₁ hr₂⟩
  | or e₁ e₂ ih₁ ih₂ =>
      obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h
      obtain ⟨w₁, hw₁, hr₁⟩ := ih₁ v₁ h₁
      obtain ⟨w₂, hw₂, hr₂⟩ := ih₂ v₂ h₂
      exact ⟨Val.or w₁ w₂, ⟨w₁, w₂, hw₁, hw₂, rfl⟩, hv ▸ Val.or_mono hr₁ hr₂⟩

/-- Rewriting `undef` to `poison` can only **add** observable behaviors.  On the
source side of a refinement check this is the unsound direction. -/
theorem subst_poison_adds_behaviors (x : Val) (e : Expr) :
    Refines (den x e) (den x (subst Expr.poison e)) := by
  intro o ho
  obtain ⟨v, hv, hr, hne⟩ := ho
  obtain ⟨v', hv', hr'⟩ := subst_poison_covers x e v hv
  exact ⟨v', hv', Val.refines_trans hr hr', hne⟩

/-- Rewriting `undef` to zero can only **remove** possible values.  On the
target side of a refinement check this is the unsound direction. -/
theorem subst_zero_removes_behaviors (x : Val) (e : Expr) (v : Val)
    (h : den x (subst (Expr.lit false false) e) v) : den x e v := by
  induction e generalizing v with
  | lit a b => exact h
  | arg => exact h
  | undef => exact ⟨false, false, h⟩
  | poison => exact h
  | choice => exact h
  | and e₁ e₂ ih₁ ih₂ =>
      obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h
      exact ⟨v₁, v₂, ih₁ v₁ h₁, ih₂ v₂ h₂, hv⟩
  | or e₁ e₂ ih₁ ih₂ =>
      obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h
      exact ⟨v₁, v₂, ih₁ v₁ h₁, ih₂ v₂ h₂, hv⟩

/-- **The mirrored assignment is sound.**  Rewriting `undef` to `poison` on the
*target* side and to zero on the *source* side over-approximates the target and
under-approximates the source, so a refinement proved after these rewrites
holds for the original expressions.  (It may fail to prove a true refinement.) -/
theorem mirrored_rewrite_is_sound (x : Val) (t s : Expr)
    (h : Refines (den x (subst Expr.poison t))
      (den x (subst (Expr.lit false false) s))) :
    Refines (den x t) (den x s) := by
  intro o ho
  have h₁ := subst_poison_adds_behaviors x t o ho
  obtain ⟨v, hv, hr, hne⟩ := h o h₁
  exact ⟨v, subst_zero_removes_behaviors x s v hv, hr, hne⟩

/-! ### Counterexample 1: source-side `undef → poison` -/

/-- A bit-field store into an indeterminate storage unit:
`(old & 0b10) | arg`, where `old` is `undef` and the argument carries the new
value of bit 0 (its bit 1 is clear). -/
noncomputable def cBitfieldStore : Expr :=
  Expr.or (Expr.and Expr.undef (Expr.lit false true)) Expr.arg

/-- A wrong translation: it always returns the all-zero unit. -/
noncomputable def brokenTranslation : Expr := Expr.lit false false

/-- With `undef` kept, every result of the store has bit 0 equal to the
argument's bit 0. -/
theorem cBitfieldStore_bit0_defined (xa : Bool) (v : Val)
    (h : den (Val.bits xa false) cBitfieldStore v) : ∃ b1, v = Val.bits xa b1 := by
  obtain ⟨v₁, v₂, h₁, h₂, hv⟩ := h
  obtain ⟨u, m, hu, hm, hv₁⟩ := h₁
  obtain ⟨a, b, hab⟩ := hu
  subst hab
  subst hm
  subst hv₁
  subst h₂
  subst hv
  refine ⟨b && true || false, ?_⟩
  show Val.bits (a && false || xa) (b && true || false) = Val.bits xa (b && true || false)
  cases a <;> rfl

/-- After the rewrite the store evaluates to `poison` only. -/
theorem cBitfieldStore_poisoned (x v : Val)
    (h : den x (subst Expr.poison cBitfieldStore) v) : v = Val.poison := by
  obtain ⟨v₁, v₂, h₁, _, hv⟩ := h
  obtain ⟨u, m, hu, _, hv₁⟩ := h₁
  subst hu
  subst hv₁
  subst hv
  rfl

/-- **CE1.**  After `undef → poison` on the source side the wrong translation
is accepted for every argument, although against the original source it is
rejected for the argument whose bit 0 is set. -/
theorem ce1_c_bitfield_undef_to_poison_vacuous_refinement :
    (∀ x : Val, Refines (den x brokenTranslation)
        (den x (subst Expr.poison cBitfieldStore)))
    ∧ ¬ Refines (den (Val.bits true false) brokenTranslation)
        (den (Val.bits true false) cBitfieldStore) := by
  constructor
  · intro x o ho
    obtain ⟨_, _, _, hne⟩ := ho
    refine ⟨Val.poison, ?_, Or.inr rfl, hne⟩
    exact ⟨Val.poison, x,
      ⟨Val.poison, Val.bits false true, rfl, rfl, rfl⟩, rfl, rfl⟩
  · intro h
    have hObs : observe (den (Val.bits true false) brokenTranslation)
        (Val.bits false false) :=
      ⟨Val.bits false false, rfl, Val.refines_refl _, fun hc => Val.noConfusion hc⟩
    obtain ⟨v, hv, hr, _⟩ := h _ hObs
    obtain ⟨b1, hb1⟩ := cBitfieldStore_bit0_defined true v hv
    subst hb1
    cases hr with
    | inl hEq => exact Bool.noConfusion (Val.bits.inj hEq).1
    | inr hp => exact Val.noConfusion hp

/-- The explicit-choice rewrite does not have this defect: the wrong
translation stays rejected. -/
theorem ce1_choice_lowering_still_rejects :
    ¬ Refines (den (Val.bits true false) (subst Expr.choice brokenTranslation))
        (den (Val.bits true false) (subst Expr.choice cBitfieldStore)) :=
  fun h => ce1_c_bitfield_undef_to_poison_vacuous_refinement.2
    ((freeze_undef_set_refinement _ _ _).mp h)

/-! ### Counterexample 2: target-side `undef → 0` -/

/-- A target that returns an indeterminate value. -/
noncomputable def uninitTarget : Expr := Expr.undef

/-- A source that returns the constant zero. -/
noncomputable def zeroSource : Expr := Expr.lit false false

/-- **CE2.**  After `undef → 0` on the target side, a target returning an
indeterminate value is accepted against a source returning zero, although the
original target can return a non-zero value the source never returns. -/
theorem ce2_rust_undef_to_zero_misses_nonzero_choice (x : Val) :
    Refines (den x (subst (Expr.lit false false) uninitTarget)) (den x zeroSource)
    ∧ ¬ Refines (den x uninitTarget) (den x zeroSource) := by
  constructor
  · intro o ho
    exact ho
  · intro h
    have hObs : observe (den x uninitTarget) (Val.bits true false) :=
      ⟨Val.bits true false, ⟨true, false, rfl⟩, Val.refines_refl _,
        fun hc => Val.noConfusion hc⟩
    obtain ⟨v, hv, hr, _⟩ := h _ hObs
    have hv' : v = Val.bits false false := hv
    subst hv'
    cases hr with
    | inl hEq => exact Bool.noConfusion (Val.bits.inj hEq).1
    | inr hp => exact Val.noConfusion hp

/-! ### Per-use `undef` versus one shared choice -/

/-- The content of an SSA register: a concrete value, or the `undef` token that
is re-resolved at every use. -/
inductive Reg : Type where
  | conc : Val → Reg
  | undefTok : Reg

/-- The values one use of a register may see. -/
noncomputable def Reg.use : Reg → Val → Prop
  | Reg.conc c, v => v = c
  | Reg.undefTok, v => ∃ a b, v = Val.bits a b

/-- `xor` of two uses of the same register. -/
noncomputable def xorTwoUses (r : Reg) : Val → Prop :=
  fun v => ∃ a b, Reg.use r a ∧ Reg.use r b ∧ v = Val.xor a b

theorem Val.xor_self_bits (a b : Bool) :
    Val.xor (Val.bits a b) (Val.bits a b) = Val.bits false false := by
  cases a <;> cases b <;> rfl

/-- Freezing an `undef` register once and sharing the frozen value yields a
subset of the per-use behaviors: sound when used to model a source. -/
theorem shared_choice_refines_per_use (a b : Bool) (v : Val)
    (h : xorTwoUses (Reg.conc (Val.bits a b)) v) : xorTwoUses Reg.undefTok v := by
  obtain ⟨p, q, hp, hq, hv⟩ := h
  have hp' : p = Val.bits a b := hp
  have hq' : q = Val.bits a b := hq
  exact ⟨p, q, ⟨a, b, hp'⟩, ⟨a, b, hq'⟩, hv⟩

/-- The subset is strict: per-use `undef` can make `xor r r` non-zero, a shared
frozen value cannot.  A target must therefore be modelled with one fresh choice
per use, not with one shared choice. -/
theorem per_use_undef_strictly_more :
    xorTwoUses Reg.undefTok (Val.bits true false)
    ∧ ∀ a b, ¬ xorTwoUses (Reg.conc (Val.bits a b)) (Val.bits true false) := by
  constructor
  · exact ⟨Val.bits true false, Val.bits false false,
      ⟨true, false, rfl⟩, ⟨false, false, rfl⟩, rfl⟩
  · intro a b h
    obtain ⟨p, q, hp, hq, hv⟩ := h
    have hp' : p = Val.bits a b := hp
    have hq' : q = Val.bits a b := hq
    subst hp'
    subst hq'
    rw [Val.xor_self_bits] at hv
    exact Bool.noConfusion (Val.bits.inj hv).1

/-! ## Part 4.  Source-level UB and call-boundary attributes -/

/-- Observable outcomes of an allocation request. -/
inductive Outcome : Type where
  | allocated : Nat → Outcome
  | abort : Outcome

/-- The requested element count `n + 1`, as a mathematical integer. -/
noncomputable def boundOf (n : Int) : Int := n + 1

/-- Zero-extension of a 32-bit pattern to 64 bits, read as unsigned. -/
noncomputable def zext32 (i : Int) : Nat := (i % 4294967296).toNat

/-- Sign-extension of a 32-bit value to 64 bits, read as unsigned. -/
noncomputable def sext32AsUnsigned64 (i : Int) : Nat := (i % 18446744073709551616).toNat

/-- The largest size a Rust allocation may have. -/
noncomputable def isizeMax : Nat := 9223372036854775807

/-- C source semantics of a variable-length array bound: a non-positive bound
is undefined behavior (every outcome). -/
noncomputable def cSource (n : Int) : Outcome → Prop :=
  fun o => boundOf n ≤ 0 ∨ o = Outcome.allocated (boundOf n).toNat

/-- The compiled C IR: the bound is zero-extended and the allocation is defined
for every bit pattern. -/
noncomputable def cIr (n : Int) : Outcome → Prop :=
  fun o => o = Outcome.allocated (zext32 (boundOf n))

/-- The compiled Rust IR: the bound is sign-extended, and a request above
`isizeMax` aborts. -/
noncomputable def rustIr (n : Int) : Outcome → Prop :=
  fun o =>
    (sext32AsUnsigned64 (boundOf n) ≤ isizeMax
      ∧ o = Outcome.allocated (sext32AsUnsigned64 (boundOf n)))
    ∨ (isizeMax < sext32AsUnsigned64 (boundOf n) ∧ o = Outcome.abort)

/-- Validating the target against the compiled source IR is **sound** for
source-level correctness whenever the source compiler is correct. -/
theorem ir_level_validation_sound {O : Type} (src ir tgt : O → Prop)
    (hCompile : ∀ o, ir o → src o) (hValidated : ∀ o, tgt o → ir o) :
    ∀ o, tgt o → src o :=
  fun o h => hCompile o (hValidated o h)

/-- For the bound `n = -2` the C compiler output is a correct refinement of the
C source (the source is undefined there). -/
theorem cIr_refines_cSource_at_neg (o : Outcome) (_h : cIr (-2) o) : cSource (-2) o :=
  Or.inl (by decide)

/-- For the bound `n = -2` the Rust output is also a correct refinement of the
C source. -/
theorem rustIr_refines_cSource_at_neg (o : Outcome) (_h : rustIr (-2) o) :
    cSource (-2) o :=
  Or.inl (by decide)

/-- For the bound `n = -2` the compiled C IR allocates `4294967295` elements. -/
theorem cIr_at_neg : cIr (-2) (Outcome.allocated 4294967295) := by
  have h : zext32 (boundOf (-2)) = 4294967295 := by decide
  show Outcome.allocated 4294967295 = Outcome.allocated (zext32 (boundOf (-2)))
  rw [h]

/-- For the bound `n = -2` the compiled Rust IR aborts: the sign-extended
request is `18446744073709551615`, above `isizeMax`. -/
theorem rustIr_at_neg : rustIr (-2) Outcome.abort :=
  Or.inr ⟨by decide, rfl⟩

/-- **CE3.**  There is an input on which (a) the compiled C IR refines the C
source, (b) the Rust output refines the C source, and yet (c) the Rust output
does not refine the compiled C IR.  Validation against IR reports a
counterexample for a translation that is correct with respect to the source. -/
theorem ce3_clang_ub_refinement_creates_false_positive :
    (∀ o, cIr (-2) o → cSource (-2) o)
    ∧ (∀ o, rustIr (-2) o → cSource (-2) o)
    ∧ ¬ (∀ o, rustIr (-2) o → cIr (-2) o) := by
  refine ⟨cIr_refines_cSource_at_neg, rustIr_refines_cSource_at_neg, ?_⟩
  intro h
  have hBad : Outcome.abort = Outcome.allocated (zext32 (boundOf (-2))) :=
    h _ rustIr_at_neg
  exact Outcome.noConfusion hBad

/-- On a positive bound all three agree, so the disagreement of CE3 is confined
to inputs on which the source is undefined. -/
theorem all_three_agree_at_positive (o : Outcome) :
    (rustIr 3 o ↔ cIr 3 o) ∧ (cIr 3 o ↔ cSource 3 o) := by
  have hS : sext32AsUnsigned64 (boundOf 3) = 4 := by decide
  have hZ : zext32 (boundOf 3) = 4 := by decide
  have hB : (boundOf 3).toNat = 4 := by decide
  have hSZ : Outcome.allocated (sext32AsUnsigned64 (boundOf 3))
      = Outcome.allocated (zext32 (boundOf 3)) := by rw [hS, hZ]
  have hZB : Outcome.allocated (zext32 (boundOf 3))
      = Outcome.allocated (boundOf 3).toNat := by rw [hZ, hB]
  constructor
  · constructor
    · intro h
      cases h with
      | inl hOk =>
          show o = Outcome.allocated (zext32 (boundOf 3))
          exact hOk.2.trans hSZ
      | inr hAbort => exact absurd hAbort.1 (by decide)
    · intro h
      have h' : o = Outcome.allocated (zext32 (boundOf 3)) := h
      exact Or.inl ⟨by decide, h'.trans hSZ.symm⟩
  · constructor
    · intro h
      have h' : o = Outcome.allocated (zext32 (boundOf 3)) := h
      exact Or.inr (h'.trans hZB)
    · intro h
      cases h with
      | inl hLe => exact absurd hLe (by decide)
      | inr hEq =>
          show o = Outcome.allocated (zext32 (boundOf 3))
          exact hEq.trans hZB.symm

/-- A call under the rule that passing `poison` to a `noundef` parameter is
immediate undefined behavior (every outcome). -/
noncomputable def callFaithful (noundef : Bool) (body : Val → Val → Prop) : Val → Val → Prop
  | Val.poison, o => if noundef = true then True else body Val.poison o
  | Val.bits a b, o => body (Val.bits a b) o

/-- The same call with parameter attributes ignored. -/
noncomputable def callStripped (body : Val → Val → Prop) : Val → Val → Prop :=
  fun a o => body a o

/-- Ignoring `noundef` can only remove behaviors. -/
theorem stripped_le_faithful (noundef : Bool) (body : Val → Val → Prop)
    (a o : Val) (h : callStripped body a o) : callFaithful noundef body a o := by
  cases a with
  | bits _ _ => exact h
  | poison =>
      cases noundef with
      | false => exact h
      | true => exact True.intro

/-- Consequently, ignoring `noundef` on the **source** side is sound: a target
validated against the attribute-free source also refines the faithful source. -/
theorem source_side_strip_is_sound (noundef : Bool) (body : Val → Val → Prop)
    (a : Val) (T : Val → Prop) (h : ∀ o, T o → callStripped body a o) :
    ∀ o, T o → callFaithful noundef body a o :=
  fun o ho => stripped_le_faithful noundef body a o (h o ho)

/-- A callee that ignores its argument and returns the all-zero value. -/
noncomputable def constZeroBody : Val → Val → Prop := fun _ o => o = Val.bits false false

/-- **CE4.**  Ignoring `noundef` on the **target** side is unsound.  A target
that passes `poison` to a `noundef` parameter of a constant-zero callee is
validated against a constant-zero source when the attribute is ignored, while
the faithful target has undefined behavior and can produce an outcome the
source never produces. -/
theorem ce4_omitted_noundef_attr_misses_argument_poison_ub :
    (∀ o, callStripped constZeroBody Val.poison o → o = Val.bits false false)
    ∧ ¬ (∀ o, callFaithful true constZeroBody Val.poison o → o = Val.bits false false) := by
  constructor
  · intro o h
    exact h
  · intro h
    have hUb : callFaithful true constZeroBody Val.poison (Val.bits true true) :=
      True.intro
    exact Bool.noConfusion (Val.bits.inj (h _ hUb)).1

end CrisModel

/-! ## Audit of this file's own declarations

The command below runs at elaboration time and fails the build if any
declaration in namespace `CrisModel` is `unsafe`, `partial`, a compiler helper
named `_unsafe_rec`, or depends on an axiom other than `propext` and
`Quot.sound`.

Declarations of the file being elaborated live in the second stage of the
constant map (`map₂`); the first stage (`map₁`) holds imported constants only.
Both stages are scanned and reported separately, so that a check restricted to
`map₁` cannot pass vacuously. -/
namespace CrisAudit

open Lean

/-- Does the textual name contain the given fragment? -/
def nameContains (n : Name) (fragment : String) : Bool :=
  (n.toString.splitOn fragment).length > 1

/-- Axioms a `CrisModel` declaration may depend on. -/
def allowedAxioms : List Name := [``propext, ``Quot.sound]

/-- Scan the environment and fail on any purity violation. -/
def audit : CoreM Unit := do
  let env ← getEnv
  let inScope : Name → Bool := fun n => (`CrisModel).isPrefixOf n
  let stage1 := env.constants.map₁.fold (init := (#[] : Array Name))
    (fun acc n _ => if inScope n then acc.push n else acc)
  let stage2 := env.constants.map₂.foldl (init := (#[] : Array Name))
    (fun acc n _ => if inScope n then acc.push n else acc)
  let mut unsafeRec : Array Name := #[]
  let mut unsafeOrPartial : Array Name := #[]
  let mut theorems := 0
  let mut badAxioms : Array (Name × Name) := #[]
  let mut axiomsSeen : Array Name := #[]
  for n in stage1 ++ stage2 do
    if nameContains n "_unsafe_rec" then
      unsafeRec := unsafeRec.push n
    match env.find? n with
    | none => pure ()
    | some ci =>
        if ci.isUnsafe || ci.isPartial then
          unsafeOrPartial := unsafeOrPartial.push n
        if ci matches .thmInfo _ then
          theorems := theorems + 1
        let axs ← collectAxioms n
        for a in axs do
          if !axiomsSeen.contains a then
            axiomsSeen := axiomsSeen.push a
          if !allowedAxioms.contains a then
            badAxioms := badAxioms.push (n, a)
  IO.println s!"CrisModel constants in map₁ (imported): {stage1.size}"
  IO.println s!"CrisModel constants in map₂ (this file): {stage2.size}"
  IO.println s!"theorems: {theorems}"
  IO.println s!"_unsafe_rec constants: {unsafeRec.size} {unsafeRec.toList}"
  IO.println s!"unsafe or partial constants: {unsafeOrPartial.size} {unsafeOrPartial.toList}"
  IO.println s!"axioms used: {axiomsSeen.toList}"
  IO.println s!"disallowed axiom uses: {badAxioms.size}"
  if stage2.size == 0 then
    throwError "audit scanned no declarations; the check would be vacuous"
  if unsafeRec.size != 0 || unsafeOrPartial.size != 0 || badAxioms.size != 0 then
    throwError "purity audit failed: {badAxioms.toList}"

#eval audit

end CrisAudit
