import MonoShim.Core

/-!
# Source semantics, the synthesizer, the collector and closed targets
-/

namespace Toy.MonoShim

/-! ## Source semantics `S` -/

/-- Lookup in an association list keyed by `Nat`. -/
def natLookup (l : List (Nat × Stmt)) (n : Nat) : Option Stmt := l.lookup n

/-- Impl lookup at a concrete type (first matching entry). -/
def implLookup (P : Program) (tr m : Nat) (t : Ty) : Option Stmt :=
  (P.impls.find? (fun e => decide (e.tr = tr ∧ e.m = m ∧ e.ty = t))).map ImplEntry.body

/-- Source drop behaviour computed from the type, following the documented destructor order.
A `base n` type has no fields: its glue runs the user `Drop::drop` if `base n` has one and is a
no-op otherwise. A `pair a b` drops `a` then `b` (declaration order); if dropping `a` unwinds,
`b` is still dropped on the unwind path (a panic in that cleanup drop aborts) and unwinding then
continues — the two-field drop ladder. `box τ` drops its contents; function pointers have no
destructor. Trait objects, type parameters and projections have no glue of their own here (`dyn`
values are dropped through their vtable). -/
def glueSrc (P : Program) : Ty → Option Stmt
  | .base n => some (if (natLookup P.dropImpls n).isSome then .invoke (.userDrop n) else .skip)
  | .box t => some (.drop t)
  | .pair a b => some (.seq (.onUnwind (.drop a) (.drop b)) (.drop b))
  | .fnPtr => some .skip
  | _ => none

/-- Source clone behaviour of non-base types: a pair clones as the aggregate expression
`(x.0.clone(), x.1.clone())`; a function pointer is `Copy`. Boxes, trait objects, parameters and
projections have no clone behaviour here (in particular `box τ` is not cloneable in the toy). -/
def cloneSrc : Ty → Option Stmt
  | .pair a b => some (.cloneAgg [a, b])
  | .fnPtr => some .skip
  | _ => none

/-- Source definitions for every key kind. Instances instantiate the generic body by substitution
followed by normalization (`Stmt.norm`); method and user `Drop`/`Clone` bodies are looked up and
normalized; shim keys are answered from the type (`glueSrc`, `cloneSrc`) or, for a reify shim, by
a forwarding call. -/
def srcDef0 (P : Program) : Key → Option Stmt
  | .inst f τs => (P.fns[f]?).map fun fd => (fd.body.subst τs).norm P
  | .meth tr m t => (implLookup P tr m t).map (Stmt.norm P)
  | .userDrop n => (natLookup P.dropImpls n).map (Stmt.norm P)
  | .userClone n => (natLookup P.cloneImpls n).map (Stmt.norm P)
  | .dropGlue t => glueSrc P t
  | .cloneShim t => cloneSrc t
  | .reifyShim f τs => (P.fns[f]?).map fun _ => .call f τs

/-- The source semantics resolves a requested key after normalizing its types: at run time
`<τ as tr>::Out` simply is its normal form. -/
def srcDef (P : Program) (k : Key) : Option Stmt := srcDef0 P (k.norm P)

/-- The source semantics `S`: run a key with the source resolver. -/
def runS (P : Program) (n : Nat) (k : Key) (st : St) : Res × St := runKey P.sig (srcDef P) n k st

/-! ## Synthesizer -/

/-- The tuple-like clone ladder: clone field `i`; if that unwinds, drop the clones of fields
`i-1, …, 0` (innermost cleanup first). -/
def ladder : List Ty → Stmt
  | [] => .skip
  | t :: ts => .seq (.clone t) (.onUnwind (ladder ts) (.drop t))

/-- The standard synthesizer: declaration-order drop glue, the clone ladder for pairs, the
trivial clone for function pointers, and a forwarding reify shim. -/
def synthStd (P : Program) : Key → Option Stmt
  | .dropGlue t => glueSrc P t
  | .cloneShim (.pair a b) => some (ladder [a, b])
  | .cloneShim .fnPtr => some .skip
  | .reifyShim f τs => (P.fns[f]?).map fun _ => .call f τs
  | _ => none

/-! ## Collector and closed targets -/

/-- A monomorphization pipeline configuration: the collector's edge function over bodies and the
shim synthesizer. -/
structure MonoCfg where
  E : Stmt → List Key
  synth : Key → Option Stmt

/-- The standard configuration: follow every runtime reference, synthesize with `synthStd`. -/
def stdCfg (P : Program) : MonoCfg := ⟨refs P.sig, synthStd P⟩

/-- The body the compiler emits for a key: synthesized for shim keys, the source body (instantiated
and normalized by `srcDef0`) otherwise. -/
def bodyM (P : Program) (cfg : MonoCfg) (k : Key) : Option Stmt :=
  if k.isShim then cfg.synth k else srcDef0 P k

/-- The collector's edge function on keys: the edges of the emitted body, keyed after
normalization (the definer canonicalizes the keys it records). -/
def edgesM (P : Program) (cfg : MonoCfg) (k : Key) : List Key :=
  match bodyM P cfg k with
  | some b => (cfg.E b).map (Key.norm P)
  | none => []

/-- The monomorphic symbol table restricted to a key set `T`: defined exactly on `T`. -/
def tableM (P : Program) (cfg : MonoCfg) (T : List Key) (k : Key) : Option Stmt :=
  if k ∈ T then bodyM P cfg k else none

/-- The mono semantics `M`: run a key in the finite table; calling a key outside `T` is a link
error. -/
def runM (P : Program) (cfg : MonoCfg) (T : List Key) (n : Nat) (k : Key) (st : St) : Res × St :=
  runKey P.sig (tableM P cfg T) n k st

/-- Least-fixpoint reachability from roots under an edge function. -/
inductive Reach (edges : Key → List Key) (roots : List Key) : Key → Prop
  | root {k : Key} : k ∈ roots → Reach edges roots k
  | step {k k' : Key} : Reach edges roots k → k' ∈ edges k → Reach edges roots k'

/-- A closed target: every key of `T` has a body in `tbl`, and every key that body references
(its runtime references) lies in `T`. -/
def Closed (sig : Sig) (tbl : Key → Option Stmt) (T : List Key) : Prop :=
  ∀ k ∈ T, (tbl k).isSome ∧ ∀ b ∈ (tbl k).toList, ∀ k' ∈ refs sig b, k' ∈ T

instance (sig : Sig) (tbl : Key → Option Stmt) (T : List Key) : Decidable (Closed sig tbl T) := by
  unfold Closed; exact inferInstance

/-- Worklist collector. `sched work new` decides how newly found keys are merged into the
remaining worklist (FIFO, LIFO, or anything else); the head of the worklist is processed next.
Every step consumes one unit of fuel; `none` means the fuel ran out. -/
def collectGo (edges : Key → List Key) (sched : List Key → List Key → List Key) :
    Nat → List Key → List Key → Option (List Key)
  | 0, _, _ => none
  | _ + 1, [], done => some done
  | n + 1, k :: work, done =>
    if k ∈ done then collectGo edges sched n work done
    else collectGo edges sched n (sched work (edges k)) (k :: done)

def collect (edges : Key → List Key) (sched : List Key → List Key → List Key)
    (roots : List Key) (fuel : Nat) : Option (List Key) :=
  collectGo edges sched fuel roots []

def fifo (work new : List Key) : List Key := work ++ new
def lifo (work new : List Key) : List Key := new ++ work

/-- A scheduler is admissible when it neither loses nor invents worklist entries. -/
def SchedOK (sched : List Key → List Key → List Key) : Prop :=
  ∀ w n x, x ∈ sched w n ↔ x ∈ w ∨ x ∈ n

/-! ## Hypotheses of the adequacy theorem, as separate properties -/

/-- (H1) The collector's edge function covers every runtime reference of every body. -/
def CoversRefs (sig : Sig) (E : Stmt → List Key) : Prop :=
  ∀ b k, k ∈ refs sig b → k ∈ E b

/-- Behavioural equivalence of two bodies: under every call oracle, from every state, running
either body in a fresh frame gives the same outcome and final state. -/
def BodyEquiv (sig : Sig) (b b' : Stmt) : Prop :=
  ∀ (c : Call) (st : St),
    ((execS sig c b [] st).1, (execS sig c b [] st).2.2) =
    ((execS sig c b' [] st).1, (execS sig c b' [] st).2.2)

/-- Both absent, or both present and behaviourally equivalent. -/
def OptEquiv (sig : Sig) : Option Stmt → Option Stmt → Prop
  | none, none => True
  | some b, some b' => BodyEquiv sig b b'
  | _, _ => False

/-- (H2) On every shim key of `T`, the synthesizer's output is equivalent to the source
construct (and defined exactly when the source defines it). -/
def SynthAgrees (P : Program) (cfg : MonoCfg) (T : List Key) : Prop :=
  ∀ k ∈ T, k.isShim = true → OptEquiv P.sig (cfg.synth k) (srcDef0 P k)

/-- (H3a) Canonical target keys: every key of `T` is already in normal form. -/
def CanonicalKeys (P : Program) (T : List Key) : Prop :=
  ∀ k ∈ T, k.norm P = k

instance (P : Program) (T : List Key) : Decidable (CanonicalKeys P T) := by
  unfold CanonicalKeys; exact inferInstance

/-- (H3b) Canonical references: every key referenced by a body the compiler emits for a key of
`T` is already in normal form (the referrer keys exactly as the definer does). -/
def CanonicalRefs (P : Program) (cfg : MonoCfg) (T : List Key) : Prop :=
  ∀ k ∈ T, ∀ b ∈ (bodyM P cfg k).toList, ∀ k' ∈ refs P.sig b, k'.norm P = k'

instance (P : Program) (cfg : MonoCfg) (T : List Key) : Decidable (CanonicalRefs P cfg T) := by
  unfold CanonicalRefs; exact inferInstance

/-- (H0) The source program defines every non-shim key of `T`. -/
def InstDefined (P : Program) (T : List Key) : Prop :=
  ∀ k ∈ T, k.isShim = false → (srcDef0 P k).isSome

instance (P : Program) (T : List Key) : Decidable (InstDefined P T) := by
  unfold InstDefined; exact inferInstance

/-- (H2t) The synthesizer is total on the shim keys of `T`. -/
def SynthTotal (cfg : MonoCfg) (T : List Key) : Prop :=
  ∀ k ∈ T, k.isShim = true → (cfg.synth k).isSome

instance (cfg : MonoCfg) (T : List Key) : Decidable (SynthTotal cfg T) := by
  unfold SynthTotal; exact inferInstance

/-- The roots lie in `T`. -/
def RootsIn (roots T : List Key) : Prop := ∀ k ∈ roots, k ∈ T

instance (roots T : List Key) : Decidable (RootsIn roots T) := by
  unfold RootsIn; exact inferInstance

/-- `T` is closed under the collector's edge function. -/
def EdgesIn (edges : Key → List Key) (T : List Key) : Prop := ∀ k ∈ T, ∀ k' ∈ edges k, k' ∈ T

instance (edges : Key → List Key) (T : List Key) : Decidable (EdgesIn edges T) := by
  unfold EdgesIn; exact inferInstance

/-! ## Idempotent normalization -/

/-- Every right-hand side of the associated-type table is already in normal form (a decidable
condition on `P.assoc` alone). -/
def assocNormal (P : Program) : Bool :=
  P.assoc.all fun e => decide (e.2.2.norm P.assoc = e.2.2)

/-- Under `assocNormal`, single-pass normalization is idempotent. -/
theorem ty_norm_idem_of_assocNormal (P : Program) (h : assocNormal P = true) :
    ∀ t : Ty, (t.norm P.assoc).norm P.assoc = t.norm P.assoc := by
  have hall : ∀ e ∈ P.assoc, e.2.2.norm P.assoc = e.2.2 := by
    intro e he
    exact of_decide_eq_true ((List.all_eq_true.mp h) e he)
  intro t
  induction t with
  | base n => rfl
  | box t ih => simp [Ty.norm, ih]
  | pair a b iha ihb => simp [Ty.norm, iha, ihb]
  | dyn tr => rfl
  | fnPtr => rfl
  | param i => rfl
  | proj tr t ih =>
    simp only [Ty.norm]
    rcases hf : assocLookup P.assoc tr (t.norm P.assoc) with _ | rhs
    · simp only [Option.getD_none, Ty.norm, ih, hf]
    · simp only [Option.getD_some]
      unfold assocLookup at hf
      rcases hfind : P.assoc.find? (fun e => decide (e.1 = tr ∧ e.2.1 = t.norm P.assoc)) with _ | e
      · rw [hfind] at hf; simp at hf
      · rw [hfind] at hf; simp at hf; subst hf
        exact hall e (List.mem_of_find?_eq_some hfind)

end Toy.MonoShim
