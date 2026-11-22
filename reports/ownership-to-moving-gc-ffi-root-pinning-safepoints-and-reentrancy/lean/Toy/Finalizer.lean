import Toy.Relocation

/-!
# Finalizers: resurrection and ordering

Objects are named by identity.  `G.alive` says whether an object's storage still exists and
`G.roots` lists the objects designated by registered roots.  `Sound` is the root invariant
every handle-based interface relies on: a registered root never designates freed storage.

A finalizer body is an arbitrary function on the root list.  A body that *receives* the dying
object (`Nat → List Nat → List Nat`) can store it; a body that receives nothing can only
rearrange roots that already exist.
-/

namespace Toy

/-- Collector-visible state. -/
structure G where
  alive : Nat → Bool
  roots : List Nat

/-- No registered root designates freed storage. -/
def Sound (g : G) : Prop := ∀ o, o ∈ g.roots → g.alive o = true

/-- Run the finalizer of `d`, then free `d` unconditionally. -/
def finalizeFree (body : Nat → List Nat → List Nat) (d : Nat) (g : G) : G :=
  { alive := upd g.alive d false, roots := body d g.roots }

/-- Run the finalizer of `d`, then free `d` only if it is still unrooted. -/
def finalizeRetrace (body : Nat → List Nat → List Nat) (d : Nat) (g : G) : G :=
  { alive := if d ∈ body d g.roots then g.alive else upd g.alive d false
    roots := body d g.roots }

/-- **Resurrection breaks free-after-finalize.**  A finalizer that stores the object it is
given leaves a registered root designating freed storage. -/
theorem resurrection_dangles :
    ∃ (body : Nat → List Nat → List Nat) (d : Nat) (g : G),
      Sound g ∧ d ∉ g.roots ∧ g.alive d = true ∧ ¬ Sound (finalizeFree body d g) := by
  refine ⟨fun d r => d :: r, 0, { alive := fun _ => true, roots := [] }, ?_, ?_, rfl, ?_⟩
  · intro o ho
    cases ho
  · intro h
    cases h
  · intro hs
    have h0 : (finalizeFree (fun d r => d :: r) 0 { alive := fun _ => true, roots := [] }).alive 0
        = true := hs 0 (List.mem_cons_self ..)
    simp [finalizeFree] at h0

/-- **Re-tracing after the finalizer is sound.**  If a finalizer can add at most its own object
to the roots, freeing only when the object is still unrooted preserves the root invariant. -/
theorem retrace_sound (body : Nat → List Nat → List Nat) (d : Nat) (g : G)
    (hs : Sound g) (hd : g.alive d = true)
    (hb : ∀ o, o ∈ body d g.roots → o = d ∨ o ∈ g.roots) :
    Sound (finalizeRetrace body d g) := by
  intro o ho
  have ho' : o ∈ body d g.roots := ho
  show (if d ∈ body d g.roots then g.alive else upd g.alive d false) o = true
  by_cases hmem : d ∈ body d g.roots
  · simp only [hmem, ↓reduceIte]
    cases hb o ho' with
    | inl e => rw [e]; exact hd
    | inr r => exact hs o r
  · simp only [hmem, ↓reduceIte]
    have hne : o ≠ d := by
      intro e
      rw [e] at ho'
      exact hmem ho'
    rw [upd_other _ _ hne]
    cases hb o ho' with
    | inl e => exact absurd e hne
    | inr r => exact hs o r

/-- **A finalizer that is not given its object cannot resurrect it.**  If the body can only
keep or drop roots that already exist, free-after-finalize preserves the root invariant. -/
theorem objectless_finalizer_sound (body : List Nat → List Nat) (d : Nat) (g : G)
    (hs : Sound g) (hd : d ∉ g.roots) (hb : ∀ o, o ∈ body g.roots → o ∈ g.roots) :
    Sound (finalizeFree (fun _ => body) d g) := by
  intro o ho
  have hr : o ∈ g.roots := hb o ho
  have hne : o ≠ d := by
    intro e
    rw [e] at hr
    exact hd hr
  show upd g.alive d false o = true
  rw [upd_other _ _ hne]
  exact hs o hr

/-! ## Ordering -/

/-- Finalize the objects of `order` one at a time, freeing each right after its finalizer.
`deps d` lists the objects the finalizer of `d` reads.  Returns `false` if some finalizer
read freed storage. -/
def runInterleaved (deps : Nat → List Nat) : (Nat → Bool) → List Nat → Bool
  | _, [] => true
  | alive, d :: ds =>
    (deps d).all alive && runInterleaved deps (upd alive d false) ds

/-- Run every finalizer of `order` first, and free nothing until all have run. -/
def runTwoPhase (deps : Nat → List Nat) (alive : Nat → Bool) (order : List Nat) : Bool :=
  order.all (fun d => (deps d).all alive)

/-- **Interleaved free-after-finalize is order-sensitive.**  Object `0`'s finalizer reads
object `1`.  Finalizing `1` first makes `0`'s finalizer read freed storage; finalizing `0`
first does not. -/
theorem interleaved_order_sensitive :
    runInterleaved (fun d => if d = 0 then [1] else []) (fun _ => true) [1, 0] = false ∧
    runInterleaved (fun d => if d = 0 then [1] else []) (fun _ => true) [0, 1] = true := by
  constructor <;> decide

/-- **Two-phase finalization is order-insensitive.**  If every finalizer's dependencies exist
when finalization starts, no finalizer reads freed storage, for every order. -/
theorem two_phase_order_insensitive (deps : Nat → List Nat) (alive : Nat → Bool)
    (order : List Nat) (h : ∀ d, d ∈ order → ∀ o, o ∈ deps d → alive o = true) :
    runTwoPhase deps alive order = true := by
  unfold runTwoPhase
  rw [List.all_eq_true]
  intro d hd
  rw [List.all_eq_true]
  intro o ho
  exact h d hd o ho

end Toy
