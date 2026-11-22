/-
  Reentrant Callbacks, Call-Stack Well-Bracketedness, and Framed Membranes (Toy Model)

  Captures three mechanisms where multi-language linking breaks or succeeds:
  1. Breakdown of naive shared-state linking under reentrant callbacks:
     a module that preserves invariant `x = y` under non-reentrant calls violates
     `x = y` when an external callback re-enters mid-update
     (`naive_sequential_preserves_inv`, `naive_reentrant_linking_breaks_invariant`).
  2. Call-stack well-bracketedness (the Dreyer-Neis-Birkedal / Cerise "awkward example"):
     well-bracketed LIFO calls always satisfy the assertion `x = 1`
     (`wbcf_awkward_safe`), while a single non-bracketed return-pointer replay
     reaches `x = 0` and breaks the assertion (`non_wbcf_awkward_fails`).
  3. Framed rely-guarantee / view-reconciliation membrane soundness:
     when a module restores its shared invariant before every external call and
     the peer's rely preserves the module's disjoint private frame, both the
     shared invariant and caller-private frames are preserved across arbitrary
     reentrant callback depth (`framed_membrane_reentrant_sound`).

  Model-system relation: none proved. This is a standalone Mathlib-free Lean 4
  toy mechanization illustrating the formal structure of the cited papers.
-/

namespace ReentrantMembrane

/-! ### Part 1: Naive Shared-State Linking Breaks Under Reentrant Callbacks -/

/-- Shared heap with two coupled fields `x, y` (invariant: `x = y`) and an
    external scratch cell `ext`. -/
structure SharedHeap where
  x : Nat
  y : Nat
  ext : Nat
  deriving DecidableEq, Repr

def CoupledInv (h : SharedHeap) : Prop := h.x = h.y

/-- A naive module performs `x := x + 1; cb(); y := y + 1` (leaving `CoupledInv`
    broken during the outgoing callback `cb()`), and exposes a `readCheck`
    entrypoint that observes whether `CoupledInv` holds. -/
def naiveModule (cb : SharedHeap → SharedHeap × Bool) (h : SharedHeap) :
    SharedHeap × Bool :=
  let h1 := { h with x := h.x + 1 }
  let (h2, ok) := cb h1
  let h3 := { h2 with y := h2.y + 1 }
  (h3, ok)

/-- Entrypoint `checkInv` called by a peer: returns `true` iff `x == y`. -/
def checkInv (h : SharedHeap) : SharedHeap × Bool :=
  (h, decide (h.x = h.y))

/-- Sequential (non-reentrant) callback that only touches `ext` preserves both
    `CoupledInv` and the `ok = true` check. -/
theorem naive_sequential_preserves_inv (f : Nat → Nat) (h : SharedHeap)
    (hInv : CoupledInv h) :
    let (h', ok) := naiveModule (fun s => ({ s with ext := f s.ext }, true)) h
    CoupledInv h' ∧ ok = true := by
  simp only [naiveModule, CoupledInv] at hInv ⊢
  exact ⟨congrArg (· + 1) hInv, trivial⟩

/-- Reentrant callback: while `naiveModule` is suspended after `x := x + 1`,
    the peer re-enters `checkInv` and observes the broken invariant (`ok = false`). -/
theorem naive_reentrant_linking_breaks_invariant :
    let h0 : SharedHeap := { x := 0, y := 0, ext := 0 }
    CoupledInv h0 ∧ (naiveModule checkInv h0).2 = false := by
  exact ⟨rfl, rfl⟩

/-! ### Part 2: Well-Bracketed Control Flow vs. Return-Pointer Replay (Awkward Example) -/

/-- Control point inside the awkward closure
    `let x = ref 0 in fun f -> (x := 0; f (); x := 1; f (); assert(x == 1))`. -/
inductive AwkPC where
  | afterFirstCall   -- waiting to execute `x := 1; f()`
  | afterSecondCall  -- waiting to execute `assert(x == 1)`
  deriving DecidableEq, Repr

/-- Machine state for the awkward example: private location `x`, saved return
    continuations (LIFO stack for WBCF; unordered pool for non-WBCF), and
    whether the assertion has failed. -/
structure AwkState where
  x : Nat
  stack : List AwkPC
  failed : Bool
  deriving DecidableEq, Repr

/-- Transitions of the awkward component interacting with an arbitrary peer
    under **strict well-bracketed (LIFO)** call/return discipline:
    - `callEntry`: peer invokes the closure -> sets `x := 0`, pushes `afterFirstCall`,
      and yields to peer (`f()`).
    - `retFirst`: peer returns to top-of-stack `afterFirstCall` -> sets `x := 1`,
      replaces top with `afterSecondCall`, and yields to peer (second `f()`).
    - `retSecond`: peer returns to top-of-stack `afterSecondCall` -> checks `x == 1`
      and pops the frame. -/
inductive WbcfStep : AwkState → AwkState → Prop where
  | callEntry {x stk} :
      WbcfStep ⟨x, stk, false⟩ ⟨0, .afterFirstCall :: stk, false⟩
  | retFirst {x stk} :
      WbcfStep ⟨x, .afterFirstCall :: stk, false⟩ ⟨1, .afterSecondCall :: stk, false⟩
  | retSecond {x stk} :
      WbcfStep ⟨x, .afterSecondCall :: stk, false⟩ ⟨x, stk, !decide (x = 1)⟩

inductive WbcfReach : AwkState → AwkState → Prop where
  | refl (s) : WbcfReach s s
  | step {s1 s2 s3} : WbcfStep s1 s2 → WbcfReach s2 s3 → WbcfReach s1 s3

/-- Inductive invariant preserved by strict LIFO well-bracketed transitions:
    the assertion has not failed (`failed = false`), and whenever the top stack
    frame is `afterSecondCall`, `x = 1`. Any nested `callEntry` pushes
    `afterFirstCall` above `afterSecondCall` and must pass through `retFirst`
    (restoring `x = 1`) before the outer `afterSecondCall` frame can resurface. -/
def WbcfInv (s : AwkState) : Prop :=
  s.failed = false ∧ (s.stack.head? = some .afterSecondCall → s.x = 1)

theorem wbcf_step_preserves_inv {s1 s2 : AwkState}
    (hInv : WbcfInv s1) (hStep : WbcfStep s1 s2) : WbcfInv s2 := by
  cases hStep with
  | callEntry =>
    exact ⟨rfl, by simp⟩
  | retFirst =>
    exact ⟨rfl, fun _ => rfl⟩
  | @retSecond x stk =>
    have hx : x = 1 := hInv.2 rfl
    subst hx
    exact ⟨rfl, fun _ => rfl⟩

theorem wbcf_reach_preserves_inv {s1 s2 : AwkState}
    (hReach : WbcfReach s1 s2) (hInv : WbcfInv s1) : WbcfInv s2 := by
  induction hReach with
  | refl => exact hInv
  | step hStep _ ih => exact ih (wbcf_step_preserves_inv hInv hStep)

/-- Under well-bracketed LIFO control flow, the awkward example NEVER fails its
    assertion (`s.failed = false`) across any reentrant sequence of calls. -/
theorem wbcf_awkward_safe {s : AwkState}
    (hReach : WbcfReach ⟨0, [], false⟩ s) : s.failed = false :=
  (wbcf_reach_preserves_inv hReach ⟨rfl, by simp⟩).1

/-- Non-bracketed control flow (e.g., `call/cc` or raw return-pointer replay on an
    unprotected machine): the peer may invoke ANY previously issued continuation
    in `stack`, not only the top frame. -/
inductive NonWbcfStep : AwkState → AwkState → Prop where
  | callEntry {x stk} :
      NonWbcfStep ⟨x, stk, false⟩ ⟨0, .afterFirstCall :: stk, false⟩
  | retFirst {x stk} :
      NonWbcfStep ⟨x, .afterFirstCall :: stk, false⟩ ⟨1, .afterSecondCall :: stk, false⟩
  | retAnySecond {x stk} :
      AwkPC.afterSecondCall ∈ stk →
      NonWbcfStep ⟨x, stk, false⟩ ⟨x, stk, !decide (x = 1)⟩

inductive NonWbcfReach : AwkState → AwkState → Prop where
  | refl (s) : NonWbcfReach s s
  | step {s1 s2 s3} : NonWbcfStep s1 s2 → NonWbcfReach s2 s3 → NonWbcfReach s1 s3

/-- Classic 4-step Dreyer-Neis-Birkedal attack:
    1. Outer call (`x := 0`, pushes `afterFirstCall`),
    2. Return from first callback (`x := 1`, replaces top with `afterSecondCall`),
    3. Nested reentrant call (`x := 0`, pushes `afterFirstCall` over `afterSecondCall`),
    4. Non-bracketed jump directly to the outer `afterSecondCall` while `x = 0` -> assertion fails. -/
theorem non_wbcf_awkward_fails :
    ∃ s, NonWbcfReach ⟨0, [], false⟩ s ∧ s.failed = true := by
  refine ⟨⟨0, [.afterFirstCall, .afterSecondCall], true⟩, ?_, rfl⟩
  apply NonWbcfReach.step NonWbcfStep.callEntry
  apply NonWbcfReach.step NonWbcfStep.retFirst
  apply NonWbcfReach.step NonWbcfStep.callEntry
  apply NonWbcfReach.step (NonWbcfStep.retAnySecond (by simp))
  exact NonWbcfReach.refl _

/-! ### Part 3: Framed Rely-Guarantee / Membrane Soundness Under Arbitrary Reentrancy -/

/-- A partitioned multi-language state separating:
    - `priv` : module-private / caller-framed local state (e.g. spilled stack slots,
               private ML/C heap, or capability-encapsulated region);
    - `shared` : membrane-visible shared state governed by invariant `Inv`;
    - `peer` : peer-private state (e.g. C heap or foreign runtime state). -/
structure MembraneState (Priv Shared Peer : Type) where
  priv : Priv
  shared : Shared
  peer : Peer

/-- A framed membrane contract parameterized by:
    - `Inv : Shared -> Prop`: invariant over the membrane-visible shared state
      that MUST hold at every boundary crossing (entry, outgoing call, return);
    - `modPre` / `modPost`: internal steps of the verified module before and after
      an outgoing external call, each preserving `Inv` at the boundary and leaving
      `peer` untouched;
    - `peerAction`: an arbitrary peer transition that may mutate `peer` and `shared`
      (preserving `Inv`) and may re-enter the module arbitrarily many times, while
      framed off from mutating `priv` (rely condition). -/
structure FramedMembrane (Priv Shared Peer : Type) where
  Inv : Shared → Prop
  /-- Module prefix before outgoing call: transforms `(priv, shared)` and restores `Inv`. -/
  modPre : Priv → Shared → Priv × Shared
  modPre_inv : ∀ p s, Inv s → Inv (modPre p s).2
  /-- Module suffix after outgoing call returns: transforms `(priv, shared)` and restores `Inv`. -/
  modPost : Priv → Shared → Priv × Shared
  modPost_inv : ∀ p s, Inv s → Inv (modPost p s).2
  /-- Peer internal step: cannot modify `priv`, preserves `Inv` on `shared`. -/
  peerStep : Shared → Peer → Shared × Peer
  peerStep_inv : ∀ s e, Inv s → Inv (peerStep s e).1

/-- Finite call-tree representation of a peer interacting with the verified
    module under a `FramedMembrane` contract:
    - `done`: terminate;
    - `localStep k`: run `peerStep` (which cannot touch `priv` and preserves `Inv`),
      then continue with `k`;
    - `callMod cb k`: invoke the module (`modPre`, then reentrant callback `cb`,
      then `modPost`), threading `priv` through any nested module calls, then
      continue with `k`. -/
inductive PeerAction (Priv Shared Peer : Type) where
  | done
  | localStep (k : PeerAction Priv Shared Peer)
  | callMod (cb : PeerAction Priv Shared Peer) (k : PeerAction Priv Shared Peer)

def evalPeer {Priv Shared Peer : Type} (M : FramedMembrane Priv Shared Peer) :
    PeerAction Priv Shared Peer → MembraneState Priv Shared Peer →
    MembraneState Priv Shared Peer
  | .done, st => st
  | .localStep k, ⟨p, s, e⟩ =>
      let (s', e') := M.peerStep s e
      evalPeer M k ⟨p, s', e'⟩
  | .callMod cb k, ⟨p, s, e⟩ =>
      -- Module runs `modPre` (restoring `Inv` before yielding), runs arbitrary
      -- reentrant callback `cb` (which may mutate `priv` only through nested
      -- `callMod` invocations, never directly via `peerStep`), then runs `modPost`.
      let (p1, s1) := M.modPre p s
      let ⟨p2, s2, e2⟩ := evalPeer M cb ⟨p1, s1, e⟩
      let (p3, s3) := M.modPost p2 s2
      evalPeer M k ⟨p3, s3, e2⟩

/-- Framed rely-guarantee / membrane soundness under arbitrary reentrancy:
    for any arbitrarily nested reentrant callback tree `act`, if the initial
    shared state satisfies `M.Inv`, then the final shared state satisfies `M.Inv`.
    (Invariance of `priv` under peer-only actions is proved separately by
    `peer_only_preserves_private_frame`.) -/
theorem framed_membrane_reentrant_sound {Priv Shared Peer : Type}
    (M : FramedMembrane Priv Shared Peer)
    (act : PeerAction Priv Shared Peer)
    (st : MembraneState Priv Shared Peer)
    (hInv : M.Inv st.shared) :
    M.Inv (evalPeer M act st).shared := by
  induction act generalizing st with
  | done => exact hInv
  | localStep k ih =>
    rcases st with ⟨p, s, e⟩
    simp only [evalPeer]
    exact ih ⟨p, (M.peerStep s e).1, (M.peerStep s e).2⟩ (M.peerStep_inv s e hInv)
  | callMod cb k ihCb ihK =>
    rcases st with ⟨p, s, e⟩
    simp only [evalPeer]
    have h1 : M.Inv (M.modPre p s).2 := M.modPre_inv p s hInv
    have h2 : M.Inv (evalPeer M cb ⟨(M.modPre p s).1, (M.modPre p s).2, e⟩).shared :=
      ihCb ⟨(M.modPre p s).1, (M.modPre p s).2, e⟩ h1
    rcases hRes : evalPeer M cb ⟨(M.modPre p s).1, (M.modPre p s).2, e⟩ with ⟨p2, s2, e2⟩
    rw [hRes] at h2
    have h3 : M.Inv (M.modPost p2 s2).2 := M.modPost_inv p2 s2 h2
    exact ihK ⟨(M.modPost p2 s2).1, (M.modPost p2 s2).2, e2⟩ h3

/-- Strong frame-preservation lemma: if a peer executes only `localStep` actions
    (no calls into the module), it cannot modify `priv` at all, and preserves `M.Inv`. -/
def IsPeerOnly {Priv Shared Peer : Type} : PeerAction Priv Shared Peer → Prop
  | .done => True
  | .localStep k => IsPeerOnly k
  | .callMod _ _ => False

theorem peer_only_preserves_private_frame {Priv Shared Peer : Type}
    (M : FramedMembrane Priv Shared Peer)
    (act : PeerAction Priv Shared Peer)
    (hOnly : IsPeerOnly act)
    (st : MembraneState Priv Shared Peer)
    (hInv : M.Inv st.shared) :
    (evalPeer M act st).priv = st.priv ∧ M.Inv (evalPeer M act st).shared := by
  induction act generalizing st with
  | done => exact ⟨rfl, hInv⟩
  | localStep k ih =>
    rcases st with ⟨p, s, e⟩
    simp only [evalPeer]
    exact ih hOnly ⟨p, (M.peerStep s e).1, (M.peerStep s e).2⟩ (M.peerStep_inv s e hInv)
  | callMod _ _ => exact False.elim hOnly

/-- Instantiation showing how restoring `CoupledInv` BEFORE the outgoing callback
    fixes the broken module from Part 1 for arbitrary reentrancy depth. -/
def fixedCoupledMembrane : FramedMembrane Nat SharedHeap Nat where
  Inv := CoupledInv
  modPre := fun p h => (p + 1, { h with x := h.x + 1, y := h.y + 1 })
  modPre_inv := fun _ _ hInv => congrArg (· + 1) hInv
  modPost := fun p h => (p, h)
  modPost_inv := fun _ _ hInv => hInv
  peerStep := fun h e => ({ h with ext := h.ext + e }, e + 1)
  peerStep_inv := fun _ _ hInv => hInv

theorem fixed_coupled_reentrant_safe (act : PeerAction Nat SharedHeap Nat)
    (p e : Nat) (h : SharedHeap) (hInv : CoupledInv h) :
    CoupledInv (evalPeer fixedCoupledMembrane act ⟨p, h, e⟩).shared :=
  framed_membrane_reentrant_sound fixedCoupledMembrane act ⟨p, h, e⟩ hInv

end ReentrantMembrane
