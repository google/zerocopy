/-!
# Hook attachment and noninterference

Standalone Lean `v4.34.1` file (core library only; no `sorry`, no `axiom`).

A loaded kernel module attached to a hook (an endpoint, a notification, an
interrupt) runs in supervisor mode whenever the hook fires. The companion SFI model
(`SmodeSfiChecker.lean`) shows that an admitted module is a deterministic,
terminating function of the context bytes it is handed and of its own scratch
bytes. This file takes that result as the *definition* of a module — an
arbitrary function from (context, scratch) to (scratch, verdict, cost) — and
asks which attachments keep a two-domain kernel noninterfering.

* `fire` is the kernel transition for one hook activation: the module reads the
  triggering domain's context, updates its scratch, returns a verdict into the
  triggering domain's context, and its running time is charged to the
  triggering domain.
* `same_domain_step_consistent` and `same_domain_locally_respects`: if the
  triggering domain is the domain that owns the module and its scratch, hook
  activation satisfies both unwinding conditions for **every** module.
* `cross_domain_verdict_leaks`, `cross_domain_time_leaks`,
  `cross_domain_scratch_absorbs`: if a hook owned by one domain fires in the
  context of the other, there are modules that leak in either direction,
  through the verdict, through running time, and through the scratch.
-/

namespace HookNoninterference

inductive Dom where
  | lo | hi
  deriving DecidableEq, Repr

/-- Behavior of an admitted module on one activation:
`f ctx scratch = (scratch', verdict, cost)`. -/
abbrev Module := Nat → Nat → Nat × Nat × Nat

/-- Abstract kernel state. `owner` labels the module, its scratch region, and
the hook object it is attached to. -/
structure KState where
  owner   : Dom
  scratch : Nat          -- the module's persistent scratch region
  obs     : Dom → Nat    -- each domain's own state (message registers, IPC outcome)
  clock   : Dom → Nat    -- time consumed in each domain's slices

/-- One hook activation in the context of domain `trig`: for an endpoint hook
`trig` is the domain performing the IPC; for an interrupt hook `trig` is the
domain whose slice is running when the interrupt is taken. -/
def fire (m : Module) (trig : Dom) (s : KState) : KState :=
  { s with
    scratch := (m (s.obs trig) s.scratch).1
    obs := fun d => if d = trig then (m (s.obs trig) s.scratch).2.1 else s.obs d
    clock := fun d => if d = trig then s.clock d + (m (s.obs trig) s.scratch).2.2 else s.clock d }

/-- What domain `d` can observe: its own state, its own consumed time, and the
module's scratch if it owns the module. -/
def ObsEq (d : Dom) (s t : KState) : Prop :=
  s.owner = t.owner ∧ s.obs d = t.obs d ∧ s.clock d = t.clock d ∧
  (s.owner = d → s.scratch = t.scratch)

/-- **Step consistency under the same-domain rule.** If the hook fires only in
the context of the module's owner, two states that a domain cannot tell apart
remain indistinguishable to it after the activation — for every module. -/
theorem same_domain_step_consistent (m : Module) (d : Dom) (s t : KState)
    (h : ObsEq d s t) : ObsEq d (fire m s.owner s) (fire m t.owner t) := by
  obtain ⟨ho, hobs, hclk, hscr⟩ := h
  by_cases hd : s.owner = d
  · have hs := hscr hd
    have ht : t.owner = d := ho ▸ hd
    subst hd
    refine ⟨ho, ?_, ?_, ?_⟩
    · show (if s.owner = s.owner then (m (s.obs s.owner) s.scratch).2.1 else s.obs s.owner)
        = (if s.owner = t.owner then (m (t.obs t.owner) t.scratch).2.1 else t.obs s.owner)
      rw [← ho, ← hobs, ← hs]
    · show (if s.owner = s.owner then s.clock s.owner + (m (s.obs s.owner) s.scratch).2.2
            else s.clock s.owner)
        = (if s.owner = t.owner then t.clock s.owner + (m (t.obs t.owner) t.scratch).2.2
            else t.clock s.owner)
      rw [← ho, ← hobs, ← hs, ← hclk]
    · intro _
      show (m (s.obs s.owner) s.scratch).1 = (m (t.obs t.owner) t.scratch).1
      rw [← ho, ← hobs, ← hs]
  · have ht : t.owner ≠ d := ho ▸ hd
    refine ⟨ho, ?_, ?_, ?_⟩
    · show (if d = s.owner then _ else s.obs d) = (if d = t.owner then _ else t.obs d)
      rw [if_neg (fun e => hd e.symm), if_neg (fun e => ht e.symm)]
      exact hobs
    · show (if d = s.owner then _ else s.clock d) = (if d = t.owner then _ else t.clock d)
      rw [if_neg (fun e => hd e.symm), if_neg (fun e => ht e.symm)]
      exact hclk
    · intro e
      exact absurd e hd

/-- **Local respect under the same-domain rule.** An activation in the owner's
context is invisible to the other domain — for every module. -/
theorem same_domain_locally_respects (m : Module) (d : Dom) (s : KState)
    (hd : s.owner ≠ d) : ObsEq d (fire m s.owner s) s := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · show (if d = s.owner then _ else s.obs d) = s.obs d
    rw [if_neg (fun e => hd e.symm)]
  · show (if d = s.owner then _ else s.clock d) = s.clock d
    rw [if_neg (fun e => hd e.symm)]
  · intro e
    exact absurd e hd

/-- Two states that differ only in the secret held in a `hi`-owned module's
scratch. -/
def sLeak (secret : Nat) : KState :=
  { owner := .hi, scratch := secret, obs := fun _ => 0, clock := fun _ => 0 }

/-- **A `hi`-owned filter on a `lo` endpoint leaks through its verdict.** The
module returns its scratch as the verdict; `lo` reads the secret out of its own
IPC outcome. -/
theorem cross_domain_verdict_leaks :
    ObsEq .lo (sLeak 0) (sLeak 1) ∧
    ¬ ObsEq .lo (fire (fun _ sc => (sc, sc, 0)) .lo (sLeak 0))
                (fire (fun _ sc => (sc, sc, 0)) .lo (sLeak 1)) := by
  refine ⟨⟨rfl, rfl, rfl, fun e => by cases e⟩, ?_⟩
  intro h
  have h2 : (fire (fun _ sc => (sc, sc, 0)) .lo (sLeak 0)).obs .lo
      = (fire (fun _ sc => (sc, sc, 0)) .lo (sLeak 1)).obs .lo := h.2.1
  exact absurd h2 (by decide)

/-- **A `hi`-owned observer on a `lo` hook leaks through running time.** The
module returns a constant verdict but runs for a secret-dependent number of
instructions, which are charged to `lo`. -/
theorem cross_domain_time_leaks :
    ObsEq .lo (sLeak 0) (sLeak 1) ∧
    ¬ ObsEq .lo (fire (fun _ sc => (sc, 0, sc)) .lo (sLeak 0))
                (fire (fun _ sc => (sc, 0, sc)) .lo (sLeak 1)) := by
  refine ⟨⟨rfl, rfl, rfl, fun e => by cases e⟩, ?_⟩
  intro h
  have h2 : (fire (fun _ sc => (sc, 0, sc)) .lo (sLeak 0)).clock .lo
      = (fire (fun _ sc => (sc, 0, sc)) .lo (sLeak 1)).clock .lo := h.2.2.1
  exact absurd h2 (by decide)

/-- Two states that differ only in `lo`'s own state. -/
def sAbsorb (loSecret : Nat) : KState :=
  { owner := .hi, scratch := 0, obs := fun d => if d = .lo then loSecret else 0,
    clock := fun _ => 0 }

/-- **The reverse direction.** A `hi`-owned module on a `lo` hook copies `lo`'s
context into `hi`-readable scratch; this is a flow from `lo` to `hi` created by
the attachment alone, whatever the capability-level policy says. -/
theorem cross_domain_scratch_absorbs :
    ObsEq .hi (sAbsorb 0) (sAbsorb 1) ∧
    ¬ ObsEq .hi (fire (fun ctx _ => (ctx, 0, 0)) .lo (sAbsorb 0))
                (fire (fun ctx _ => (ctx, 0, 0)) .lo (sAbsorb 1)) := by
  refine ⟨⟨rfl, rfl, rfl, fun _ => rfl⟩, ?_⟩
  intro h
  have h2 : (fire (fun ctx _ => (ctx, 0, 0)) .lo (sAbsorb 0)).scratch
      = (fire (fun ctx _ => (ctx, 0, 0)) .lo (sAbsorb 1)).scratch := h.2.2.2 rfl
  exact absurd h2 (by decide)

end HookNoninterference
