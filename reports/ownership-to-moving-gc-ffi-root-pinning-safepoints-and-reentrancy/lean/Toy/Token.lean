import Toy.Relocation

/-!
# Branded safepoint tokens: a static discipline for raw views of movable objects

Native code is a straight-line list of operations.  It may

* `load x s`     — copy the current flat address of handle `s` into local `x` (an unrooted
                   raw view, as a C local of type `value`, a `Value<'a>`, or a raw array
                   pointer would be);
* `pinLoad x s`  — pin the object designated by `s`, then take its flat address;
* `unpinAll`     — leave the pinned region, releasing every pin taken so far;
* `use x`        — dereference the flat address in `x` directly;
* `useH s`       — dereference through the handle;
* `safepoint`    — call into the runtime: allocate, release and re-acquire the runtime lock,
                   or call back into managed code.  The runtime may then relocate objects any
                   number of times, and reentrant code may overwrite payloads (`RtStep`).

The collector never sees the locals `x`: it rewrites root slots, not raw views.

The static discipline (`check`) brands every raw view with the *epoch* of the token it was
borrowed under.  A `safepoint` consumes the token and issues the next epoch, which is how a
function taking the runtime handle by unique borrow invalidates every value borrowed from
it.  `use x` is accepted only for a view branded with the current epoch, or a pinned view.

`branded_tokens_sound` shows that accepted programs never dereference a stale flat address,
for every relocation choice and every reentrant write.  `unbranded_use_is_stale` shows the
discipline is not vacuous: the three-instruction program it rejects does go stale.
-/

namespace Toy

/-- What the runtime may do while native code sits at a safepoint. -/
inductive RtStep : Heap → Heap → Prop
  /-- a collection with an arbitrary legal relocation -/
  | gc {h h' : Heap} (f : Addr → Addr) : Moves f h h' → RtStep h h'
  /-- reentrant code overwrites the payload of some live object -/
  | write (h : Heap) (a : Addr) (v : Val) : h.mem a ≠ none →
      RtStep h { h with mem := upd h.mem a (some v) }

abbrev Var := Nat

/-- Native-code operations. -/
inductive Op where
  | load (x : Var) (s : Slot)
  | pinLoad (x : Var) (s : Slot)
  | unpinAll
  | use (x : Var)
  | useH (s : Slot)
  | safepoint

/-- Static brand of a raw view. -/
inductive Brand where
  /-- borrowed from the runtime token at this epoch -/
  | tok (epoch : Nat)
  /-- guarded by a pin -/
  | pinned

abbrev Ctx := Var → Option Brand

/-- Run-time locals: a flat address, together with the slot it was read from.  The slot is
ghost information used only to *state* staleness; no operation inspects it. -/
abbrev Env := Var → Option (Slot × Addr)

/-- May a view with this brand be dereferenced under the token of epoch `n`? -/
def usable (n : Nat) : Option Brand → Bool
  | some (.tok e) => e == n
  | some .pinned => true
  | none => false

/-- Forget every pinned view. -/
def dropPins (Γ : Ctx) : Ctx := fun y =>
  match Γ y with
  | some .pinned => none
  | o => o

/-- The static discipline.  `n` is the epoch of the token currently held. -/
def check : Nat → Ctx → List Op → Bool
  | _, _, [] => true
  | n, Γ, .load x _ :: ops => check n (upd Γ x (some (.tok n))) ops
  | n, Γ, .pinLoad x _ :: ops => check n (upd Γ x (some .pinned)) ops
  | n, Γ, .unpinAll :: ops => check n (dropPins Γ) ops
  | n, Γ, .use x :: ops => usable n (Γ x) && check n Γ ops
  | n, Γ, .useH _ :: ops => check n Γ ops
  | n, Γ, .safepoint :: ops => check (n + 1) Γ ops

/-- The raw view obtained from handle `s` right now. -/
def view (h : Heap) (s : Slot) : Option (Slot × Addr) := (h.roots s).map (fun a => (s, a))

/-- Pin the object currently designated by `s`. -/
def pinAt (h : Heap) (s : Slot) : Heap :=
  { h with pin := fun b => if h.roots s = some b then true else h.pin b }

/-- Release every pin. -/
def unpin (h : Heap) : Heap := { h with pin := fun _ => false }

/-- `Stale h env ops`: some execution of `ops` from heap `h` and locals `env` dereferences a
flat address that is no longer the address its handle designates.  The semantics performs no
check of its own: `use` reads whatever address the local holds. -/
inductive Stale : Heap → Env → List Op → Prop
  | here {h : Heap} {env : Env} {x : Var} {s : Slot} {a : Addr} {ops : List Op} :
      env x = some (s, a) → h.roots s ≠ some a → Stale h env (.use x :: ops)
  | use {h : Heap} {env : Env} {x : Var} {ops : List Op} :
      Stale h env ops → Stale h env (.use x :: ops)
  | useH {h : Heap} {env : Env} {s : Slot} {ops : List Op} :
      Stale h env ops → Stale h env (.useH s :: ops)
  | load {h : Heap} {env : Env} {x : Var} {s : Slot} {ops : List Op} :
      Stale h (upd env x (view h s)) ops → Stale h env (.load x s :: ops)
  | pinLoad {h : Heap} {env : Env} {x : Var} {s : Slot} {ops : List Op} :
      Stale (pinAt h s) (upd env x (view h s)) ops → Stale h env (.pinLoad x s :: ops)
  | unpinAll {h : Heap} {env : Env} {ops : List Op} :
      Stale (unpin h) env ops → Stale h env (.unpinAll :: ops)
  | safepoint {h h' : Heap} {env : Env} {ops : List Op} :
      Star RtStep h h' → Stale h' env ops → Stale h env (.safepoint :: ops)

/-- A view that is not stale reads exactly what its handle reads. -/
theorem current_view_reads_as_handle {h : Heap} {s : Slot} {a : Addr}
    (cur : h.roots s = some a) : readRaw h a = readHandle h s := by
  simp [readRaw, readHandle, cur]

/-- The invariant linking static brands to run-time facts. -/
structure Inv (n : Nat) (Γ : Ctx) (h : Heap) (env : Env) : Prop where
  /-- no brand is from the future -/
  bound  : ∀ x e, Γ x = some (.tok e) → e ≤ n
  /-- a view branded with the current epoch is current -/
  fresh  : ∀ x s a, env x = some (s, a) → Γ x = some (.tok n) → h.roots s = some a
  /-- a pinned view is current and its object is pinned -/
  pinned : ∀ x s a, env x = some (s, a) → Γ x = some .pinned →
      h.roots s = some a ∧ h.pin a = true

/-- A pinned view stays current across everything the runtime may do at a safepoint. -/
theorem rt_keeps_pinned_view {h h' : Heap} (st : Star RtStep h h') {s : Slot} {a : Addr}
    (cur : h.roots s = some a) (hp : h.pin a = true) :
    h'.roots s = some a ∧ h'.pin a = true := by
  induction st with
  | refl _ => exact ⟨cur, hp⟩
  | step hab _ ih =>
    cases hab with
    | gc f m =>
      apply ih
      · rw [m.roots_fwd s, cur]
        simp [m.pinned_fixed a hp]
      · rw [m.pin_same]
        exact hp
    | write _ _ _ => exact ih cur hp

/-- (b, part 2) **Soundness of branded safepoint tokens.**  A program accepted by `check`
never dereferences a stale flat address, whatever relocations the collector chooses and
whatever payload writes reentrant code performs at each safepoint. -/
theorem branded_tokens_sound : ∀ (ops : List Op) (n : Nat) (Γ : Ctx) (h : Heap) (env : Env),
    check n Γ ops = true → Inv n Γ h env → ¬ Stale h env ops := by
  intro ops
  induction ops with
  | nil =>
    intro n Γ h env _ _ hst
    cases hst
  | cons op ops ih =>
    intro n Γ h env hc inv hst
    cases op with
    | load x s =>
      cases hst with
      | load hst' =>
        refine ih n _ h _ hc ?_ hst'
        refine ⟨?_, ?_, ?_⟩
        · intro y e hy
          by_cases hyx : y = x
          · subst hyx
            rw [upd_same] at hy
            cases hy
            exact Nat.le_refl _
          · rw [upd_other _ _ hyx] at hy
            exact inv.bound y e hy
        · intro y s' a hy hΓ
          by_cases hyx : y = x
          · subst hyx
            rw [upd_same] at hy
            unfold view at hy
            cases hr : h.roots s with
            | none => rw [hr] at hy; cases hy
            | some a' =>
              rw [hr] at hy
              simp at hy
              obtain ⟨hs, ha⟩ := hy
              subst hs
              subst ha
              exact hr
          · rw [upd_other _ _ hyx] at hy hΓ
            exact inv.fresh y s' a hy hΓ
        · intro y s' a hy hΓ
          by_cases hyx : y = x
          · subst hyx
            rw [upd_same] at hΓ
            cases hΓ
          · rw [upd_other _ _ hyx] at hy hΓ
            exact inv.pinned y s' a hy hΓ
    | pinLoad x s =>
      cases hst with
      | pinLoad hst' =>
        refine ih n _ _ _ hc ?_ hst'
        refine ⟨?_, ?_, ?_⟩
        · intro y e hy
          by_cases hyx : y = x
          · subst hyx
            rw [upd_same] at hy
            cases hy
          · rw [upd_other _ _ hyx] at hy
            exact inv.bound y e hy
        · intro y s' a hy hΓ
          by_cases hyx : y = x
          · subst hyx
            rw [upd_same] at hΓ
            cases hΓ
          · rw [upd_other _ _ hyx] at hy hΓ
            exact inv.fresh y s' a hy hΓ
        · intro y s' a hy hΓ
          by_cases hyx : y = x
          · subst hyx
            rw [upd_same] at hy
            unfold view at hy
            cases hr : h.roots s with
            | none => rw [hr] at hy; cases hy
            | some a' =>
              rw [hr] at hy
              simp at hy
              obtain ⟨hs, ha⟩ := hy
              subst hs
              subst ha
              refine ⟨hr, ?_⟩
              show (if h.roots s = some a' then true else h.pin a') = true
              simp [hr]
          · rw [upd_other _ _ hyx] at hy hΓ
            obtain ⟨c, p⟩ := inv.pinned y s' a hy hΓ
            refine ⟨c, ?_⟩
            show (if h.roots s = some a then true else h.pin a) = true
            simp [p]
    | unpinAll =>
      cases hst with
      | unpinAll hst' =>
        refine ih n _ _ env hc ?_ hst'
        have key : ∀ y b, dropPins Γ y = some b → Γ y = some b ∧ b ≠ .pinned := by
          intro y b hb
          unfold dropPins at hb
          cases hΓy : Γ y with
          | none => rw [hΓy] at hb; cases hb
          | some b' =>
            rw [hΓy] at hb
            cases b' with
            | tok e =>
              simp at hb
              subst hb
              exact ⟨rfl, fun c => by cases c⟩
            | pinned => simp at hb
        refine ⟨?_, ?_, ?_⟩
        · intro y e hy
          exact inv.bound y e (key y _ hy).1
        · intro y s' a hy hΓ
          exact inv.fresh y s' a hy (key y _ hΓ).1
        · intro y s' a _ hΓ
          exact absurd rfl (key y _ hΓ).2
    | use x =>
      have hc' : usable n (Γ x) = true ∧ check n Γ ops = true := by
        simpa [check] using hc
      cases hst with
      | here hx hne =>
        apply hne
        cases hΓx : Γ x with
        | none =>
          rw [hΓx] at hc'
          simp [usable] at hc'
        | some b =>
          cases b with
          | tok e =>
            rw [hΓx] at hc'
            have he : e = n := by simpa [usable] using hc'.1
            subst he
            exact inv.fresh x _ _ hx hΓx
          | pinned => exact (inv.pinned x _ _ hx hΓx).1
      | use hst' => exact ih n Γ h env hc'.2 inv hst'
    | useH s =>
      cases hst with
      | useH hst' => exact ih n Γ h env hc inv hst'
    | safepoint =>
      cases hst with
      | safepoint st hst' =>
        refine ih (n + 1) Γ _ env hc ?_ hst'
        refine ⟨?_, ?_, ?_⟩
        · intro y e hy
          exact Nat.le_succ_of_le (inv.bound y e hy)
        · intro y s' a _ hΓ
          have := inv.bound y (n + 1) hΓ
          omega
        · intro y s' a hy hΓ
          obtain ⟨c, p⟩ := inv.pinned y s' a hy hΓ
          exact rt_keeps_pinned_view st c p

/-- Starting with no raw views, the invariant holds trivially. -/
theorem Inv.init (n : Nat) (h : Heap) : Inv n (fun _ => none) h (fun _ => none) where
  bound := fun _ _ hy => by cases hy
  fresh := fun _ _ _ hy _ => by cases hy
  pinned := fun _ _ _ hy _ => by cases hy

/-- (b, part 2, closed form) An accepted program run from scratch is never stale. -/
theorem branded_tokens_sound_closed (ops : List Op) (h : Heap)
    (hc : check 0 (fun _ => none) ops = true) : ¬ Stale h (fun _ => none) ops :=
  branded_tokens_sound ops 0 _ h _ hc (Inv.init 0 h)

/-! ## The discipline is not vacuous -/

/-- Take a raw view, cross a safepoint, dereference the view. -/
def staleProgram : List Op := [.load 0 0, .safepoint, .use 0]

/-- Take a raw view and use it; cross a safepoint; take the view again and use it. -/
def reloadProgram : List Op := [.load 0 0, .use 0, .safepoint, .load 0 0, .use 0, .useH 0]

/-- Pin, cross a safepoint, use the pinned view, leave the pinned region. -/
def pinnedProgram : List Op := [.pinLoad 0 0, .safepoint, .use 0, .unpinAll]

/-- Use a pinned view after leaving the pinned region and crossing a safepoint. -/
def afterUnpinProgram : List Op := [.pinLoad 0 0, .unpinAll, .safepoint, .use 0]

theorem staleProgram_rejected : check 0 (fun _ => none) staleProgram = false := by decide
theorem reloadProgram_accepted : check 0 (fun _ => none) reloadProgram = true := by decide
theorem pinnedProgram_accepted : check 0 (fun _ => none) pinnedProgram = true := by decide
theorem afterUnpinProgram_rejected :
    check 0 (fun _ => none) afterUnpinProgram = false := by decide

/-- One object with payload `7` at address `0`, designated by slot `0`; nothing pinned. -/
def heap₀ : Heap :=
  { mem := fun a => if a = 0 then some 7 else none
    roots := fun s => if s = 0 then some 0 else none
    pin := fun _ => false }

/-- (a, as a program) The rejected program really does dereference a stale flat address:
the collector moves the object from address `0` to address `1` at the safepoint, and the
local still holds `0`. -/
theorem unbranded_use_is_stale : Stale heap₀ (fun _ => none) staleProgram := by
  have live : heap₀.mem 0 = some 7 := rfl
  have free : heap₀.mem 1 = none := rfl
  obtain ⟨f, h', m, _, _, fwd, _⟩ :=
    unpinned_raw_can_dangle heap₀ (a := 0) (b := 1) live rfl free rfl
  have hr : h'.roots 0 = some 1 := fwd 0 rfl
  apply Stale.load
  apply Stale.safepoint (Star.step (RtStep.gc f m) (Star.refl h'))
  apply Stale.here (s := 0) (a := 0)
  · rfl
  · rw [hr]
    intro e
    cases e

/-- **Validity is not exclusivity.**  A pinned view stays current across a safepoint, yet the
payload read through it can differ before and after: reentrant code wrote through its own
handle.  Branding and pinning rule out stale addresses; they say nothing about who else may
access the object. -/
theorem pinned_view_valid_not_exclusive :
    ∃ (h h' : Heap) (s : Slot) (a : Addr),
      h.roots s = some a ∧ h.pin a = true ∧ Star RtStep h h' ∧
      h'.roots s = some a ∧ h'.pin a = true ∧ readRaw h' a ≠ readRaw h a := by
  refine ⟨pinAt heap₀ 0, { pinAt heap₀ 0 with mem := upd (pinAt heap₀ 0).mem 0 (some 8) },
    0, 0, rfl, rfl, ?_, rfl, rfl, ?_⟩
  · refine Star.step (RtStep.write (pinAt heap₀ 0) 0 8 ?_) (Star.refl _)
    intro e
    cases e
  · intro e
    cases e

end Toy
