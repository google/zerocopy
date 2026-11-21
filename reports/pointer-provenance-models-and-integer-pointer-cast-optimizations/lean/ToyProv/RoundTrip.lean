import ToyProv.IntEq

/-!
# R3 — Round-trip casts `int2ptr (ptr2int p)`

Two directions must be distinguished:

* **fold** `d := int2ptr k` ⟶ `d := p` (with `k == (int)p`): what an optimizer wants when it
  sees a round trip;
* **introduce** `d := p` ⟶ `d := int2ptr k`: replacing a pointer by its round trip.

"`int2ptr (ptr2int p)` behaves like `p`" means both directions preserve behaviour.
-/

namespace Toy.Prov

/-- **R3a.** In the exposed model, if in every reachable state at the rewrite point (`hk`) `k`
holds `p`'s address as an integer and (`hc`) the `int2ptr` candidates for that address are
exactly `p`'s own provenance — i.e. `p`'s allocation is live, exposed, contains the address in
its closed range, and is the *only* such allocation (or `p` has no provenance and there is no
candidate) — then `int2ptr k` and `p` are interchangeable: the two programs have equal
behaviour. Both the fold and the introduce direction are therefore refinements. -/
theorem int2ptrToCopy_beh_eq_exposed_of_intIsAddrOf_of_candEqProv
    (pre post : Prog) (d k p : Reg)
    (hk : AllAfter .exposed pre (intIsAddrOfC k p))
    (hc : AllAfter .exposed pre (candEqProvC p)) :
    beh .exposed (pre ++ .copy d p :: post) = beh .exposed (pre ++ .int2ptr d k :: post) := by
  apply beh_replace_of_step_eq
  intro s hs
  have h1 := hk s hs
  have h2 := hc s hs
  simp only [intIsAddrOfC] at h1
  split at h1
  · rename_i a x hka hpx
    simp only [candEqProvC, hpx, decide_eq_true_eq] at h2
    have hax : a = x.addr := by simpa using h1
    subst hax
    obtain ⟨prov, addr⟩ := x
    simp only at h2
    cases prov with
    | none => simp [step, hka, hpx, h2, castToPtr]
    | some A => simp [step, hka, hpx, h2, castToPtr]
  · simp at h1

/-- **R3a, `hk` needed.** (Same programs as R2b's `hk` counterexample.) -/
theorem int2ptrToCopy_beh_eq_intIsAddrOf_needed :
    AllAfter .exposed r2bPreK (candEqProvC 0) ∧
      beh .exposed (r2bPreK ++ .copy 3 0 :: r2bPostK) ≠ beh .exposed (r2bPreK ++ .int2ptr 3 2 :: r2bPostK) :=
  ⟨by decide, by decide⟩

/-- **R3a, `hc` needed; R3b.** `k := (int)p` where `p` is one past the end of A: A is live, exposed
by the cast, and contains the address in its closed range (`provIsCandC`), so the exposed set does
contain `p`'s allocation; but the adjacent B is exposed too. The round trip and `p` behave
differently: the source outputs `[7]` (its cast can pick B), the target is UB. So liveness and
exposure of `p`'s allocation do not make the fold sound. -/
theorem roundTrip_fold_counterexample_exposed_boundary :
    Int2ptrToCopy .exposed (r2bPreRT ++ .int2ptr 4 3 :: r2bPostRT) (r2bPreRT ++ .copy 4 2 :: r2bPostRT) ∧
      AllAfter .exposed r2bPreRT (provIsCandC 2) ∧
      ¬ Refines .exposed (r2bPreRT ++ .copy 4 2 :: r2bPostRT) (r2bPreRT ++ .int2ptr 4 3 :: r2bPostRT) ∧
      beh .exposed (r2bPreRT ++ .int2ptr 4 3 :: r2bPostRT) = [.done [7]] ∧
      beh .exposed (r2bPreRT ++ .copy 4 2 :: r2bPostRT) = [.ub] :=
  ⟨⟨r2bPreRT, r2bPostRT, 4, 3, 2, rfl, rfl, by decide⟩, by decide, by decide, by decide, by decide⟩

theorem int2ptrToCopy_not_sound_exposed : ¬ Sound .exposed Int2ptrToCopy :=
  fun h => roundTrip_fold_counterexample_exposed_boundary.2.2.1
    (h _ _ roundTrip_fold_counterexample_exposed_boundary.1)

/-- **R3b positive control.** The same pair is a refinement in the flat model (where the cast and
`p` are the same provenance-less pointer); in the strict model the source is UB. -/
theorem roundTrip_fold_boundary_flat_strict :
    Int2ptrToCopy .flat (r2bPreRT ++ .int2ptr 4 3 :: r2bPostRT) (r2bPreRT ++ .copy 4 2 :: r2bPostRT) ∧
      Refines .flat (r2bPreRT ++ .copy 4 2 :: r2bPostRT) (r2bPreRT ++ .int2ptr 4 3 :: r2bPostRT) ∧
      beh .flat (r2bPreRT ++ .copy 4 2 :: r2bPostRT) = [.done [7]] ∧
      beh .strict (r2bPreRT ++ .int2ptr 4 3 :: r2bPostRT) = [.ub] :=
  ⟨⟨r2bPreRT, r2bPostRT, 4, 3, 2, rfl, rfl, by decide⟩, by decide, by decide, by decide⟩

/-- A (16..18) exposed, B (18..20); `k := (int)B` (exposes B). `p` is B's *start*, in bounds
of B (`base ≤ address < base + size` holds with `address = base`). -/
def r3PreBase : Prog := [.alloc 0 2, .alloc 1 2, .ptr2int 9 0, .ptr2int 3 1]
/-- Move the cast pointer back by 2 (into A) and store through it; read A. -/
def r3PostBase : Prog := [.offset 5 4 (-2), .const 6 7, .store 5 6, .load 7 .int 0, .obs 7]

/-- **R3b, in-bounds base pointer.** The boundary problem is not specific to one-past pointers: B's
start is in bounds of B (address = base), yet it is also A's one-past address, so with A exposed the cast
has two candidates. The source's cast can pick A (moving back by 2 then stays in A) and outputs
`[7]`; the folded target keeps B's provenance and its store is UB. -/
theorem roundTrip_fold_counterexample_exposed_base_pointer :
    Int2ptrToCopy .exposed (r3PreBase ++ .int2ptr 4 3 :: r3PostBase) (r3PreBase ++ .copy 4 1 :: r3PostBase) ∧
      AllAfter .exposed r3PreBase (fun s => match s.regs 1 with
        | some (.ptr x) => canAccess .exposed s x 1 | _ => false) ∧
      AllAfter .exposed r3PreBase (provIsCandC 1) ∧ ¬ AllAfter .exposed r3PreBase (candSubProvC 1) ∧
      beh .exposed (r3PreBase ++ .int2ptr 4 3 :: r3PostBase) = [.done [7]] ∧
      beh .exposed (r3PreBase ++ .copy 4 1 :: r3PostBase) = [.ub] :=
  ⟨⟨r3PreBase, r3PostBase, 4, 3, 1, rfl, rfl, by decide⟩, by decide, by decide, by decide, by decide,
    by decide⟩

/-- **R3a non-vacuity.** After `k := (int)A` (A alone exposed), the hypotheses hold and both
programs output `[5]`. -/
def r3PostNV : Prog := [.const 3 5, .store 2 3, .load 4 .int 0, .obs 4]
theorem int2ptrToCopy_beh_eq_nonvacuous :
    AllAfter .exposed r2bPreNV (intIsAddrOfC 1 0) ∧ AllAfter .exposed r2bPreNV (candEqProvC 0) ∧
      beh .exposed (r2bPreNV ++ .copy 2 0 :: r3PostNV) = [.done [5]] :=
  ⟨by decide, by decide, by decide⟩

/-! ### R3c — strict: the round trip does not behave like `p` -/

def r3Pre : Prog := [.alloc 0 2, .ptr2int 1 0]
def r3Post : Prog := [.const 3 7, .store 2 3, .load 4 .int 0, .obs 4]

/-- **R3c.** In the strict model the round trip is not interchangeable with `p`: introducing it
(the single-instruction rewrite `d := p` ⟶ `d := int2ptr k`, here with `k := (int)p` computed
earlier) turns a program that outputs `[7]` into a UB program, so `CopyToInt2ptr` is unsound in
`strict`. -/
theorem roundTrip_counterexample_strict :
    CopyToInt2ptr .strict (r3Pre ++ .copy 2 0 :: r3Post) (r3Pre ++ .int2ptr 2 1 :: r3Post) ∧
      ¬ Refines .strict (r3Pre ++ .int2ptr 2 1 :: r3Post) (r3Pre ++ .copy 2 0 :: r3Post) ∧
      beh .strict (r3Pre ++ .copy 2 0 :: r3Post) = [.done [7]] ∧
      beh .strict (r3Pre ++ .int2ptr 2 1 :: r3Post) = [.ub] :=
  ⟨⟨r3Pre, r3Post, 2, 1, 0, rfl, rfl, by decide⟩, by decide, by decide, by decide⟩

theorem copyToInt2ptr_not_sound_strict : ¬ Sound .strict CopyToInt2ptr :=
  fun h => roundTrip_counterexample_strict.2.1 (h _ _ roundTrip_counterexample_strict.1)

/-- **R3c positive control.** The same pair is behaviour-preserving in the exposed model (A was
exposed by the cast and is the unique candidate). -/
theorem roundTrip_example_exposed :
    beh .exposed (r3Pre ++ .int2ptr 2 1 :: r3Post) = beh .exposed (r3Pre ++ .copy 2 0 :: r3Post) := by
  decide

end Toy.Prov
