/-
Toy.RedGreen.Minimal
====================

Card `early-cutoff-skips-cached-query-with-unchanged-dependencies`.  With early
cutoff (any replay order), a query holding a cached entry all of whose
recorded dependencies have, in the new state, values with the recorded
fingerprints is never executed during the revision — not even partially (an
execution that panics or runs out of fuel counts as executed): it never
appears in the execution log `execLog`, and its slot stays `old e` or becomes
`done e false`.

Without early cutoff this fails, and even with early cutoff a cached query
whose own value is unchanged is executed when one of its recorded dependencies
changed (proved).  The property is about changed recorded dependencies, not
changed values.
-/
import Toy.RedGreen.Basic
import Toy.RedGreen.Lemmas
import Toy.RedGreen.Examples
import Toy.RedGreen.DefExamples
import Toy.RedGreen.ExecLog
import Toy.RedGreen.ValueSound

namespace Toy.RedGreen

/-! ### Lemmas for the main statement

`GoodLDB q e s` says that the instrumented state `s` (working database and
execution log) satisfies `Inv`, that `q`'s slot is `old e` or `done e false`,
and that `q` is not in the log.  Every instrumented step preserves it when
`e`'s recorded dependencies are unchanged in the new state. -/

section NoExec

variable {Q I V F : Type} [DecidableEq Q] [DecidableEq F]

private def GoodLDB (rules : Rules Q I V) (fp : V → F) (oldInp newInp : I → V)
    (q : Q) (e : Entry Q I V F) (s : LDB Q I V F) : Prop :=
  Inv rules fp oldInp newInp s.1 ∧ (s.1 q = .old e ∨ s.1 q = .done e false) ∧ q ∉ s.2

omit [DecidableEq Q] [DecidableEq F] in
private theorem runSt_goodLDB (rules : Rules Q I V) (fp : V → F) (oldInp newInp : I → V)
    (q : Q) (e : Entry Q I V F)
    (g : LDB Q I V F → Key Q I → Out V × LDB Q I V F)
    (hg : ∀ s k, GoodLDB rules fp oldInp newInp q e s →
      GoodLDB rules fp oldInp newInp q e (g s k).2) :
    ∀ (p : Prog (Key Q I) V) (s : LDB Q I V F),
      GoodLDB rules fp oldInp newInp q e s →
      GoodLDB rules fp oldInp newInp q e (p.runSt fp g s).2.2
  | .ret _, _, hs => hs
  | .panic, _, hs => hs
  | .fetch k c, s, hs => by
    simp only [Prog.runSt]
    have hs₁ := hg s k hs
    cases hgk : g s k with
    | mk o s₁ =>
      rw [hgk] at hs₁
      cases o with
      | panic => exact hs₁
      | stuck => exact hs₁
      | val v => exact runSt_goodLDB rules fp oldInp newInp q e g hg (c v) s₁ hs₁

omit [DecidableEq Q] in
private theorem checkDepsX_goodLDB (cutoff stopAtRed : Bool)
    (rules : Rules Q I V) (fp : V → F) (oldInp newInp : I → V)
    (q : Q) (e : Entry Q I V F)
    (g : LDB Q I V F → Key Q I → Out V × LDB Q I V F)
    (hg : ∀ s k, GoodLDB rules fp oldInp newInp q e s →
      GoodLDB rules fp oldInp newInp q e (g s k).2) :
    ∀ (deps : List (Key Q I × F)) (s : LDB Q I V F) (anyRed : Bool),
      GoodLDB rules fp oldInp newInp q e s →
      GoodLDB rules fp oldInp newInp q e (checkDepsX cutoff stopAtRed fp g s deps anyRed).2
  | [], _, _, hs => hs
  | (d, fd) :: rest, s, anyRed, hs => by
    simp only [checkDepsX]
    have hs₁ := hg s d hs
    cases hgd : g s d with
    | mk o s₁ =>
      rw [hgd] at hs₁
      cases o with
      | panic => exact hs₁
      | stuck => exact hs₁
      | val v =>
        simp only
        split
        · split
          · exact hs₁
          · exact checkDepsX_goodLDB cutoff stopAtRed rules fp oldInp newInp q e g hg rest s₁ true hs₁
        · exact checkDepsX_goodLDB cutoff stopAtRed rules fp oldInp newInp q e g hg rest s₁ anyRed hs₁

omit [DecidableEq Q] in
private theorem checkDeps_cutoff_never_red (stopAtRed : Bool)
    (rules : Rules Q I V) (fp : V → F) (oldInp newInp : I → V)
    (f : DB Q I V F → Key Q I → Out V × DB Q I V F)
    (hf_inv : ∀ db k, Inv rules fp oldInp newInp db → Inv rules fp oldInp newInp (f db k).2)
    (hf_val : ∀ db k v, Inv rules fp oldInp newInp db → (f db k).1 = .val v →
      ∃ m, eval rules newInp m k = .val v) :
    ∀ (deps : List (Key Q I × F)) (db : DB Q I V F),
      Inv rules fp oldInp newInp db →
      (∀ d fd, (d, fd) ∈ deps → ∃ n v, eval rules newInp n d = .val v ∧ fp v = fd) →
      (checkDeps true stopAtRed fp f db deps false).1 ≠ .red
  | [], _, _, _ => by simp [checkDeps]
  | (d, fd) :: rest, db, hinv, hunch => by
    simp only [checkDeps]
    have hinv₁ := hf_inv db d hinv
    cases hfd : f db d with
    | mk o db₁ =>
      rw [hfd] at hinv₁
      cases o with
      | panic => intro h; cases h
      | stuck => intro h; cases h
      | val v' =>
        obtain ⟨m', hm'⟩ := hf_val db d v' hinv (by rw [hfd])
        obtain ⟨n₀, v, hv, hfpv⟩ := hunch d fd (by simp)
        have heq := eval_eq_of_ne_stuck rules newInp d
          (by rw [hm']; intro hc; cases hc) (by rw [hv]; intro hc; cases hc)
        rw [hm', hv] at heq
        cases heq
        have hchg : changedAt true fp db₁ d v' fd = false := by simp [changedAt, hfpv]
        simp only [hchg, Bool.false_eq_true, ↓reduceIte]
        exact checkDeps_cutoff_never_red stopAtRed rules fp oldInp newInp f hf_inv hf_val
          rest db₁ hinv₁ (fun d' fd' hm => hunch d' fd' (by simp [hm]))

private theorem fetch_cutoff_noExec_and_slot (r : Replay)
    (rules : Rules Q I V) (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V)
    (q : Q) (e : Entry Q I V F)
    (hunch : ∀ d f, (d, f) ∈ e.deps → ∃ n v, eval rules newInp n d = .val v ∧ fp v = f) :
    ∀ (m : Nat) (db : DB Q I V F) (k : Key Q I),
      Inv rules fp oldInp newInp db →
      (db q = .old e ∨ db q = .done e false) →
      q ∉ execLog ⟨r, true⟩ rules fp newInp m db k ∧
      ((fetch ⟨r, true⟩ rules fp newInp m db k).2 q = .old e ∨
       (fetch ⟨r, true⟩ rules fp newInp m db k).2 q = .done e false)
  | 0, _, _, _, hq => ⟨by simp [execLog, fetchX], hq⟩
  | _ + 1, _, .inr _, _, hq => ⟨by simp [execLog, fetchX], hq⟩
  | n + 1, db, .inl q', hinv, hq => by
    have hf_inv : ∀ s k, Inv rules fp oldInp newInp s →
        Inv rules fp oldInp newInp (fetch ⟨r, true⟩ rules fp newInp n s k).2 :=
      fun s k hs => (fetch_inv_and_value_sound ⟨r, true⟩ rules fp hfp oldInp newInp n s k hs).1
    have hf_val : ∀ s k v, Inv rules fp oldInp newInp s →
        (fetch ⟨r, true⟩ rules fp newInp n s k).1 = .val v → ∃ m, eval rules newInp m k = .val v :=
      fun s k v hs hv => (fetch_inv_and_value_sound ⟨r, true⟩ rules fp hfp oldInp newInp n s k hs).2 v hv
    have hg_good : ∀ (s : LDB Q I V F) (k : Key Q I),
        GoodLDB rules fp oldInp newInp q e s →
        GoodLDB rules fp oldInp newInp q e (fetchX ⟨r, true⟩ rules fp newInp n s k).2 := by
      intro ⟨s_db, s_log⟩ k ⟨hs_inv, hs_q, hs_nmem⟩
      rw [fetchX_eq ⟨r, true⟩ rules fp newInp n s_db s_log k]
      have hih := fetch_cutoff_noExec_and_slot r rules fp hfp oldInp newInp q e hunch n s_db k
        hs_inv hs_q
      refine ⟨hf_inv s_db k hs_inv, hih.2, ?_⟩
      simp only [List.mem_append, not_or]
      exact ⟨hs_nmem, hih.1⟩
    have hexec_ne : ∀ (s : LDB Q I V F),
        q' ≠ q → GoodLDB rules fp oldInp newInp q e s →
        q ∉ (execX rules fp (fetchX ⟨r, true⟩ rules fp newInp n) s q').2.2 ∧
        ((execX rules fp (fetchX ⟨r, true⟩ rules fp newInp n) s q').2.1 q = .old e ∨
         (execX rules fp (fetchX ⟨r, true⟩ rules fp newInp n) s q').2.1 q = .done e false) := by
      intro ⟨s_db, s_log⟩ hne ⟨hs_inv, hs_q, hs_nmem⟩
      have hstart : GoodLDB rules fp oldInp newInp q e (s_db, s_log ++ [q']) := by
        refine ⟨hs_inv, hs_q, ?_⟩
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨hs_nmem, Ne.symm hne⟩
      have hrun := runSt_goodLDB rules fp oldInp newInp q e _ hg_good (rules q')
        (s_db, s_log ++ [q']) hstart
      unfold execX
      cases hr : (rules q').runSt fp (fetchX ⟨r, true⟩ rules fp newInp n) (s_db, s_log ++ [q']) with
      | mk o rest =>
        cases rest with
        | mk tr s₁ =>
          rw [hr] at hrun
          cases o with
          | panic => exact ⟨hrun.2.2, hrun.2.1⟩
          | stuck => exact ⟨hrun.2.2, hrun.2.1⟩
          | val v =>
            refine ⟨hrun.2.2, ?_⟩
            simp only [DB.set, Ne.symm hne, ite_false]
            exact hrun.2.1
    have hfx_db : (fetch ⟨r, true⟩ rules fp newInp (n + 1) db (.inl q')).2 =
        (fetchX ⟨r, true⟩ rules fp newInp (n + 1) (db, []) (.inl q')).2.1 := by
      rw [fetchX_eq]
    rw [hfx_db]
    unfold execLog
    have hinit : GoodLDB rules fp oldInp newInp q e (db, []) :=
      ⟨hinv, hq, by simp⟩
    simp only [fetchX]
    cases hq' : db q' with
    | done e' b' => exact ⟨by simp, hq⟩
    | none =>
      have hne : q' ≠ q := by
        intro heq; subst heq; rw [hq'] at hq; rcases hq with h | h <;> cases h
      exact hexec_ne (db, []) hne hinit
    | old e' =>
      simp only
      have hmg_good : GoodLDB rules fp oldInp newInp q e
          (markGreenX ⟨r, true⟩ fp (fetchX ⟨r, true⟩ rules fp newInp n) (db, []) e'.deps).2 := by
        unfold markGreenX
        cases r with
        | ordered => exact checkDepsX_goodLDB true true rules fp oldInp newInp q e _ hg_good e'.deps (db, []) false hinit
        | reversed => exact checkDepsX_goodLDB true true rules fp oldInp newInp q e _ hg_good e'.deps.reverse (db, []) false hinit
        | exhaustive => exact checkDepsX_goodLDB true false rules fp oldInp newInp q e _ hg_good e'.deps (db, []) false hinit
      obtain ⟨L₁, hmg_tr⟩ := markGreen_tracks ⟨r, true⟩ fp (fetchX ⟨r, true⟩ rules fp newInp n)
        (fetch ⟨r, true⟩ rules fp newInp n) (fetchX_tracks ⟨r, true⟩ rules fp newInp n) db e'.deps
      have hmg_fst : (markGreenX ⟨r, true⟩ fp (fetchX ⟨r, true⟩ rules fp newInp n) (db, []) e'.deps).1 =
          (markGreen ⟨r, true⟩ fp (fetch ⟨r, true⟩ rules fp newInp n) db e'.deps).1 := by
        rw [hmg_tr []]
      cases hmX : markGreenX ⟨r, true⟩ fp (fetchX ⟨r, true⟩ rules fp newInp n) (db, []) e'.deps with
      | mk verdict s₁ =>
        rw [hmX] at hmg_good hmg_fst
        cases verdict with
        | panic => exact ⟨hmg_good.2.2, hmg_good.2.1⟩
        | stuck => exact ⟨hmg_good.2.2, hmg_good.2.1⟩
        | green =>
          refine ⟨hmg_good.2.2, ?_⟩
          simp only
          by_cases heq : q' = q
          · subst heq
            have he' : e' = e := by
              rw [hq'] at hq; rcases hq with h | h
              · cases h; rfl
              · cases h
            subst he'
            right; simp [DB.set]
          · simp only [DB.set, Ne.symm heq, ite_false]
            exact hmg_good.2.1
        | red =>
          have hne : q' ≠ q := by
            intro heq; subst heq
            have he' : e' = e := by
              rw [hq'] at hq; rcases hq with h | h
              · cases h; rfl
              · cases h
            subst he'
            have hnotred : (markGreen ⟨r, true⟩ fp (fetch ⟨r, true⟩ rules fp newInp n) db e'.deps).1 ≠ .red := by
              unfold markGreen
              cases r with
              | ordered => exact checkDeps_cutoff_never_red true rules fp oldInp newInp _ hf_inv hf_val e'.deps db hinv hunch
              | reversed =>
                exact checkDeps_cutoff_never_red true rules fp oldInp newInp _ hf_inv hf_val e'.deps.reverse db hinv
                  (fun d fd hm => hunch d fd (List.mem_reverse.mp hm))
              | exhaustive => exact checkDeps_cutoff_never_red false rules fp oldInp newInp _ hf_inv hf_val e'.deps db hinv hunch
            exact hnotred hmg_fst.symm
          exact hexec_ne s₁ hne hmg_good

end NoExec

/-- **Early cutoff never executes a cached query whose recorded dependencies
are unchanged.**  For any replay order with early cutoff, collision-free
fingerprints, and a working database `db₀` satisfying `Inv`: if query `q`
holds the cached entry `e` (`db₀ q = old e`) and every recorded dependency of
`e` has, in the new state, a from-scratch value whose fingerprint is the
recorded one, then for every working database `db` reachable from `db₀` by
incremental fetches, the slot of `q` in `db` is still `old e` or has been
marked green as `done e false`, and no fetch from `db` executes `q`. -/
theorem early_cutoff_never_executes_cached_query_with_unchanged_recorded_deps
    {Q I V F : Type} [DecidableEq Q] [DecidableEq F]
    (r : Replay) (rules : Rules Q I V) (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V)
    (db₀ : DB Q I V F) (hinv : Inv rules fp oldInp newInp db₀)
    (q : Q) (e : Entry Q I V F) (hq : db₀ q = .old e)
    (hunch : ∀ d f, (d, f) ∈ e.deps → ∃ n v, eval rules newInp n d = .val v ∧ fp v = f)
    (db : DB Q I V F) (hreach : Reachable ⟨r, true⟩ rules fp newInp db₀ db)
    (m : Nat) (k : Key Q I) :
    q ∉ execLog ⟨r, true⟩ rules fp newInp m db k ∧ (db q = .old e ∨ db q = .done e false) := by
  have hreach_slot : Inv rules fp oldInp newInp db ∧ (db q = .old e ∨ db q = .done e false) := by
    induction hreach with
    | refl => exact ⟨hinv, Or.inl hq⟩
    | step n₀ k₀ _ ih =>
      exact ⟨(fetch_inv_and_value_sound ⟨r, true⟩ rules fp hfp oldInp newInp n₀ _ k₀ ih.1).1,
        (fetch_cutoff_noExec_and_slot r rules fp hfp oldInp newInp q e hunch n₀ _ k₀ ih.1 ih.2).2⟩
  exact ⟨(fetch_cutoff_noExec_and_slot r rules fp hfp oldInp newInp q e hunch m db k
    hreach_slot.1 hreach_slot.2).1, hreach_slot.2⟩

/-! ## Example K: early cutoff in action -/

/-- The recorded entry of `top` in example K. -/
def eK : Entry Q3 IK Nat Nat := ⟨[(.inl .a, 0), (.inr .y, 2)], 2⟩

/-- The recorded entry of `a` in example K. -/
def eKa : Entry Q3 IK Nat Nat := ⟨[(.inr .x, 1)], 0⟩

theorem start_odbK_top : start odbK .top = .old eK := by decide
theorem start_odbK_a : start odbK .a = .old eKa := by decide

theorem eK_deps_unchanged :
    ∀ d f, (d, f) ∈ eK.deps → ∃ n v, eval rulesK newK n d = .val v ∧ fpId v = f := by
  intro d f h
  simp only [eK, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨3, 0, by decide, rfl⟩
  · exact ⟨1, 2, by decide, rfl⟩

theorem eKa_deps_changed :
    ¬ ∀ d f, (d, f) ∈ eKa.deps → ∃ n v, eval rulesK newK n d = .val v ∧ fpId v = f := by
  intro h
  obtain ⟨n, v, hv, hfp⟩ := h (.inr .x) 1 (by simp [eKa])
  cases n with
  | zero => cases hv
  | succ n' =>
    simp [eval, newK, inpXY] at hv
    subst hv
    simp [fpId] at hfp

theorem inv_K : Inv rulesK fpId oldK newK (start odbK) :=
  inv_start rulesK fpId oldK newK odbK (recordAll_consistent rulesK fpId oldK 10)

/-- **Non-vacuity, and the property in action.**  Example K satisfies every
hypothesis of
`early_cutoff_never_executes_cached_query_with_unchanged_recorded_deps` for
`q = top`, for every replay order: `x` changes, `a` is executed and reproduces
`0`, `y` is unchanged.  Fetching `top` executes only `a` and marks `top`
green. -/
theorem early_cutoff_skips_nonvacuous (r : Replay) :
    FpInjective fpId ∧ Inv rulesK fpId oldK newK (start odbK) ∧ start odbK .top = .old eK ∧
    (∀ d f, (d, f) ∈ eK.deps → ∃ n v, eval rulesK newK n d = .val v ∧ fpId v = f) ∧
    Reachable ⟨r, true⟩ rulesK fpId newK (start odbK)
      (fetch ⟨r, true⟩ rulesK fpId newK 6 (start odbK) (.inl .top)).2 ∧
    execLog ⟨r, true⟩ rulesK fpId newK 6 (start odbK) (.inl .top) = [.a] ∧
    (fetch ⟨r, true⟩ rulesK fpId newK 6 (start odbK) (.inl .top)).2 .top = .done eK false := by
  refine ⟨fpId_injective, inv_K, start_odbK_top, eK_deps_unchanged, .step 6 (.inl Q3.top) .refl,
    ?_, ?_⟩ <;> cases r <;> decide

/-! ## Each hypothesis is needed -/

/-- **Early cutoff is needed.**  Example K with early cutoff off (ordered
replay): every other hypothesis holds for `q = top`, and fetching `top`
executes it (its slot becomes `done … true`), because its dependency `a` was
re-executed, although `a` reproduced its recorded fingerprint. -/
theorem no_cutoff_reexecutes_query_with_unchanged_recorded_dependencies :
    FpInjective fpId ∧ Inv rulesK fpId oldK newK (start odbK) ∧ start odbK .top = .old eK ∧
    (∀ d f, (d, f) ∈ eK.deps → ∃ n v, eval rulesK newK n d = .val v ∧ fpId v = f) ∧
    Reachable ⟨.ordered, false⟩ rulesK fpId newK (start odbK) (start odbK) ∧
    .top ∈ execLog ⟨.ordered, false⟩ rulesK fpId newK 6 (start odbK) (.inl .top) ∧
    (fetch ⟨.ordered, false⟩ rulesK fpId newK 6 (start odbK) (.inl .top)).2 .top = .done eK true :=
  ⟨fpId_injective, inv_K, start_odbK_top, eK_deps_unchanged, .refl, by decide, by decide⟩

/-- **Unchanged recorded dependencies are needed — and an unchanged value is
not enough.**  In example K, take `q = a` with its entry `eKa`: every other
hypothesis holds, `a`'s recorded dependency `x` changed (`1 → 3`), and fetching
`top` executes `a`, although `a`'s value (`0`) is the same in both states.
Early cutoff stops propagation at `a`'s dependents, not at `a`. -/
theorem early_cutoff_reexecutes_query_whose_value_is_unchanged :
    FpInjective fpId ∧ Inv rulesK fpId oldK newK (start odbK) ∧ start odbK .a = .old eKa ∧
    ¬ (∀ d f, (d, f) ∈ eKa.deps → ∃ n v, eval rulesK newK n d = .val v ∧ fpId v = f) ∧
    Reachable ⟨.ordered, true⟩ rulesK fpId newK (start odbK) (start odbK) ∧
    eval rulesK newK 2 (.inl .a) = .val eKa.value ∧
    .a ∈ execLog ⟨.ordered, true⟩ rulesK fpId newK 6 (start odbK) (.inl .top) ∧
    (fetch ⟨.ordered, true⟩ rulesK fpId newK 6 (start odbK) (.inl .top)).2 .a =
      .done ⟨[(.inr .x, 3)], 0⟩ true :=
  ⟨fpId_injective, inv_K, start_odbK_a, eKa_deps_changed, .refl, by decide, by decide, by decide⟩

/-- A working database violating `Inv`: `a` holds a `done` slot with a wrong
value `5`. -/
def staleDbK : DB Q3 IK Nat Nat :=
  fun q => if q = .a then .done ⟨[(.inr .x, 3)], 5⟩ true else start odbK q

theorem staleDbK_not_inv : ¬ Inv rulesK fpId oldK newK staleDbK := by
  intro h
  have hgood : EntryConsistent rulesK fpId newK .a ⟨[(.inr .x, 3)], 0⟩ := ⟨2, by decide⟩
  exact absurd (entryConsistent_unique rulesK fpId newK .a (h .a) hgood) (by decide)

/-- **`Inv` is needed.**  Take `db₀ = db = staleDbK`: every other hypothesis
holds for `q = top` (its recorded dependencies `a ↦ 0`, `y ↦ 2` are unchanged
in the new state), yet fetching `top` executes it, because the stale slot makes
`a` look changed. -/
theorem stale_db_reexecutes_query_with_unchanged_recorded_dependencies :
    FpInjective fpId ∧ ¬ Inv rulesK fpId oldK newK staleDbK ∧ staleDbK .top = .old eK ∧
    (∀ d f, (d, f) ∈ eK.deps → ∃ n v, eval rulesK newK n d = .val v ∧ fpId v = f) ∧
    Reachable ⟨.ordered, true⟩ rulesK fpId newK staleDbK staleDbK ∧
    .top ∈ execLog ⟨.ordered, true⟩ rulesK fpId newK 6 staleDbK (.inl .top) ∧
    (fetch ⟨.ordered, true⟩ rulesK fpId newK 6 staleDbK (.inl .top)).2 .top ≠ .old eK ∧
    (fetch ⟨.ordered, true⟩ rulesK fpId newK 6 staleDbK (.inl .top)).2 .top ≠ .done eK false :=
  ⟨fpId_injective, staleDbK_not_inv, by decide, eK_deps_unchanged, .refl, by decide, by decide,
    by decide⟩

/-- **Reachability is needed.**  Take `db₀ = start odbK` (which satisfies
`Inv`) and `db = staleDbK`, which is not reachable from it (every reachable
database satisfies `Inv`).  The slot of `top` in `staleDbK` is still `old eK`,
but fetching `top` from `staleDbK` executes it. -/
theorem unreachable_db_reexecutes_query_with_unchanged_recorded_dependencies :
    FpInjective fpId ∧ Inv rulesK fpId oldK newK (start odbK) ∧ start odbK .top = .old eK ∧
    (∀ d f, (d, f) ∈ eK.deps → ∃ n v, eval rulesK newK n d = .val v ∧ fpId v = f) ∧
    ¬ Reachable ⟨.ordered, true⟩ rulesK fpId newK (start odbK) staleDbK ∧
    .top ∈ execLog ⟨.ordered, true⟩ rulesK fpId newK 6 staleDbK (.inl .top) :=
  ⟨fpId_injective, inv_K, start_odbK_top, eK_deps_unchanged,
    fun h => staleDbK_not_inv (inv_of_reachable ⟨.ordered, true⟩ rulesK fpId fpId_injective
      oldK newK _ _ inv_K h),
    by decide⟩

/-- `odbKnoTop` is consistent with the old state of example K. -/
theorem odbKnoTop_consistent : DBConsistent rulesK fpId oldK odbKnoTop := by
  intro q e h
  cases q with
  | top => cases h
  | a => exact recordAll_consistent rulesK fpId oldK 10 .a e h
  | b => exact recordAll_consistent rulesK fpId oldK 10 .b e h

/-- **A cached entry is needed (`db₀ q = old e`).**  In example K′ (example K
without a cached entry for `top`), `top`'s slot is `none`; with `e = eK` every
other hypothesis holds, and fetching `top` executes it (first execution in this
revision). -/
theorem uncached_query_with_unchanged_recorded_dependencies_executes :
    FpInjective fpId ∧ Inv rulesK fpId oldK newK (start odbKnoTop) ∧
    start odbKnoTop .top = .none ∧
    (∀ d f, (d, f) ∈ eK.deps → ∃ n v, eval rulesK newK n d = .val v ∧ fpId v = f) ∧
    Reachable ⟨.ordered, true⟩ rulesK fpId newK (start odbKnoTop) (start odbKnoTop) ∧
    .top ∈ execLog ⟨.ordered, true⟩ rulesK fpId newK 6 (start odbKnoTop) (.inl .top) :=
  ⟨fpId_injective, inv_start rulesK fpId oldK newK odbKnoTop odbKnoTop_consistent, by decide,
    eK_deps_unchanged, .refl, by decide⟩

/-! ## Example F: collision-freedom is needed -/

theorem fpCollide13_not_injective : ¬ FpInjective fpCollide13 :=
  fun h => absurd (h 1 3 rfl) (by decide)

/-- The recorded entry of `top` in example F. -/
def eF : Entry Q3 IK Nat Nat := ⟨[(.inl .b, 30)], 30⟩

/-- **Collision-freedom is needed.**  Example F: `fpCollide13` collides on `1`
and `3`.  Every other hypothesis holds for `q = top` (its recorded dependency
`b ↦ 30` is unchanged in the new state), yet fetching `top` executes it: the
collision makes `a` look unchanged, so `a` is marked green with the stale `1`;
`b` is re-executed because `y` changed and computes `10` from the stale `a`;
`10` differs from the recorded `30`, so `top` is executed. -/
theorem fp_collision_reexecutes_query_with_unchanged_recorded_dependencies :
    ¬ FpInjective fpCollide13 ∧ Inv rulesF fpCollide13 oldF newF (start odbF) ∧
    start odbF .top = .old eF ∧
    (∀ d f, (d, f) ∈ eF.deps → ∃ n v, eval rulesF newF n d = .val v ∧ fpCollide13 v = f) ∧
    Reachable ⟨.ordered, true⟩ rulesF fpCollide13 newF (start odbF) (start odbF) ∧
    .top ∈ execLog ⟨.ordered, true⟩ rulesF fpCollide13 newF 8 (start odbF) (.inl .top) := by
  refine ⟨fpCollide13_not_injective,
    inv_start rulesF fpCollide13 oldF newF odbF (recordAll_consistent rulesF fpCollide13 oldF 10),
    by decide, ?_, .refl, by decide⟩
  intro d f h
  simp only [eF, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  rcases h with ⟨rfl, rfl⟩
  exact ⟨4, 30, by decide, rfl⟩

end Toy.RedGreen
