/-
Toy.RedGreen.ValueSound
=======================

Value soundness for every replay order.  For any configuration (recorded,
reversed or all-edges replay; early cutoff on or off) and collision-free
fingerprints, one incremental fetch from a working database satisfying the
simulation invariant `Inv`

* returns a database that again satisfies `Inv`, and
* if it returns a value, returns the from-scratch value of the new state.

Marking a query green requires every recorded dependency to reproduce its
recorded fingerprint, whatever order the dependencies are checked in; with an
injective fingerprint function the query's code then follows its recorded
path in the new state, so the reused entry is consistent with the new state.
Replay order matters only for panics and termination (card
`ordered-replay-necessary`).

Card `every-replay-order-is-value-sound`.  All fully proved.
-/
import Toy.RedGreen.Basic
import Toy.RedGreen.Lemmas

namespace Toy.RedGreen

section ValueSound

variable {Q I V F : Type}

/-- If a program's run against `f` succeeds with trace `deps`, and `g` returns,
for every recorded key, a value with the recorded fingerprint, then (with an
injective fingerprint function) the run against `g` succeeds with the same
value and trace. -/
theorem Prog.runT_of_trace_match {K V F : Type} (f g : K → Out V) (fp : V → F)
    (hfp : FpInjective fp) :
    ∀ (p : Prog K V) (v : V) (deps : List (K × F)),
      p.runT f fp = (.val v, deps) →
      (∀ d fd, (d, fd) ∈ deps → ∃ v', g d = .val v' ∧ fp v' = fd) →
      p.runT g fp = (.val v, deps)
  | .ret _, _, _, hrun, _ => by
    simp only [Prog.runT, Prod.mk.injEq, Out.val.injEq] at hrun ⊢
    exact hrun
  | .panic, _, _, hrun, _ => by
    simp only [Prog.runT, Prod.mk.injEq] at hrun
    cases hrun.1
  | .fetch k c, v, deps, hrun, hdeps => by
    simp only [Prog.runT] at hrun ⊢
    cases hfk : f k with
    | panic => rw [hfk] at hrun; simp at hrun
    | stuck => rw [hfk] at hrun; simp at hrun
    | val v₀ =>
      rw [hfk] at hrun
      simp only at hrun
      cases hcr : (c v₀).runT f fp with
      | mk o tr =>
        rw [hcr] at hrun
        simp only [Prod.mk.injEq] at hrun
        obtain ⟨ho, hdeps_eq⟩ := hrun
        subst ho
        subst hdeps_eq
        obtain ⟨v', hgk, hfpv⟩ := hdeps k (fp v₀) (by simp)
        have hveq : v' = v₀ := hfp v' v₀ hfpv
        subst hveq
        rw [hgk]
        simp only
        rw [Prog.runT_of_trace_match f g fp hfp (c v') v tr hcr
          (fun d fd hd => hdeps d fd (by simp [hd]))]

/-- Finitely many keys with finished from-scratch values have a common fuel. -/
theorem eval_common_fuel (rules : Rules Q I V) (fp : V → F) (inp : I → V) :
    ∀ (deps : List (Key Q I × F)),
      (∀ d fd, (d, fd) ∈ deps → ∃ n v, eval rules inp n d = .val v ∧ fp v = fd) →
      ∃ N, ∀ d fd, (d, fd) ∈ deps → ∃ v, eval rules inp N d = .val v ∧ fp v = fd
  | [], _ => ⟨0, fun _ _ h => by cases h⟩
  | (d₀, fd₀) :: rest, h => by
    obtain ⟨n₀, v₀, hv₀, hfp₀⟩ := h d₀ fd₀ (by simp)
    obtain ⟨N₁, hN₁⟩ := eval_common_fuel rules fp inp rest (fun d fd hd => h d fd (by simp [hd]))
    refine ⟨max n₀ N₁, fun d fd hd => ?_⟩
    simp only [List.mem_cons, Prod.mk.injEq] at hd
    rcases hd with ⟨rfl, rfl⟩ | hrest
    · refine ⟨v₀, ?_, hfp₀⟩
      rw [eval_mono rules inp n₀ (max n₀ N₁) d (Nat.le_max_left _ _) (by rw [hv₀]; intro hc; cases hc)]
      exact hv₀
    · obtain ⟨v, hv, hfpv⟩ := hN₁ d fd hrest
      refine ⟨v, ?_, hfpv⟩
      rw [eval_mono rules inp N₁ (max n₀ N₁) d (Nat.le_max_right _ _) (by rw [hv]; intro hc; cases hc)]
      exact hv

/-- An entry consistent with the old state whose recorded dependencies all have
new-state values with the recorded fingerprints is consistent with the new
state. -/
theorem entryConsistent_of_deps_match (rules : Rules Q I V) (fp : V → F)
    (hfp : FpInjective fp) (oldInp newInp : I → V) (q : Q) (e : Entry Q I V F)
    (hold : EntryConsistent rules fp oldInp q e)
    (hdeps : ∀ d fd, (d, fd) ∈ e.deps → ∃ n v, eval rules newInp n d = .val v ∧ fp v = fd) :
    EntryConsistent rules fp newInp q e := by
  obtain ⟨n₀, hn₀⟩ := hold
  obtain ⟨N, hN⟩ := eval_common_fuel rules fp newInp e.deps hdeps
  exact ⟨N, Prog.runT_of_trace_match (eval rules oldInp n₀) (eval rules newInp N) fp hfp (rules q)
    e.value e.deps hn₀ hN⟩

theorem runSt_value_sound (rules : Rules Q I V) (fp : V → F) (oldInp newInp : I → V)
    (f : DB Q I V F → Key Q I → Out V × DB Q I V F)
    (hf_inv : ∀ db k, Inv rules fp oldInp newInp db → Inv rules fp oldInp newInp (f db k).2)
    (hf_val : ∀ db k v, Inv rules fp oldInp newInp db → (f db k).1 = .val v →
      ∃ m, eval rules newInp m k = .val v) :
    ∀ (p : Prog (Key Q I) V) (db : DB Q I V F), Inv rules fp oldInp newInp db →
      Inv rules fp oldInp newInp (p.runSt fp f db).2.2 ∧
      (∀ v tr, (p.runSt fp f db).1 = .val v → (p.runSt fp f db).2.1 = tr →
        ∃ M, p.runT (eval rules newInp M) fp = (.val v, tr))
  | .ret w, db, hinv => by
    refine ⟨hinv, fun v tr hv htr => ?_⟩
    simp only [Prog.runSt] at hv htr
    cases hv; subst htr
    exact ⟨0, rfl⟩
  | .panic, db, hinv => by
    refine ⟨hinv, fun v tr hv _ => ?_⟩
    simp only [Prog.runSt] at hv; cases hv
  | .fetch k c, db, hinv => by
    simp only [Prog.runSt]
    have hinv₁ := hf_inv db k hinv
    have hval₁ := hf_val db k
    cases hfk : f db k with
    | mk o db₁ =>
      rw [hfk] at hinv₁
      cases o with
      | panic => exact ⟨hinv₁, fun _ _ hv _ => by cases hv⟩
      | stuck => exact ⟨hinv₁, fun _ _ hv _ => by cases hv⟩
      | val v₀ =>
        obtain ⟨m₀, hm₀⟩ := hval₁ v₀ hinv (by rw [hfk])
        simp only
        have hrec := runSt_value_sound rules fp oldInp newInp f hf_inv hf_val (c v₀) db₁ hinv₁
        cases hcr : (c v₀).runSt fp f db₁ with
        | mk o' rest =>
          cases rest with
          | mk tr' db₂ =>
            rw [hcr] at hrec
            refine ⟨hrec.1, fun v tr hv htr => ?_⟩
            obtain ⟨M', hM'⟩ := hrec.2 v tr' hv rfl
            refine ⟨max m₀ M', ?_⟩
            simp only [Prog.runT]
            have hm₀' : eval rules newInp (max m₀ M') k = .val v₀ := by
              rw [eval_mono rules newInp m₀ (max m₀ M') k (Nat.le_max_left _ _)
                (by rw [hm₀]; intro hc; cases hc)]
              exact hm₀
            rw [hm₀']
            simp only
            have hM'' : (c v₀).runT (eval rules newInp (max m₀ M')) fp = (.val v, tr') := by
              rw [Prog.runT_congr_of_ne_stuck (eval rules newInp M')
                (eval rules newInp (max m₀ M')) fp
                (fun k' hk' => eval_mono rules newInp M' (max m₀ M') k' (Nat.le_max_right _ _) hk')
                (c v₀) (by rw [hM']; intro hc; cases hc)]
              exact hM'
            rw [hM'']
            simp only [htr]

theorem checkDeps_value_sound [DecidableEq F] (cutoff stopAtRed : Bool) (rules : Rules Q I V)
    (fp : V → F) (oldInp newInp : I → V) (f : DB Q I V F → Key Q I → Out V × DB Q I V F)
    (hf_inv : ∀ db k, Inv rules fp oldInp newInp db → Inv rules fp oldInp newInp (f db k).2)
    (hf_val : ∀ db k v, Inv rules fp oldInp newInp db → (f db k).1 = .val v →
      ∃ m, eval rules newInp m k = .val v) :
    ∀ (deps : List (Key Q I × F)) (db : DB Q I V F) (anyRed : Bool),
      Inv rules fp oldInp newInp db →
      Inv rules fp oldInp newInp (checkDeps cutoff stopAtRed fp f db deps anyRed).2 ∧
      ((checkDeps cutoff stopAtRed fp f db deps anyRed).1 = .green →
        anyRed = false ∧
        ∀ d fd, (d, fd) ∈ deps → ∃ m v, eval rules newInp m d = .val v ∧ fp v = fd)
  | [], db, anyRed, hinv => by
    simp only [checkDeps]
    refine ⟨hinv, fun h => ?_⟩
    cases anyRed with
    | true => simp at h
    | false => exact ⟨rfl, fun _ _ hd => by cases hd⟩
  | (d, fd) :: rest, db, anyRed, hinv => by
    simp only [checkDeps]
    have hinv₁ := hf_inv db d hinv
    have hval₁ := hf_val db d
    cases hfd : f db d with
    | mk o db₁ =>
      rw [hfd] at hinv₁
      cases o with
      | panic => exact ⟨hinv₁, fun h => by cases h⟩
      | stuck => exact ⟨hinv₁, fun h => by cases h⟩
      | val v =>
        obtain ⟨m, hm⟩ := hval₁ v hinv (by rw [hfd])
        simp only
        by_cases hchg : changedAt cutoff fp db₁ d v fd = true
        · simp only [hchg, ↓reduceIte]
          cases stopAtRed with
          | true => exact ⟨hinv₁, fun h => by cases h⟩
          | false =>
            have hrec := checkDeps_value_sound cutoff false rules fp oldInp newInp f hf_inv hf_val
              rest db₁ true hinv₁
            exact ⟨hrec.1, fun h => by have := (hrec.2 h).1; cases this⟩
        · simp only [hchg, Bool.false_eq_true, ↓reduceIte]
          have hfp_eq : fp v = fd := by
            unfold changedAt at hchg
            by_cases hfeq : fp v = fd
            · exact hfeq
            · simp [hfeq] at hchg
          have hrec := checkDeps_value_sound cutoff stopAtRed rules fp oldInp newInp f hf_inv hf_val
            rest db₁ anyRed hinv₁
          refine ⟨hrec.1, fun h => ?_⟩
          obtain ⟨hary, hrest⟩ := hrec.2 h
          refine ⟨hary, fun d' fd' hmem => ?_⟩
          simp only [List.mem_cons, Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl⟩ | hmem'
          · exact ⟨m, v, hm, hfp_eq⟩
          · exact hrest d' fd' hmem'

theorem exec_value_sound [DecidableEq Q] (rules : Rules Q I V) (fp : V → F) (oldInp newInp : I → V)
    (f : DB Q I V F → Key Q I → Out V × DB Q I V F)
    (hf_inv : ∀ db k, Inv rules fp oldInp newInp db → Inv rules fp oldInp newInp (f db k).2)
    (hf_val : ∀ db k v, Inv rules fp oldInp newInp db → (f db k).1 = .val v →
      ∃ m, eval rules newInp m k = .val v)
    (db : DB Q I V F) (q : Q) (hinv : Inv rules fp oldInp newInp db) :
    Inv rules fp oldInp newInp (exec rules fp f db q).2 ∧
    (∀ v, (exec rules fp f db q).1 = .val v → ∃ m, eval rules newInp m (.inl q) = .val v) := by
  have hrun := runSt_value_sound rules fp oldInp newInp f hf_inv hf_val (rules q) db hinv
  unfold exec
  cases hr : (rules q).runSt fp f db with
  | mk o rest =>
    cases rest with
    | mk tr db₁ =>
      rw [hr] at hrun
      cases o with
      | panic => exact ⟨hrun.1, fun _ h => by cases h⟩
      | stuck => exact ⟨hrun.1, fun _ h => by cases h⟩
      | val v =>
        obtain ⟨M, hM⟩ := hrun.2 v tr rfl rfl
        refine ⟨fun q' => ?_, fun v' hv => ?_⟩
        · unfold DB.set
          by_cases heq : q' = q
          · subst heq; simp only [ite_true]; exact ⟨M, hM⟩
          · simp only [heq, ite_false]; exact hrun.1 q'
        · cases hv
          refine ⟨M + 1, ?_⟩
          simp only [eval, ← Prog.runT_fst (eval rules newInp M) fp, hM]

/-- **One incremental fetch preserves `Inv` and returns only from-scratch
values, for every configuration.**  No replay-order hypothesis. -/
theorem fetch_inv_and_value_sound [DecidableEq Q] [DecidableEq F] (cfg : Config)
    (rules : Rules Q I V) (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V) :
    ∀ (n : Nat) (db : DB Q I V F) (k : Key Q I), Inv rules fp oldInp newInp db →
      Inv rules fp oldInp newInp (fetch cfg rules fp newInp n db k).2 ∧
      (∀ v, (fetch cfg rules fp newInp n db k).1 = .val v → ∃ m, eval rules newInp m k = .val v)
  | 0, db, _, hinv => ⟨hinv, fun _ h => by cases h⟩
  | _ + 1, db, .inr i, hinv => ⟨hinv, fun v h => by cases h; exact ⟨1, rfl⟩⟩
  | n + 1, db, .inl q, hinv => by
    have hf_inv : ∀ s k, Inv rules fp oldInp newInp s →
        Inv rules fp oldInp newInp (fetch cfg rules fp newInp n s k).2 :=
      fun s k hs => (fetch_inv_and_value_sound cfg rules fp hfp oldInp newInp n s k hs).1
    have hf_val : ∀ s k v, Inv rules fp oldInp newInp s →
        (fetch cfg rules fp newInp n s k).1 = .val v → ∃ m, eval rules newInp m k = .val v :=
      fun s k v hs hv => (fetch_inv_and_value_sound cfg rules fp hfp oldInp newInp n s k hs).2 v hv
    simp only [fetch]
    cases hq : db q with
    | done e b =>
      have he : EntryConsistent rules fp newInp q e := by
        have := hinv q; rw [hq] at this; exact this
      obtain ⟨M, hM⟩ := he
      refine ⟨hinv, fun v hv => ?_⟩
      cases hv
      exact ⟨M + 1, by simp only [eval, ← Prog.runT_fst (eval rules newInp M) fp, hM]⟩
    | none =>
      exact exec_value_sound rules fp oldInp newInp _ hf_inv hf_val db q hinv
    | old e =>
      have hold : EntryConsistent rules fp oldInp q e := by
        have := hinv q; rw [hq] at this; exact this
      have hmg : Inv rules fp oldInp newInp
            (markGreen cfg fp (fetch cfg rules fp newInp n) db e.deps).2 ∧
          ((markGreen cfg fp (fetch cfg rules fp newInp n) db e.deps).1 = .green →
            ∀ d fd, (d, fd) ∈ e.deps → ∃ m v, eval rules newInp m d = .val v ∧ fp v = fd) := by
        unfold markGreen
        cases cfg.replay with
        | ordered =>
          have h := checkDeps_value_sound cfg.cutoff true rules fp oldInp newInp _ hf_inv hf_val
            e.deps db false hinv
          exact ⟨h.1, fun hg => (h.2 hg).2⟩
        | reversed =>
          have h := checkDeps_value_sound cfg.cutoff true rules fp oldInp newInp _ hf_inv hf_val
            e.deps.reverse db false hinv
          exact ⟨h.1, fun hg d fd hmem => (h.2 hg).2 d fd (List.mem_reverse.mpr hmem)⟩
        | exhaustive =>
          have h := checkDeps_value_sound cfg.cutoff false rules fp oldInp newInp _ hf_inv hf_val
            e.deps db false hinv
          exact ⟨h.1, fun hg => (h.2 hg).2⟩
      simp only
      cases hm : markGreen cfg fp (fetch cfg rules fp newInp n) db e.deps with
      | mk verdict db₁ =>
        rw [hm] at hmg
        cases verdict with
        | panic => exact ⟨hmg.1, fun _ h => by cases h⟩
        | stuck => exact ⟨hmg.1, fun _ h => by cases h⟩
        | red => exact exec_value_sound rules fp oldInp newInp _ hf_inv hf_val db₁ q hmg.1
        | green =>
          have hnew : EntryConsistent rules fp newInp q e :=
            entryConsistent_of_deps_match rules fp hfp oldInp newInp q e hold (hmg.2 rfl)
          obtain ⟨M, hM⟩ := hnew
          refine ⟨fun q' => ?_, fun v hv => ?_⟩
          · unfold DB.set
            by_cases heq : q' = q
            · subst heq; simp only [ite_true]; exact ⟨M, hM⟩
            · simp only [heq, ite_false]; exact hmg.1 q'
          · cases hv
            exact ⟨M + 1, by simp only [eval, ← Prog.runT_fst (eval rules newInp M) fp, hM]⟩

/-- Every working database reachable by incremental fetches (any
configuration) from a database satisfying `Inv` satisfies `Inv`. -/
theorem inv_of_reachable [DecidableEq Q] [DecidableEq F] (cfg : Config)
    (rules : Rules Q I V) (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V)
    (db₀ db : DB Q I V F) (h₀ : Inv rules fp oldInp newInp db₀)
    (hr : Reachable cfg rules fp newInp db₀ db) : Inv rules fp oldInp newInp db := by
  induction hr with
  | refl => exact h₀
  | step n k _ ih => exact (fetch_inv_and_value_sound cfg rules fp hfp oldInp newInp n _ k ih).1

/-- **Value soundness for every replay order (card
`every-replay-order-is-value-sound`).**  For any configuration — recorded,
reversed or all-edges replay, early cutoff on or off — collision-free
fingerprints, the same query code as the one that produced the database, and
a database consistent with the old input state: every incremental fetch made
during the revision (from the start database or from any database produced
from it by earlier fetches) that returns a value returns a from-scratch value
of the new state. -/
theorem fetch_value_sound_of_any_replay [DecidableEq Q] [DecidableEq F] (cfg : Config)
    (rulesOld rulesNew : Rules Q I V) (hsame : rulesOld = rulesNew)
    (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V) (odb : OldDB Q I V F)
    (hcons : DBConsistent rulesOld fp oldInp odb) (db : DB Q I V F)
    (hreach : Reachable cfg rulesNew fp newInp (start odb) db) (m : Nat) (k : Key Q I) (v : V)
    (hv : (fetch cfg rulesNew fp newInp m db k).1 = .val v) :
    ∃ n, eval rulesNew newInp n k = .val v := by
  subst hsame
  have hinv := inv_of_reachable cfg rulesOld fp hfp oldInp newInp _ db
    (inv_start rulesOld fp oldInp newInp odb hcons) hreach
  exact (fetch_inv_and_value_sound cfg rulesOld fp hfp oldInp newInp m db k hinv).2 v hv

end ValueSound

end Toy.RedGreen
