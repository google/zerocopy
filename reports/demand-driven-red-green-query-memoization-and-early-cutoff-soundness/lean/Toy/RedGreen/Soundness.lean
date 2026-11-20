/-
Toy.RedGreen.Soundness
======================

Cards `incremental-fetch-agrees` (agreement of ordered red-green replay with
from-scratch evaluation) and `early-cutoff-agrees-with-reexecution`.

`fetch_simulation_invariant` is the main simulation invariant, proved by
recursion on the fuel from the one-step value-soundness lemma
`fetch_inv_and_value_sound` and the simulation lemmas below.  The other
results of this module are derived from it.
-/
import Toy.RedGreen.Basic
import Toy.RedGreen.Lemmas
import Toy.RedGreen.Examples
import Toy.RedGreen.ValueSound

namespace Toy.RedGreen

section General

variable {Q I V F : Type} [DecidableEq Q] [DecidableEq F]

/-! ### Simulation lemmas

Each lemma assumes the fetch function used for dependencies (`f`, at fuel
`n`) already satisfies the simulation properties on every `Inv` database:
it preserves `Inv`, returns only from-scratch values and panics of the new
state, and finishes whenever from-scratch evaluation at fuel `n` finishes.
The main theorem below supplies these assumptions by recursion on the fuel. -/

omit [DecidableEq Q] [DecidableEq F] in
private theorem hf_match_of_sim
    (rules : Rules Q I V) (fp : V → F) (oldInp newInp : I → V) (n : Nat)
    (f : DB Q I V F → Key Q I → Out V × DB Q I V F)
    (hf_val : ∀ s k v, Inv rules fp oldInp newInp s → (f s k).1 = .val v →
      ∃ m, eval rules newInp m k = .val v)
    (hf_pan : ∀ s k, Inv rules fp oldInp newInp s → (f s k).1 = .panic →
      ∃ m, eval rules newInp m k = .panic)
    (hf_adeq : ∀ s k, Inv rules fp oldInp newInp s → eval rules newInp n k ≠ .stuck →
      (f s k).1 ≠ .stuck)
    (s : DB Q I V F) (k : Key Q I) (hinv : Inv rules fp oldInp newInp s)
    (hne : eval rules newInp n k ≠ .stuck) :
    (f s k).1 = eval rules newInp n k := by
  have hfn := hf_adeq s k hinv hne
  cases hfk : (f s k).1 with
  | stuck => exact absurd hfk hfn
  | val v =>
    obtain ⟨m, hm⟩ := hf_val s k v hinv hfk
    exact ((eval_eq_of_ne_stuck rules newInp k (by rw [hm]; intro h; cases h) hne).symm.trans hm).symm
  | panic =>
    obtain ⟨m, hm⟩ := hf_pan s k hinv hfk
    exact ((eval_eq_of_ne_stuck rules newInp k (by rw [hm]; intro h; cases h) hne).symm.trans hm).symm

omit [DecidableEq Q] [DecidableEq F] in
private theorem runSt_sim (rules : Rules Q I V) (fp : V → F) (oldInp newInp : I → V) (n : Nat)
    (f : DB Q I V F → Key Q I → Out V × DB Q I V F)
    (hf_inv : ∀ s k, Inv rules fp oldInp newInp s → Inv rules fp oldInp newInp (f s k).2)
    (hf_val : ∀ s k v, Inv rules fp oldInp newInp s → (f s k).1 = .val v →
      ∃ m, eval rules newInp m k = .val v)
    (hf_pan : ∀ s k, Inv rules fp oldInp newInp s → (f s k).1 = .panic →
      ∃ m, eval rules newInp m k = .panic)
    (hf_adeq : ∀ s k, Inv rules fp oldInp newInp s → eval rules newInp n k ≠ .stuck →
      (f s k).1 ≠ .stuck) :
    ∀ (p : Prog (Key Q I) V) (db : DB Q I V F), Inv rules fp oldInp newInp db →
      ((p.runSt fp f db).1 = .panic → ∃ M, p.run (eval rules newInp M) = .panic) ∧
      (p.run (eval rules newInp n) ≠ .stuck → (p.runSt fp f db).1 ≠ .stuck)
  | .ret _, _, _ => ⟨fun h => by simp [Prog.runSt] at h, fun _ h => by simp [Prog.runSt] at h⟩
  | .panic, _, _ => ⟨fun _ => ⟨0, rfl⟩, fun _ h => by simp [Prog.runSt] at h⟩
  | .fetch k c, db, hinv => by
    have hinv₁ := hf_inv db k hinv
    refine ⟨fun hpan => ?_, fun hne => ?_⟩
    · simp only [Prog.runSt] at hpan
      cases hfk : f db k with
      | mk o db₁ =>
        rw [hfk] at hpan hinv₁
        cases o with
        | stuck => cases hpan
        | panic =>
          obtain ⟨m₁, hm₁⟩ := hf_pan db k hinv (by rw [hfk])
          exact ⟨m₁, by simp [Prog.run, hm₁]⟩
        | val v =>
          simp only at hpan
          obtain ⟨m₁, hm₁⟩ := hf_val db k v hinv (by rw [hfk])
          have hrec := (runSt_sim rules fp oldInp newInp n f hf_inv hf_val hf_pan hf_adeq
            (c v) db₁ hinv₁).1
          cases hcr : (c v).runSt fp f db₁ with
          | mk o' rest =>
            cases rest with
            | mk tr' db₂ =>
              rw [hcr] at hpan hrec
              obtain ⟨M₂, hM₂⟩ := hrec hpan
              refine ⟨max m₁ M₂, ?_⟩
              have hm₁' : eval rules newInp (max m₁ M₂) k = .val v := by
                rw [eval_mono rules newInp m₁ (max m₁ M₂) k (Nat.le_max_left _ _)
                  (by rw [hm₁]; intro h; cases h)]
                exact hm₁
              have hM₂' : (c v).run (eval rules newInp (max m₁ M₂)) = .panic := by
                rw [Prog.run_congr_of_ne_stuck (eval rules newInp M₂)
                  (eval rules newInp (max m₁ M₂))
                  (fun k' hk' => eval_mono rules newInp M₂ (max m₁ M₂) k' (Nat.le_max_right _ _) hk')
                  (c v) (by rw [hM₂]; intro h; cases h)]
                exact hM₂
              simp [Prog.run, hm₁', hM₂']
    · simp only [Prog.run] at hne
      have hk_ne : eval rules newInp n k ≠ .stuck := by
        intro h0; rw [h0] at hne; exact hne rfl
      have hmatch : (f db k).1 = eval rules newInp n k :=
        hf_match_of_sim rules fp oldInp newInp n f hf_val hf_pan hf_adeq db k hinv hk_ne
      simp only [Prog.runSt]
      cases hfk : f db k with
      | mk o db₁ =>
        rw [hfk] at hmatch hinv₁
        simp only at hmatch
        cases hek : eval rules newInp n k with
        | stuck => exact absurd hek hk_ne
        | panic => rw [hek] at hmatch; subst hmatch; simp
        | val v =>
          rw [hek] at hmatch hne
          subst hmatch
          simp only
          have hrec := (runSt_sim rules fp oldInp newInp n f hf_inv hf_val hf_pan hf_adeq
            (c v) db₁ hinv₁).2 hne
          cases hcr : (c v).runSt fp f db₁ with
          | mk o' rest =>
            cases rest with
            | mk tr' db₂ =>
              rw [hcr] at hrec
              exact hrec

omit [DecidableEq F] in
private theorem exec_sim (rules : Rules Q I V) (fp : V → F) (oldInp newInp : I → V) (n : Nat)
    (f : DB Q I V F → Key Q I → Out V × DB Q I V F)
    (hf_inv : ∀ s k, Inv rules fp oldInp newInp s → Inv rules fp oldInp newInp (f s k).2)
    (hf_val : ∀ s k v, Inv rules fp oldInp newInp s → (f s k).1 = .val v →
      ∃ m, eval rules newInp m k = .val v)
    (hf_pan : ∀ s k, Inv rules fp oldInp newInp s → (f s k).1 = .panic →
      ∃ m, eval rules newInp m k = .panic)
    (hf_adeq : ∀ s k, Inv rules fp oldInp newInp s → eval rules newInp n k ≠ .stuck →
      (f s k).1 ≠ .stuck)
    (db : DB Q I V F) (q : Q) (hinv : Inv rules fp oldInp newInp db) :
    ((exec rules fp f db q).1 = .panic → ∃ m, eval rules newInp m (.inl q) = .panic) ∧
    (eval rules newInp (n + 1) (.inl q) ≠ .stuck → (exec rules fp f db q).1 ≠ .stuck) := by
  have hrun := runSt_sim rules fp oldInp newInp n f hf_inv hf_val hf_pan hf_adeq (rules q) db hinv
  unfold exec
  cases hr : (rules q).runSt fp f db with
  | mk o rest =>
    cases rest with
    | mk tr db₁ =>
      rw [hr] at hrun
      refine ⟨fun hp => ?_, fun hne => ?_⟩
      · cases o with
        | val _ => cases hp
        | stuck => cases hp
        | panic =>
          obtain ⟨M, hM⟩ := hrun.1 rfl
          exact ⟨M + 1, hM⟩
      · have hne' := hrun.2 hne
        cases o with
        | val _ => intro h; cases h
        | panic => intro h; cases h
        | stuck => exact absurd rfl hne'

omit [DecidableEq Q] in
private theorem checkDeps_ordered_sim (cutoff : Bool)
    (rules : Rules Q I V) (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V)
    (n n₀ : Nat) (v_old : V)
    (f : DB Q I V F → Key Q I → Out V × DB Q I V F)
    (hf_inv : ∀ s k, Inv rules fp oldInp newInp s → Inv rules fp oldInp newInp (f s k).2)
    (hf_val : ∀ s k v, Inv rules fp oldInp newInp s → (f s k).1 = .val v →
      ∃ m, eval rules newInp m k = .val v)
    (hf_pan : ∀ s k, Inv rules fp oldInp newInp s → (f s k).1 = .panic →
      ∃ m, eval rules newInp m k = .panic)
    (hf_adeq : ∀ s k, Inv rules fp oldInp newInp s → eval rules newInp n k ≠ .stuck →
      (f s k).1 ≠ .stuck) :
    ∀ (p : Prog (Key Q I) V) (deps : List (Key Q I × F)) (db : DB Q I V F),
      p.runT (eval rules oldInp n₀) fp = (.val v_old, deps) →
      Inv rules fp oldInp newInp db →
      ((checkDeps cutoff true fp f db deps false).1 = .panic →
        ∃ M, p.run (eval rules newInp M) = .panic) ∧
      (p.run (eval rules newInp n) ≠ .stuck →
        (checkDeps cutoff true fp f db deps false).1 ≠ .stuck)
  | .ret w, deps, db, htr, _ => by
    simp only [Prog.runT, Prod.mk.injEq] at htr
    obtain ⟨_, rfl⟩ := htr
    exact ⟨fun h => by simp [checkDeps] at h, fun _ h => by simp [checkDeps] at h⟩
  | .panic, _, _, htr, _ => by
    simp only [Prog.runT, Prod.mk.injEq] at htr
    cases htr.1
  | .fetch d c, deps, db, htr, hinv => by
    simp only [Prog.runT] at htr
    cases hold_d : eval rules oldInp n₀ d with
    | panic => rw [hold_d] at htr; simp at htr
    | stuck => rw [hold_d] at htr; simp at htr
    | val v₀ =>
      rw [hold_d] at htr
      simp only at htr
      cases hcr : (c v₀).runT (eval rules oldInp n₀) fp with
      | mk o_old rest =>
        rw [hcr] at htr
        simp only [Prod.mk.injEq] at htr
        obtain ⟨ho_old, hdeps_eq⟩ := htr
        subst ho_old; subst hdeps_eq
        have hinv₁ := hf_inv db d hinv
        refine ⟨fun hpan => ?_, fun hne => ?_⟩
        · simp only [checkDeps] at hpan
          cases hfd : f db d with
          | mk o db₁ =>
            rw [hfd] at hpan hinv₁
            cases o with
            | stuck => cases hpan
            | panic =>
              obtain ⟨m₁, hm₁⟩ := hf_pan db d hinv (by rw [hfd])
              exact ⟨m₁, by simp [Prog.run, hm₁]⟩
            | val v =>
              simp only at hpan
              by_cases hchg : changedAt cutoff fp db₁ d v (fp v₀) = true
              · simp [hchg] at hpan
              · simp only [hchg, Bool.false_eq_true, ↓reduceIte] at hpan
                have hfp_eq : fp v = fp v₀ := by
                  unfold changedAt at hchg
                  by_cases he : fp v = fp v₀
                  · exact he
                  · simp [he] at hchg
                have hveq : v = v₀ := hfp v v₀ hfp_eq
                subst hveq
                obtain ⟨m₁, hm₁⟩ := hf_val db d v hinv (by rw [hfd])
                obtain ⟨M₂, hM₂⟩ := (checkDeps_ordered_sim cutoff rules fp hfp oldInp newInp n n₀
                  v_old f hf_inv hf_val hf_pan hf_adeq (c v) rest db₁ hcr hinv₁).1 hpan
                refine ⟨max m₁ M₂, ?_⟩
                have hm₁' : eval rules newInp (max m₁ M₂) d = .val v := by
                  rw [eval_mono rules newInp m₁ (max m₁ M₂) d (Nat.le_max_left _ _)
                    (by rw [hm₁]; intro h; cases h)]
                  exact hm₁
                have hM₂' : (c v).run (eval rules newInp (max m₁ M₂)) = .panic := by
                  rw [Prog.run_congr_of_ne_stuck (eval rules newInp M₂)
                    (eval rules newInp (max m₁ M₂))
                    (fun k' hk' => eval_mono rules newInp M₂ (max m₁ M₂) k' (Nat.le_max_right _ _) hk')
                    (c v) (by rw [hM₂]; intro h; cases h)]
                  exact hM₂
                simp [Prog.run, hm₁', hM₂']
        · simp only [Prog.run] at hne
          have hd_ne : eval rules newInp n d ≠ .stuck := by
            intro h0; rw [h0] at hne; exact hne rfl
          have hmatch : (f db d).1 = eval rules newInp n d :=
            hf_match_of_sim rules fp oldInp newInp n f hf_val hf_pan hf_adeq db d hinv hd_ne
          simp only [checkDeps]
          cases hfd : f db d with
          | mk o db₁ =>
            rw [hfd] at hmatch hinv₁
            simp only at hmatch
            cases hed : eval rules newInp n d with
            | stuck => exact absurd hed hd_ne
            | panic => rw [hed] at hmatch; subst hmatch; simp
            | val v =>
              rw [hed] at hmatch hne
              subst hmatch
              simp only
              by_cases hchg : changedAt cutoff fp db₁ d v (fp v₀) = true
              · simp [hchg]
              · simp only [hchg, Bool.false_eq_true, ↓reduceIte]
                have hfp_eq : fp v = fp v₀ := by
                  unfold changedAt at hchg
                  by_cases he : fp v = fp v₀
                  · exact he
                  · simp [he] at hchg
                have hveq : v = v₀ := hfp v v₀ hfp_eq
                subst hveq
                exact (checkDeps_ordered_sim cutoff rules fp hfp oldInp newInp n n₀ v_old f
                  hf_inv hf_val hf_pan hf_adeq (c v) rest db₁ hcr hinv₁).2 hne

/-- **Main simulation invariant.**  For ordered replay (with or without early
cutoff) and collision-free fingerprints, one incremental fetch from a working
database satisfying `Inv` (old slots consistent with the old state, done
slots with the new state)

* returns a database that again satisfies `Inv`;
* if it finishes, returns the from-scratch outcome (value or panic) of the new
  state;
* finishes whenever from-scratch evaluation finishes with the same fuel. -/
theorem fetch_simulation_invariant (cfg : Config) (hord : cfg.replay = .ordered)
    (rules : Rules Q I V) (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V) :
    ∀ (n : Nat) (db : DB Q I V F) (k : Key Q I), Inv rules fp oldInp newInp db →
      Inv rules fp oldInp newInp (fetch cfg rules fp newInp n db k).2 ∧
      ((fetch cfg rules fp newInp n db k).1 ≠ .stuck →
          ∃ m, eval rules newInp m k = (fetch cfg rules fp newInp n db k).1) ∧
      (eval rules newInp n k ≠ .stuck → (fetch cfg rules fp newInp n db k).1 ≠ .stuck)
  | 0, db, _, hinv => ⟨hinv, fun h => absurd rfl h, fun h => absurd rfl h⟩
  | _ + 1, db, .inr i, hinv => ⟨hinv, fun _ => ⟨1, rfl⟩, fun _ h => by cases h⟩
  | n + 1, db, .inl q, hinv => by
    have hvs := fetch_inv_and_value_sound cfg rules fp hfp oldInp newInp (n + 1) db (.inl q) hinv
    have hf_inv : ∀ s k, Inv rules fp oldInp newInp s →
        Inv rules fp oldInp newInp (fetch cfg rules fp newInp n s k).2 :=
      fun s k hs => (fetch_inv_and_value_sound cfg rules fp hfp oldInp newInp n s k hs).1
    have hf_val : ∀ s k v, Inv rules fp oldInp newInp s →
        (fetch cfg rules fp newInp n s k).1 = .val v → ∃ m, eval rules newInp m k = .val v :=
      fun s k v hs hv => (fetch_inv_and_value_sound cfg rules fp hfp oldInp newInp n s k hs).2 v hv
    have hf_pan : ∀ s k, Inv rules fp oldInp newInp s →
        (fetch cfg rules fp newInp n s k).1 = .panic → ∃ m, eval rules newInp m k = .panic := by
      intro s k hs hp
      obtain ⟨m, hm⟩ := (fetch_simulation_invariant cfg hord rules fp hfp oldInp newInp
        n s k hs).2.1 (by rw [hp]; intro h; cases h)
      exact ⟨m, hm.trans hp⟩
    have hf_adeq : ∀ s k, Inv rules fp oldInp newInp s →
        eval rules newInp n k ≠ .stuck → (fetch cfg rules fp newInp n s k).1 ≠ .stuck :=
      fun s k hs hne => (fetch_simulation_invariant cfg hord rules fp hfp oldInp newInp
        n s k hs).2.2 hne
    refine ⟨hvs.1, fun hfn => ?_, fun hen => ?_⟩
    · cases hfo : (fetch cfg rules fp newInp (n + 1) db (.inl q)).1 with
      | stuck => exact absurd hfo hfn
      | val v => exact hvs.2 v hfo
      | panic =>
        simp only [fetch] at hfo
        cases hq : db q with
        | done e b => rw [hq] at hfo; cases hfo
        | none =>
          rw [hq] at hfo
          exact (exec_sim rules fp oldInp newInp n _ hf_inv hf_val hf_pan hf_adeq db q hinv).1 hfo
        | old e =>
          rw [hq] at hfo
          simp only at hfo
          have hold : EntryConsistent rules fp oldInp q e := by
            have := hinv q; rw [hq] at this; exact this
          obtain ⟨n₀, hn₀⟩ := hold
          have hmg_inv : Inv rules fp oldInp newInp
              (markGreen cfg fp (fetch cfg rules fp newInp n) db e.deps).2 := by
            unfold markGreen; rw [hord]
            exact (checkDeps_value_sound cfg.cutoff true rules fp oldInp newInp _
              hf_inv hf_val e.deps db false hinv).1
          have hmg_sim := checkDeps_ordered_sim cfg.cutoff rules fp hfp oldInp newInp n n₀
            e.value _ hf_inv hf_val hf_pan hf_adeq (rules q) e.deps db hn₀ hinv
          cases hm : markGreen cfg fp (fetch cfg rules fp newInp n) db e.deps with
          | mk verdict db₁ =>
            rw [hm] at hfo hmg_inv
            have hm' : checkDeps cfg.cutoff true fp (fetch cfg rules fp newInp n) db e.deps false =
                (verdict, db₁) := by
              unfold markGreen at hm; rw [hord] at hm; exact hm
            cases verdict with
            | green => cases hfo
            | stuck => cases hfo
            | panic =>
              obtain ⟨M, hM⟩ := hmg_sim.1 (by rw [hm'])
              exact ⟨M + 1, hM⟩
            | red =>
              exact (exec_sim rules fp oldInp newInp n _ hf_inv hf_val hf_pan hf_adeq db₁ q
                hmg_inv).1 hfo
    · simp only [fetch]
      cases hq : db q with
      | done e b => intro h; cases h
      | none =>
        exact (exec_sim rules fp oldInp newInp n _ hf_inv hf_val hf_pan hf_adeq db q hinv).2 hen
      | old e =>
        simp only
        have hold : EntryConsistent rules fp oldInp q e := by
          have := hinv q; rw [hq] at this; exact this
        obtain ⟨n₀, hn₀⟩ := hold
        have hmg_inv : Inv rules fp oldInp newInp
            (markGreen cfg fp (fetch cfg rules fp newInp n) db e.deps).2 := by
          unfold markGreen; rw [hord]
          exact (checkDeps_value_sound cfg.cutoff true rules fp oldInp newInp _
            hf_inv hf_val e.deps db false hinv).1
        have hmg_adeq := (checkDeps_ordered_sim cfg.cutoff rules fp hfp oldInp newInp n n₀
          e.value _ hf_inv hf_val hf_pan hf_adeq (rules q) e.deps db hn₀ hinv).2 hen
        cases hm : markGreen cfg fp (fetch cfg rules fp newInp n) db e.deps with
        | mk verdict db₁ =>
          rw [hm] at hmg_inv
          have hm' : checkDeps cfg.cutoff true fp (fetch cfg rules fp newInp n) db e.deps false =
              (verdict, db₁) := by
            unfold markGreen at hm; rw [hord] at hm; exact hm
          rw [hm'] at hmg_adeq
          cases verdict with
          | green => intro h; cases h
          | panic => intro h; cases h
          | stuck => exact absurd rfl hmg_adeq
          | red =>
            exact (exec_sim rules fp oldInp newInp n _ hf_inv hf_val hf_pan hf_adeq db₁ q
              hmg_inv).2 hen

/-- `AgreesWithEval` implies eventual equality of the fuel-indexed outcomes. -/
theorem eventually_eq_eval_of_agrees {cfg : Config} {rules : Rules Q I V} {fp : V → F}
    {inp : I → V} {db : DB Q I V F} {k : Key Q I} (h : AgreesWithEval cfg rules fp inp db k) :
    ∃ N, ∀ m, N ≤ m → (fetch cfg rules fp inp m db k).1 = eval rules inp m k := by
  by_cases ht : ∃ n, eval rules inp n k ≠ .stuck
  · obtain ⟨n, hn⟩ := ht
    refine ⟨n, fun m hm => ?_⟩
    have hem : eval rules inp m k = eval rules inp n k := eval_mono rules inp n m k hm hn
    have hfm : (fetch cfg rules fp inp m db k).1 ≠ .stuck := h.2 m (by rw [hem]; exact hn)
    obtain ⟨n', hn'⟩ := h.1 m hfm
    rw [← hn']
    have hn's : eval rules inp n' k ≠ .stuck := by rw [hn']; exact hfm
    exact eval_eq_of_ne_stuck rules inp k hn's (by rw [hem]; exact hn)
  · refine ⟨0, fun m _ => ?_⟩
    have hs : ∀ n, eval rules inp n k = .stuck :=
      fun n => Classical.byContradiction fun hne => ht ⟨n, hne⟩
    rw [hs m]
    exact Classical.byContradiction fun hf => by
      obtain ⟨n', hn'⟩ := h.1 m hf
      rw [hs n'] at hn'
      exact hf hn'.symm

end General

/-! ## Card `incremental-fetch-agrees` -/

section Agrees

variable {Q I V F : Type} [DecidableEq Q] [DecidableEq F]

/-- **Agreement of ordered red-green replay (first demand).**  With ordered
replay (early cutoff on or off), collision-free fingerprints, the same query
code as the one that produced the database, and a database consistent with
the old input state, the incremental fetch of any key at the start of a
revision agrees with from-scratch evaluation in the new state (partial
correctness, and adequacy at equal fuel). -/
theorem fetch_agrees_with_eval_of_ordered_replay (cfg : Config) (hord : cfg.replay = .ordered)
    (rulesOld rulesNew : Rules Q I V) (hsame : rulesOld = rulesNew)
    (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V) (odb : OldDB Q I V F)
    (hcons : DBConsistent rulesOld fp oldInp odb) (k : Key Q I) :
    AgreesWithEval cfg rulesNew fp newInp (start odb) k := by
  subst hsame
  have hinv := inv_start rulesOld fp oldInp newInp odb hcons
  exact ⟨fun m => (fetch_simulation_invariant cfg hord rulesOld fp hfp oldInp newInp m _ k hinv).2.1,
    fun n => (fetch_simulation_invariant cfg hord rulesOld fp hfp oldInp newInp n _ k hinv).2.2⟩

/-- **Agreement during a whole revision.**  Under the same hypotheses, every
fetch made from a working database reachable from the start of the revision
by earlier fetches (of any keys, with any fuel) agrees with from-scratch
evaluation in the new state. -/
theorem fetch_agrees_with_eval_during_revision_of_ordered_replay (cfg : Config)
    (hord : cfg.replay = .ordered) (rulesOld rulesNew : Rules Q I V) (hsame : rulesOld = rulesNew)
    (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V) (odb : OldDB Q I V F)
    (hcons : DBConsistent rulesOld fp oldInp odb) (db : DB Q I V F)
    (hreach : Reachable cfg rulesNew fp newInp (start odb) db) (k : Key Q I) :
    AgreesWithEval cfg rulesNew fp newInp db k := by
  subst hsame
  have hinv := inv_of_reachable cfg rulesOld fp hfp oldInp newInp _ db
    (inv_start rulesOld fp oldInp newInp odb hcons) hreach
  exact ⟨fun m => (fetch_simulation_invariant cfg hord rulesOld fp hfp oldInp newInp m db k hinv).2.1,
    fun n => (fetch_simulation_invariant cfg hord rulesOld fp hfp oldInp newInp n db k hinv).2.2⟩

/-- **Eventual equality during a whole revision.**  Under the same hypotheses,
for every working database reachable from the start of the revision (in
particular the start database itself, `Reachable.refl`), for all sufficiently
large fuel the incremental fetch and from-scratch evaluation have the same
outcome — including the case where both are `stuck` at every fuel. -/
theorem fetch_eventually_eq_eval_during_revision_of_ordered_replay (cfg : Config)
    (hord : cfg.replay = .ordered) (rulesOld rulesNew : Rules Q I V) (hsame : rulesOld = rulesNew)
    (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V) (odb : OldDB Q I V F)
    (hcons : DBConsistent rulesOld fp oldInp odb) (db : DB Q I V F)
    (hreach : Reachable cfg rulesNew fp newInp (start odb) db) (k : Key Q I) :
    ∃ N, ∀ m, N ≤ m → (fetch cfg rulesNew fp newInp m db k).1 = eval rulesNew newInp m k :=
  eventually_eq_eval_of_agrees
    (fetch_agrees_with_eval_during_revision_of_ordered_replay cfg hord rulesOld rulesNew hsame fp
      hfp oldInp newInp odb hcons db hreach k)

/-- **Termination transfer during a whole revision.**  Under the same
hypotheses, if `k` terminates from scratch in the new state, then for every
working database reachable from the start of the revision the incremental
fetch of `k` finishes for all sufficiently large fuel. -/
theorem fetch_eventually_finishes_during_revision_of_terminates (cfg : Config)
    (hord : cfg.replay = .ordered) (rulesOld rulesNew : Rules Q I V) (hsame : rulesOld = rulesNew)
    (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V) (odb : OldDB Q I V F)
    (hcons : DBConsistent rulesOld fp oldInp odb) (db : DB Q I V F)
    (hreach : Reachable cfg rulesNew fp newInp (start odb) db) (k : Key Q I)
    (hterm : Terminates rulesNew newInp k) :
    ∃ N, ∀ m, N ≤ m → (fetch cfg rulesNew fp newInp m db k).1 ≠ .stuck := by
  obtain ⟨n, hn⟩ := hterm
  have h := fetch_agrees_with_eval_during_revision_of_ordered_replay cfg hord rulesOld rulesNew
    hsame fp hfp oldInp newInp odb hcons db hreach k
  exact ⟨n, fun m hm => h.2 m (by rw [eval_mono rulesNew newInp n m k hm hn]; exact hn)⟩

end Agrees

/-! ## Card `early-cutoff-agrees-with-reexecution` -/

section Cutoff

variable {Q I V F : Type} [DecidableEq Q] [DecidableEq F]

/-- **Early cutoff agrees with full re-execution (reference corollary of
`incremental-fetch-agrees`).**  With ordered replay, collision-free
fingerprints, the same query code as the one that produced the database, and
a database consistent with the old input state, the first incremental fetch of
a revision with early cutoff (a re-executed dependency that reproduces its
recorded fingerprint counts as unchanged) and without it (every dependent of a
re-executed query is re-executed) return the same outcome: whenever both
finish, at any fuels, their outcomes are equal; and for all sufficiently large
fuel their outcomes are equal.  Only outcomes are compared; the working
databases the two modes leave behind differ. -/
theorem early_cutoff_agrees_with_reexecution_of_ordered_replay (r : Replay) (hord : r = .ordered)
    (rulesOld rulesNew : Rules Q I V) (hsame : rulesOld = rulesNew)
    (fp : V → F) (hfp : FpInjective fp) (oldInp newInp : I → V) (odb : OldDB Q I V F)
    (hcons : DBConsistent rulesOld fp oldInp odb) (k : Key Q I) :
    (∀ m₁ m₂,
      (fetch ⟨r, true⟩ rulesNew fp newInp m₁ (start odb) k).1 ≠ .stuck →
      (fetch ⟨r, false⟩ rulesNew fp newInp m₂ (start odb) k).1 ≠ .stuck →
      (fetch ⟨r, true⟩ rulesNew fp newInp m₁ (start odb) k).1 =
        (fetch ⟨r, false⟩ rulesNew fp newInp m₂ (start odb) k).1) ∧
    (∃ N, ∀ m, N ≤ m →
      (fetch ⟨r, true⟩ rulesNew fp newInp m (start odb) k).1 =
        (fetch ⟨r, false⟩ rulesNew fp newInp m (start odb) k).1) := by
  subst hord
  have h₁ := fetch_agrees_with_eval_of_ordered_replay ⟨.ordered, true⟩ rfl rulesOld rulesNew hsame
    fp hfp oldInp newInp odb hcons k
  have h₂ := fetch_agrees_with_eval_of_ordered_replay ⟨.ordered, false⟩ rfl rulesOld rulesNew hsame
    fp hfp oldInp newInp odb hcons k
  refine ⟨fun m₁ m₂ hm₁ hm₂ => ?_, ?_⟩
  · obtain ⟨n₁, hn₁⟩ := h₁.1 m₁ hm₁
    obtain ⟨n₂, hn₂⟩ := h₂.1 m₂ hm₂
    rw [← hn₁, ← hn₂]
    exact eval_eq_of_ne_stuck rulesNew newInp k (by rw [hn₁]; exact hm₁) (by rw [hn₂]; exact hm₂)
  · obtain ⟨N₁, hN₁⟩ := eventually_eq_eval_of_agrees h₁
    obtain ⟨N₂, hN₂⟩ := eventually_eq_eval_of_agrees h₂
    exact ⟨max N₁ N₂, fun m hm => by
      rw [hN₁ m (Nat.le_trans (Nat.le_max_left _ _) hm), hN₂ m (Nat.le_trans (Nat.le_max_right _ _) hm)]⟩

end Cutoff

end Toy.RedGreen
