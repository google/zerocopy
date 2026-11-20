/-
Toy.RedGreen.Frame
==================

A fully proved structural fact about the algorithm: an incremental fetch never
creates or changes an `old` slot (it only turns slots into `done` slots).  Used
for the negative examples of `Reachable`.
-/
import Toy.RedGreen.Basic

namespace Toy.RedGreen

variable {Q I V F : Type}

/-- Every `old` slot of `db'` is an identical `old` slot of `db`. -/
def NoNewOld (db db' : DB Q I V F) : Prop :=
  ∀ q e, db' q = .old e → db q = .old e

theorem NoNewOld.refl (db : DB Q I V F) : NoNewOld db db := fun _ _ h => h

theorem NoNewOld.trans {a b c : DB Q I V F} (h₁ : NoNewOld a b) (h₂ : NoNewOld b c) :
    NoNewOld a c := fun q e h => h₁ q e (h₂ q e h)

theorem noNewOld_set_done [DecidableEq Q] (db : DB Q I V F) (q : Q) (e : Entry Q I V F) (b : Bool) :
    NoNewOld db (db.set q (.done e b)) := by
  intro q' e' h
  unfold DB.set at h
  by_cases hq : q' = q
  · simp [hq] at h
  · simpa [hq] using h

theorem runSt_noNewOld (fp : V → F) (f : DB Q I V F → Key Q I → Out V × DB Q I V F)
    (hf : ∀ s k, NoNewOld s (f s k).2) :
    ∀ (p : Prog (Key Q I) V) (s : DB Q I V F), NoNewOld s (p.runSt fp f s).2.2
  | .ret _, s => NoNewOld.refl s
  | .panic, s => NoNewOld.refl s
  | .fetch k c, s => by
    have hk := hf s k
    simp only [Prog.runSt]
    cases hfk : f s k with
    | mk o s₁ =>
      rw [hfk] at hk
      cases o with
      | val v =>
        simp only at hk ⊢
        exact NoNewOld.trans hk (runSt_noNewOld fp f hf (c v) s₁)
      | panic => exact hk
      | stuck => exact hk

theorem checkDeps_noNewOld [DecidableEq F] (cutoff stopAtRed : Bool) (fp : V → F)
    (f : DB Q I V F → Key Q I → Out V × DB Q I V F) (hf : ∀ s k, NoNewOld s (f s k).2) :
    ∀ (deps : List (Key Q I × F)) (db : DB Q I V F) (anyRed : Bool),
      NoNewOld db (checkDeps cutoff stopAtRed fp f db deps anyRed).2
  | [], db, _ => NoNewOld.refl db
  | (d, fd) :: rest, db, anyRed => by
    have hk := hf db d
    simp only [checkDeps]
    cases hfk : f db d with
    | mk o db₁ =>
      rw [hfk] at hk
      cases o with
      | val v =>
        simp only
        split
        · split
          · exact hk
          · exact NoNewOld.trans hk (checkDeps_noNewOld cutoff stopAtRed fp f hf rest db₁ true)
        · exact NoNewOld.trans hk (checkDeps_noNewOld cutoff stopAtRed fp f hf rest db₁ anyRed)
      | panic => exact hk
      | stuck => exact hk

theorem markGreen_noNewOld [DecidableEq F] (cfg : Config) (fp : V → F)
    (f : DB Q I V F → Key Q I → Out V × DB Q I V F) (hf : ∀ s k, NoNewOld s (f s k).2)
    (db : DB Q I V F) (deps : List (Key Q I × F)) :
    NoNewOld db (markGreen cfg fp f db deps).2 := by
  unfold markGreen
  cases cfg.replay with
  | ordered => exact checkDeps_noNewOld _ _ fp f hf _ db _
  | reversed => exact checkDeps_noNewOld _ _ fp f hf _ db _
  | exhaustive => exact checkDeps_noNewOld _ _ fp f hf _ db _

theorem exec_noNewOld [DecidableEq Q] (rules : Rules Q I V) (fp : V → F)
    (f : DB Q I V F → Key Q I → Out V × DB Q I V F) (hf : ∀ s k, NoNewOld s (f s k).2)
    (db : DB Q I V F) (q : Q) : NoNewOld db (exec rules fp f db q).2 := by
  have h := runSt_noNewOld fp f hf (rules q) db
  unfold exec
  cases hr : (rules q).runSt fp f db with
  | mk o rest =>
    cases rest with
    | mk tr db₁ =>
      rw [hr] at h
      cases o with
      | val v => exact NoNewOld.trans h (noNewOld_set_done db₁ q _ true)
      | panic => exact h
      | stuck => exact h

/-- An incremental fetch never creates or changes an `old` slot. -/
theorem fetch_noNewOld [DecidableEq Q] [DecidableEq F] (cfg : Config) (rules : Rules Q I V) (fp : V → F) (inp : I → V) :
    ∀ (n : Nat) (db : DB Q I V F) (k : Key Q I), NoNewOld db (fetch cfg rules fp inp n db k).2
  | 0, db, _ => NoNewOld.refl db
  | _ + 1, db, .inr _ => NoNewOld.refl db
  | n + 1, db, .inl q => by
    have hf : ∀ s k, NoNewOld s (fetch cfg rules fp inp n s k).2 :=
      fun s k => fetch_noNewOld cfg rules fp inp n s k
    simp only [fetch]
    cases hq : db q with
    | done e b => exact NoNewOld.refl db
    | none => exact exec_noNewOld rules fp _ hf db q
    | old e =>
      have hm := markGreen_noNewOld cfg fp _ hf db e.deps
      simp only
      cases hmg : markGreen cfg fp (fetch cfg rules fp inp n) db e.deps with
      | mk verdict db₁ =>
        rw [hmg] at hm
        cases verdict with
        | green => exact NoNewOld.trans hm (noNewOld_set_done db₁ q e false)
        | red => exact NoNewOld.trans hm (exec_noNewOld rules fp _ hf db₁ q)
        | panic => exact hm
        | stuck => exact hm

/-- Every database reachable from `db₀` has no `old` slot that `db₀` lacks. -/
theorem reachable_noNewOld [DecidableEq Q] [DecidableEq F] (cfg : Config) (rules : Rules Q I V) (fp : V → F) (inp : I → V)
    (db₀ db : DB Q I V F) (h : Reachable cfg rules fp inp db₀ db) : NoNewOld db₀ db := by
  induction h with
  | refl => exact NoNewOld.refl db₀
  | step n k _ ih => exact NoNewOld.trans ih (fetch_noNewOld cfg rules fp inp n _ k)

end Toy.RedGreen
