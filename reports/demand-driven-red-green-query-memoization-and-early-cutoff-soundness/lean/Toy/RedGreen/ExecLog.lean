/-
Toy.RedGreen.ExecLog
====================

An instrumented copy of the incremental algorithm that also records, in
order, every query whose code it starts to run (every call of `exec`),
whether that run then returns a value, panics, or runs out of fuel.  The
instrumentation does not change the algorithm: `fetchX_eq` proves that the
outcome and working database of `fetchX` are exactly those of `fetch`, and
that the log only grows by appending.

`execLog cfg rules fp inp n db k` is the list of queries executed by
`fetch cfg rules fp inp n db k`.  A query absent from it was never executed
during that fetch, not even partially.  (The slot of a query whose execution
aborts is left unchanged by `fetch`, so slots alone cannot show this.)

All fully proved.
-/
import Toy.RedGreen.Basic

namespace Toy.RedGreen

/-- State of the instrumented algorithm: the working database and the log of
executed queries, oldest first. -/
abbrev LDB (Q I V F : Type) := DB Q I V F × List Q

/-- `checkDeps` on the instrumented state (same control flow; the log is
threaded through the fetcher). -/
def checkDepsX {Q I V F : Type} [DecidableEq F] (cutoff stopAtRed : Bool) (fp : V → F)
    (f : LDB Q I V F → Key Q I → Out V × LDB Q I V F) :
    LDB Q I V F → List (Key Q I × F) → Bool → Verdict × LDB Q I V F
  | s, [], anyRed => (if anyRed then .red else .green, s)
  | s, (d, fd) :: rest, anyRed =>
    match f s d with
    | (.val v, s₁) =>
      if changedAt cutoff fp s₁.1 d v fd then
        if stopAtRed then (.red, s₁) else checkDepsX cutoff stopAtRed fp f s₁ rest true
      else checkDepsX cutoff stopAtRed fp f s₁ rest anyRed
    | (.panic, s₁) => (.panic, s₁)
    | (.stuck, s₁) => (.stuck, s₁)

/-- `markGreen` on the instrumented state. -/
def markGreenX {Q I V F : Type} [DecidableEq F] (cfg : Config) (fp : V → F)
    (f : LDB Q I V F → Key Q I → Out V × LDB Q I V F) (s : LDB Q I V F)
    (deps : List (Key Q I × F)) : Verdict × LDB Q I V F :=
  match cfg.replay with
  | .ordered => checkDepsX cfg.cutoff true fp f s deps false
  | .reversed => checkDepsX cfg.cutoff true fp f s deps.reverse false
  | .exhaustive => checkDepsX cfg.cutoff false fp f s deps false

/-- `exec` on the instrumented state: appends `q` to the log before running
`q`'s code. -/
def execX {Q I V F : Type} [DecidableEq Q] (rules : Rules Q I V) (fp : V → F)
    (f : LDB Q I V F → Key Q I → Out V × LDB Q I V F) (s : LDB Q I V F) (q : Q) :
    Out V × LDB Q I V F :=
  match (rules q).runSt fp f (s.1, s.2 ++ [q]) with
  | (.val v, tr, s₁) => (.val v, (s₁.1.set q (.done ⟨tr, v⟩ true), s₁.2))
  | (.panic, _, s₁) => (.panic, s₁)
  | (.stuck, _, s₁) => (.stuck, s₁)

/-- `fetch` on the instrumented state (same control flow as `fetch`). -/
def fetchX {Q I V F : Type} [DecidableEq Q] [DecidableEq F] (cfg : Config) (rules : Rules Q I V)
    (fp : V → F) (inp : I → V) : Nat → LDB Q I V F → Key Q I → Out V × LDB Q I V F
  | 0, s, _ => (.stuck, s)
  | _ + 1, s, .inr i => (.val (inp i), s)
  | n + 1, s, .inl q =>
    match s.1 q with
    | .done e _ => (.val e.value, s)
    | .old e =>
      match markGreenX cfg fp (fetchX cfg rules fp inp n) s e.deps with
      | (.green, s₁) => (.val e.value, (s₁.1.set q (.done e false), s₁.2))
      | (.red, s₁) => execX rules fp (fetchX cfg rules fp inp n) s₁ q
      | (.panic, s₁) => (.panic, s₁)
      | (.stuck, s₁) => (.stuck, s₁)
    | .none => execX rules fp (fetchX cfg rules fp inp n) s q

/-- The queries executed (code started, in order) by
`fetch cfg rules fp inp n db k`. -/
def execLog {Q I V F : Type} [DecidableEq Q] [DecidableEq F] (cfg : Config) (rules : Rules Q I V)
    (fp : V → F) (inp : I → V) (n : Nat) (db : DB Q I V F) (k : Key Q I) : List Q :=
  (fetchX cfg rules fp inp n (db, []) k).2.2

/-! ## The instrumentation does not change the algorithm -/

section Adequacy

variable {Q I V F : Type}

/-- An instrumented fetcher `g` tracks `f`: same outcome and database, and the
log is extended by a suffix that does not depend on the incoming log. -/
def Tracks (g : LDB Q I V F → Key Q I → Out V × LDB Q I V F)
    (f : DB Q I V F → Key Q I → Out V × DB Q I V F) : Prop :=
  ∀ db k, ∃ L : List Q, ∀ l, g (db, l) k = ((f db k).1, ((f db k).2, l ++ L))

theorem runSt_tracks (fp : V → F) (g : LDB Q I V F → Key Q I → Out V × LDB Q I V F)
    (f : DB Q I V F → Key Q I → Out V × DB Q I V F) (hg : Tracks g f) :
    ∀ (p : Prog (Key Q I) V) (db : DB Q I V F), ∃ L : List Q, ∀ l,
      p.runSt fp g (db, l) =
        ((p.runSt fp f db).1, (p.runSt fp f db).2.1, ((p.runSt fp f db).2.2, l ++ L))
  | .ret _, db => ⟨[], fun l => by simp [Prog.runSt]⟩
  | .panic, db => ⟨[], fun l => by simp [Prog.runSt]⟩
  | .fetch k c, db => by
    obtain ⟨L₁, h₁⟩ := hg db k
    cases hf : f db k with
    | mk o db₁ =>
      cases o with
      | val v =>
        obtain ⟨L₂, h₂⟩ := runSt_tracks fp g f hg (c v) db₁
        refine ⟨L₁ ++ L₂, fun l => ?_⟩
        cases hc : (c v).runSt fp f db₁ with
        | mk o rest =>
          cases rest with
          | mk tr db₂ =>
            have h₂' := h₂ (l ++ L₁)
            rw [hc] at h₂'
            simp only [Prog.runSt, h₁ l, hf, h₂', hc, List.append_assoc]
      | panic => exact ⟨L₁, fun l => by simp only [Prog.runSt, h₁ l, hf]⟩
      | stuck => exact ⟨L₁, fun l => by simp only [Prog.runSt, h₁ l, hf]⟩

theorem checkDeps_tracks [DecidableEq F] (cutoff stopAtRed : Bool) (fp : V → F)
    (g : LDB Q I V F → Key Q I → Out V × LDB Q I V F)
    (f : DB Q I V F → Key Q I → Out V × DB Q I V F) (hg : Tracks g f) :
    ∀ (deps : List (Key Q I × F)) (db : DB Q I V F) (anyRed : Bool), ∃ L : List Q, ∀ l,
      checkDepsX cutoff stopAtRed fp g (db, l) deps anyRed =
        ((checkDeps cutoff stopAtRed fp f db deps anyRed).1,
          ((checkDeps cutoff stopAtRed fp f db deps anyRed).2, l ++ L))
  | [], db, anyRed => ⟨[], fun l => by simp [checkDeps, checkDepsX]⟩
  | (d, fd) :: rest, db, anyRed => by
    obtain ⟨L₁, h₁⟩ := hg db d
    cases hf : f db d with
    | mk o db₁ =>
      cases o with
      | val v =>
        by_cases hch : changedAt cutoff fp db₁ d v fd = true
        · cases stopAtRed with
          | true => exact ⟨L₁, fun l => by simp only [checkDepsX, checkDeps, h₁ l, hf, hch, ite_true]⟩
          | false =>
            obtain ⟨L₂, h₂⟩ := checkDeps_tracks cutoff false fp g f hg rest db₁ true
            exact ⟨L₁ ++ L₂, fun l => by
              simp only [checkDepsX, checkDeps, h₁ l, hf, hch, ite_true, Bool.false_eq_true,
                ite_false, h₂ (l ++ L₁), List.append_assoc]⟩
        · obtain ⟨L₂, h₂⟩ := checkDeps_tracks cutoff stopAtRed fp g f hg rest db₁ anyRed
          exact ⟨L₁ ++ L₂, fun l => by
            simp only [checkDepsX, checkDeps, h₁ l, hf, hch, Bool.false_eq_true, ite_false,
              h₂ (l ++ L₁), List.append_assoc]⟩
      | panic => exact ⟨L₁, fun l => by simp only [checkDepsX, checkDeps, h₁ l, hf]⟩
      | stuck => exact ⟨L₁, fun l => by simp only [checkDepsX, checkDeps, h₁ l, hf]⟩

theorem markGreen_tracks [DecidableEq F] (cfg : Config) (fp : V → F)
    (g : LDB Q I V F → Key Q I → Out V × LDB Q I V F)
    (f : DB Q I V F → Key Q I → Out V × DB Q I V F) (hg : Tracks g f)
    (db : DB Q I V F) (deps : List (Key Q I × F)) : ∃ L : List Q, ∀ l,
      markGreenX cfg fp g (db, l) deps =
        ((markGreen cfg fp f db deps).1, ((markGreen cfg fp f db deps).2, l ++ L)) := by
  unfold markGreenX markGreen
  cases cfg.replay with
  | ordered => exact checkDeps_tracks _ _ fp g f hg _ db _
  | reversed => exact checkDeps_tracks _ _ fp g f hg _ db _
  | exhaustive => exact checkDeps_tracks _ _ fp g f hg _ db _

theorem exec_tracks [DecidableEq Q] (rules : Rules Q I V) (fp : V → F)
    (g : LDB Q I V F → Key Q I → Out V × LDB Q I V F)
    (f : DB Q I V F → Key Q I → Out V × DB Q I V F) (hg : Tracks g f)
    (db : DB Q I V F) (q : Q) : ∃ L : List Q, ∀ l,
      execX rules fp g (db, l) q =
        ((exec rules fp f db q).1, ((exec rules fp f db q).2, l ++ (q :: L))) := by
  obtain ⟨L, h⟩ := runSt_tracks fp g f hg (rules q) db
  refine ⟨L, fun l => ?_⟩
  have h' := h (l ++ [q])
  unfold execX exec
  cases hr : (rules q).runSt fp f db with
  | mk o rest =>
    cases rest with
    | mk tr db₁ =>
      rw [hr] at h'
      cases o with
      | val v => simp only [h', List.append_assoc, List.cons_append, List.nil_append]
      | panic => simp only [h', List.append_assoc, List.cons_append, List.nil_append]
      | stuck => simp only [h', List.append_assoc, List.cons_append, List.nil_append]

theorem fetchX_tracks [DecidableEq Q] [DecidableEq F] (cfg : Config) (rules : Rules Q I V)
    (fp : V → F) (inp : I → V) :
    ∀ (n : Nat), Tracks (fetchX cfg rules fp inp n) (fetch cfg rules fp inp n)
  | 0 => fun db k => ⟨[], fun l => by simp [fetchX, fetch]⟩
  | n + 1 => fun db k => by
    have hg := fetchX_tracks cfg rules fp inp n
    cases k with
    | inr i => exact ⟨[], fun l => by simp [fetchX, fetch]⟩
    | inl q =>
      cases hq : db q with
      | done e b => exact ⟨[], fun l => by simp [fetchX, fetch, hq]⟩
      | none =>
        obtain ⟨L, h⟩ := exec_tracks rules fp _ _ hg db q
        exact ⟨q :: L, fun l => by simp only [fetchX, fetch, hq, h l]⟩
      | old e =>
        obtain ⟨L₁, h₁⟩ := markGreen_tracks cfg fp _ _ hg db e.deps
        cases hm : markGreen cfg fp (fetch cfg rules fp inp n) db e.deps with
        | mk verdict db₁ =>
          cases verdict with
          | green => exact ⟨L₁, fun l => by simp only [fetchX, fetch, hq, h₁ l, hm]⟩
          | panic => exact ⟨L₁, fun l => by simp only [fetchX, fetch, hq, h₁ l, hm]⟩
          | stuck => exact ⟨L₁, fun l => by simp only [fetchX, fetch, hq, h₁ l, hm]⟩
          | red =>
            obtain ⟨L₂, h₂⟩ := exec_tracks rules fp _ _ hg db₁ q
            exact ⟨L₁ ++ q :: L₂, fun l => by
              simp only [fetchX, fetch, hq, h₁ l, hm, h₂ (l ++ L₁), List.append_assoc]⟩

/-- **Adequacy of the instrumentation.**  The instrumented fetch has exactly
the outcome and working database of `fetch`, and appends `execLog` to the
incoming log. -/
theorem fetchX_eq [DecidableEq Q] [DecidableEq F] (cfg : Config) (rules : Rules Q I V)
    (fp : V → F) (inp : I → V) (n : Nat) (db : DB Q I V F) (l : List Q) (k : Key Q I) :
    fetchX cfg rules fp inp n (db, l) k =
      ((fetch cfg rules fp inp n db k).1,
        ((fetch cfg rules fp inp n db k).2, l ++ execLog cfg rules fp inp n db k)) := by
  obtain ⟨L, h⟩ := fetchX_tracks cfg rules fp inp n db k
  have h0 := h []
  unfold execLog
  rw [h l, h0]
  simp

end Adequacy

end Toy.RedGreen
