import DoubleFetch.Specs

/-!
# General lemmas about the semantics

Lemmas about `Prog.execFrom`, `Prog.eval`, `Prog.obsFrom` and the single-read discipline, used by
the results.
-/

namespace Toy.DoubleFetch

namespace Prog

variable {n : Nat} {α : Type}

/-- Against the writer that never writes, a run is the private-memory evaluation. -/
theorem execFrom_const (p : Prog n α) (s : Region n) (t : Nat) :
    p.execFrom (Adversary.const s) t = p.eval s := by
  induction p generalizing t with
  | ret a => rfl
  | read i k ih => exact ih (s i) (t + 1)
  | snap k ih => exact ih s (t + 1)

/-- The result component of the observable-read semantics is the ordinary run. -/
theorem obsFrom_snd (p : Prog n α) (adv : Adversary n) (t : Nat) :
    (p.obsFrom adv t).2 = p.execFrom adv t := by
  induction p generalizing t with
  | ret a => rfl
  | read i k ih => exact ih (adv t i) (t + 1)
  | snap k ih => exact ih (adv t) (t + 1)

/-- `exec` against the writer that never writes is `eval`. -/
theorem exec_const (p : Prog n α) (s : Region n) : p.exec (Adversary.const s) = p.eval s :=
  execFrom_const p s 0

/-- The result component of `obs` is `exec`. -/
theorem obs_snd (p : Prog n α) (adv : Adversary n) : (p.obs adv).2 = p.exec adv :=
  obsFrom_snd p adv 0

/-- Under the single-read discipline, private-memory evaluation depends only on the addresses not
yet read. -/
theorem eval_congr_of_singleReadFrom (q : Prog n α) (vis : Fin n → Bool) (s s' : Region n)
    (hq : q.SingleReadFrom vis) (h : ∀ j, vis j = false → s j = s' j) : q.eval s = q.eval s' := by
  induction q generalizing vis with
  | ret a => rfl
  | read i k ih =>
    obtain ⟨hi, hk⟩ := hq
    have hsi : s i = s' i := h i hi
    simp only [eval, hsi]
    apply ih (s' i) _ (hk (s' i))
    intro j hj
    apply h j
    by_cases hji : j = i
    · simp [hji] at hj
    · simpa [hji] using hj
  | snap k ih =>
    obtain ⟨hall, _⟩ := hq
    have hss : s = s' := funext fun j => h j (hall j)
    subst hss
    rfl

/-- A program that may read nothing more (every address already read) returns the same value
against every writer and on every region. -/
theorem execFrom_eq_eval_of_allRead (q : Prog n α) (vis : Fin n → Bool)
    (hvis : ∀ j, vis j = true) (hq : q.SingleReadFrom vis) (adv : Adversary n) (t : Nat)
    (s : Region n) : q.execFrom adv t = q.eval s := by
  induction q generalizing vis t with
  | ret a => rfl
  | read i k ih =>
    obtain ⟨hi, _⟩ := hq
    rw [hvis i] at hi
    exact absurd hi (by decide)
  | snap k ih =>
    obtain ⟨hall, hk⟩ := hq
    have hs : adv t = s := funext fun j => by
      have h1 := hall j
      rw [hvis j] at h1
      exact absurd h1 (by decide)
    simp only [execFrom, eval, hs]
    exact ih s _ (fun _ => rfl) (hk s) (t + 1)

/-- Single-read sufficiency, general form: a run under the single-read discipline returns the
private-memory result on the assembled vector. -/
theorem execFrom_eq_eval_assembleFrom (p : Prog n α) (vis : Fin n → Bool)
    (hp : p.SingleReadFrom vis) (adv : Adversary n) (t : Nat) (d : Region n) :
    p.execFrom adv t = p.eval (p.assembleFrom adv t d) := by
  induction p generalizing vis t with
  | ret a => rfl
  | read i k ih =>
    obtain ⟨_, hk⟩ := hp
    simp only [execFrom, eval, assembleFrom]
    rw [ih (adv t i) _ (hk (adv t i)) (t + 1)]
    apply eval_congr_of_singleReadFrom _ _ _ _ (hk (adv t i))
    intro j hj
    by_cases hji : j = i
    · simp [hji] at hj
    · simp [hji]
  | snap k _ =>
    obtain ⟨_, hk⟩ := hp
    simp only [execFrom, eval, assembleFrom]
    exact execFrom_eq_eval_of_allRead _ _ (fun _ => rfl) (hk _) _ _ _

/-- The address of the `m`-th memory access of the private-memory run of `p` on `s` (`none` if the
run has ended or that access is a snapshot). -/
def addrAt : Prog n α → Region n → Nat → Option (Fin n)
  | ret _, _, _ => none
  | read i _, _, 0 => some i
  | read i k, s, m + 1 => (k (s i)).addrAt s m
  | snap _, _, 0 => none
  | snap k, s, m + 1 => (k s).addrAt s m

/-- A snapshot-free program follows its private-memory run on `s` against every writer that shows,
at each access time, the byte `s` has at the address being read. -/
theorem execFrom_eq_eval_of_agree (p : Prog n α) (s : Region n) (adv : Adversary n) (t0 : Nat)
    (hp : p.NoSnap) (h : ∀ m i, p.addrAt s m = some i → adv (t0 + m) i = s i) :
    p.execFrom adv t0 = p.eval s := by
  induction p generalizing t0 with
  | ret a => rfl
  | read i k ih =>
    have h0 : adv t0 i = s i := by simpa using h 0 i rfl
    simp only [execFrom, eval, h0]
    apply ih (s i) (t0 + 1) (hp (s i))
    intro m j hm
    have h1 := h (m + 1) j (by simpa [addrAt] using hm)
    rw [show t0 + (m + 1) = t0 + 1 + m by omega] at h1
    exact h1
  | snap k _ => exact absurd hp (by simp [NoSnap])

end Prog

section ReadSeq

variable {n : Nat} {α : Type}

/-- The accumulator after reading the list `l` from time `t` against `adv`. -/
def fillSeq (adv : Adversary n) : List (Fin n) → Region n → Nat → Region n
  | [], acc, _ => acc
  | i :: is, acc, t => fillSeq adv is (fun j => if j = i then adv t i else acc j) (t + 1)

theorem readSeq_execFrom (adv : Adversary n) (l : List (Fin n)) (acc : Region n)
    (k : Region n → Prog n α) (t : Nat) :
    (readSeq l acc k).execFrom adv t = (k (fillSeq adv l acc t)).execFrom adv (t + l.length) := by
  induction l generalizing acc t with
  | nil => rfl
  | cons i is ih =>
    simp only [readSeq, Prog.execFrom, fillSeq, List.length_cons]
    rw [ih]
    congr 1
    omega

theorem fillSeq_not_mem (adv : Adversary n) (l : List (Fin n)) (acc : Region n) (t : Nat)
    (j : Fin n) (hj : j ∉ l) : fillSeq adv l acc t j = acc j := by
  induction l generalizing acc t with
  | nil => rfl
  | cons i is ih =>
    simp only [List.mem_cons, not_or] at hj
    simp only [fillSeq]
    rw [ih _ _ hj.2]
    simp [hj.1]

theorem fillSeq_getElem (adv : Adversary n) (l : List (Fin n)) (hl : l.Nodup) (acc : Region n)
    (t m : Nat) (hm : m < l.length) : fillSeq adv l acc t l[m] = adv (t + m) l[m] := by
  induction l generalizing acc t m with
  | nil => simp at hm
  | cons i is ih =>
    rw [List.nodup_cons] at hl
    cases m with
    | zero =>
      simp only [List.getElem_cons_zero, fillSeq, Nat.add_zero]
      rw [fillSeq_not_mem adv is _ _ i hl.1]
      simp
    | succ m =>
      simp only [List.getElem_cons_succ, fillSeq]
      rw [ih hl.2 _ (t + 1) m (by simp at hm; omega)]
      congr 1
      omega

/-- The byte-by-byte copy reads address `j` at time `j`: the copied region is the diagonal
`fun j => adv j.val j`. -/
theorem fillSeq_finRange (adv : Adversary n) (acc : Region n) :
    fillSeq adv (List.finRange n) acc 0 = fun j => adv j.val j := by
  funext j
  have hj : j.val < (List.finRange n).length := by simp
  have he : (List.finRange n)[j.val] = j := by simp
  have := fillSeq_getElem adv (List.finRange n) (List.nodup_finRange n) acc 0 j.val hj
  rw [he, Nat.zero_add] at this
  exact this

theorem readSeq_singleReadFrom (l : List (Fin n)) (hl : l.Nodup) (acc : Region n)
    (k : Region n → Prog n α) (vis : Fin n → Bool) (hvis : ∀ i ∈ l, vis i = false)
    (hk : ∀ acc' (vis' : Fin n → Bool), (k acc').SingleReadFrom vis') :
    (readSeq l acc k).SingleReadFrom vis := by
  induction l generalizing acc vis with
  | nil => exact hk acc vis
  | cons i is ih =>
    rw [List.nodup_cons] at hl
    refine ⟨hvis i (by simp), fun b => ?_⟩
    apply ih hl.2
    intro j hj
    have hji : j ≠ i := fun h => hl.1 (h ▸ hj)
    simp [hji, hvis j (by simp [hj])]

end ReadSeq

end Toy.DoubleFetch
