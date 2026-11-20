/-
Toy.SCT.Soundness
=================

Proof that the closure criterion implies size-change termination (the direction of Lee, Jones and
Ben-Amram's Theorem 4 that uses Ramsey's theorem): colour each pair of positions `m < n` of an
infinite call path by the composite of the graphs between them; a homogeneous infinite set of
positions yields an idempotent loop graph of the closure, whose strict self-arc is repeated into
an infinitely descending thread.
-/
import Toy.SCT.Threads
import Toy.SCT.Enum
import Toy.SCT.Ramsey

namespace Toy.SCT

variable {nf k : Nat}

/-- The composite of the `d + 1` graphs `Gs a, …, Gs (a + d)` (composed left to right). -/
def segComp (Gs : Nat → SCG nf k) (a : Nat) : Nat → SCG nf k
  | 0 => Gs a
  | d + 1 => (segComp Gs a d).comp (Gs (a + d + 1))

theorem segComp_ok (Gs : Nat → SCG nf k) (a : Nat) :
    ∀ (d : Nat) (q j : Fin k) (b : Bool),
      ((segComp Gs a d).lab q j).Ok b ↔ SegThread Gs a (d + 1) q j b := by
  intro d
  induction d with
  | zero => intro q j b; exact (segThread_one Gs a q j b).symm
  | succ d ih =>
    intro q j b
    show ((segComp Gs a d).comp (Gs (a + d + 1)) |>.lab q j).Ok b ↔ _
    rw [SCG.comp_ok', segThread_append Gs (d + 1) a 1]
    constructor
    · rintro ⟨l, b1, b2, h1, h2, rfl⟩
      refine ⟨l, b1, b2, (ih q l b1).mp h1, ?_, rfl⟩
      rw [segThread_one, show a + (d + 1) = a + d + 1 by omega]
      exact h2
    · rintro ⟨l, b1, b2, h1, h2, rfl⟩
      refine ⟨l, b1, b2, (ih q l b1).mpr h1, ?_, rfl⟩
      rw [segThread_one, show a + (d + 1) = a + d + 1 by omega] at h2
      exact h2

theorem segComp_src (Gs : Nat → SCG nf k) (a : Nat) :
    ∀ d, (segComp Gs a d).src = (Gs a).src
  | 0 => rfl
  | d + 1 => segComp_src Gs a d

theorem segComp_dst (Gs : Nat → SCG nf k) (a : Nat) :
    ∀ d, (segComp Gs a d).dst = (Gs (a + d)).dst
  | 0 => rfl
  | _ + 1 => rfl

theorem segComp_inClosure {P : Prog nf k} {Gs : Nat → SCG nf k} (hpath : IsCallPath P Gs)
    (a : Nat) : ∀ d, InClosure P (segComp Gs a d)
  | 0 => .gen (hpath a).1
  | d + 1 => .comp (segComp_inClosure hpath a d) (.gen (hpath (a + d + 1)).1)
      (by rw [segComp_dst]; exact (hpath (a + d)).2)

/-- Gluing infinitely many strict threads from `q` back to `q`, one on each block
`[h n, h (n + 1))` of a strictly increasing sequence of positions, gives an infinitely descending
thread. -/
theorem hasInfDescThread_of_blocks (Gs : Nat → SCG nf k) (h : Nat → Nat)
    (hmono : ∀ m n, m < n → h m < h n) (q : Fin k)
    (hseg : ∀ n, SegThread Gs (h n) (h (n + 1) - h n) q q true) : HasInfDescThread Gs := by
  have hlt : ∀ n, h n < h (n + 1) := fun n => hmono n (n + 1) (Nat.lt_succ_self n)
  have hge : ∀ n, n ≤ h n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => have := hlt n; omega
  -- the block containing each position `t ≥ h 0`
  have hex : ∀ t, h 0 ≤ t → ∃ n, h n ≤ t ∧ t < h (n + 1) := by
    intro t
    induction t with
    | zero => intro h0; exact ⟨0, h0, by have := hlt 0; omega⟩
    | succ t ih =>
      intro ht
      by_cases h0 : h 0 ≤ t
      · obtain ⟨n, h1, h2⟩ := ih h0
        by_cases h3 : t + 1 < h (n + 1)
        · exact ⟨n, by omega, h3⟩
        · exact ⟨n + 1, by omega, by have := hlt (n + 1); omega⟩
      · exact ⟨0, ht, by have := hlt 0; omega⟩
  have hmono_le : ∀ m n, m ≤ n → h m ≤ h n := by
    intro m n hmn
    rcases Nat.lt_or_eq_of_le hmn with h' | h'
    · exact Nat.le_of_lt (hmono _ _ h')
    · rw [h']; exact Nat.le_refl _
  have huniq : ∀ t n n', h n ≤ t → t < h (n + 1) → h n' ≤ t → t < h (n' + 1) → n = n' := by
    intro t n n' h1 h2 h3 h4
    rcases Nat.lt_trichotomy n n' with hn | hn | hn
    · have := hmono_le (n + 1) n' hn
      omega
    · exact hn
    · have := hmono_le (n' + 1) n hn
      omega
  -- one thread per block
  have hfun : ∀ n, ∃ pn : Nat → Fin k, pn (h n) = q ∧ pn (h (n + 1)) = q ∧
      (∀ t, h n ≤ t → t < h (n + 1) → (Gs t).lab (pn t) (pn (t + 1)) ≠ Label.absent) ∧
      (∃ t, h n ≤ t ∧ t < h (n + 1) ∧ (Gs t).lab (pn t) (pn (t + 1)) = Label.strict) := by
    intro n
    obtain ⟨pn, h1, h2, h3, h4⟩ := segThread_to_fun Gs _ _ _ _ _ (hseg n)
    have e : h n + (h (n + 1) - h n) = h (n + 1) := by have := hlt n; omega
    rw [e] at h2 h3 h4
    exact ⟨pn, h1, h2, h3, h4 rfl⟩
  let pb : Nat → Nat → Fin k := fun n => Classical.choose (hfun n)
  have hpb : ∀ n, pb n (h n) = q ∧ pb n (h (n + 1)) = q ∧
      (∀ t, h n ≤ t → t < h (n + 1) → (Gs t).lab (pb n t) (pb n (t + 1)) ≠ Label.absent) ∧
      (∃ t, h n ≤ t ∧ t < h (n + 1) ∧ (Gs t).lab (pb n t) (pb n (t + 1)) = Label.strict) :=
    fun n => Classical.choose_spec (hfun n)
  let blk : Nat → Nat := fun t => if ht : h 0 ≤ t then Classical.choose (hex t ht) else 0
  have hblk : ∀ t, h 0 ≤ t → h (blk t) ≤ t ∧ t < h (blk t + 1) := by
    intro t ht
    simp only [blk, dite_eq_left ht]
    exact Classical.choose_spec (hex t ht)
  have hblk_eq : ∀ t n, h n ≤ t → t < h (n + 1) → blk t = n := by
    intro t n h1 h2
    have ht : h 0 ≤ t := by
      have := hmono_le 0 n (Nat.zero_le _)
      omega
    exact huniq t _ _ (hblk t ht).1 (hblk t ht).2 h1 h2
  let p : Nat → Fin k := fun t => pb (blk t) t
  -- along block `n`, the glued thread follows the thread of block `n`, including its endpoint
  have hfollow : ∀ n t, h n ≤ t → t < h (n + 1) → p t = pb n t ∧ p (t + 1) = pb n (t + 1) := by
    intro n t h1 h2
    refine ⟨by simp only [p, hblk_eq t n h1 h2], ?_⟩
    by_cases h3 : t + 1 < h (n + 1)
    · simp only [p, hblk_eq (t + 1) n (by omega) h3]
    · have e : t + 1 = h (n + 1) := by omega
      have hb : blk (t + 1) = n + 1 := hblk_eq (t + 1) (n + 1) (by omega) (by rw [e]; exact hlt _)
      simp only [p, hb]
      rw [e, (hpb (n + 1)).1, (hpb n).2.1]
  refine ⟨h 0, p, fun t ht => ?_, fun N => ?_⟩
  · obtain ⟨h1, h2⟩ := hblk t ht
    obtain ⟨e1, e2⟩ := hfollow (blk t) t h1 h2
    rw [e1, e2]
    exact (hpb (blk t)).2.2.1 t h1 h2
  · obtain ⟨t, h1, h2, hs⟩ := (hpb N).2.2.2
    obtain ⟨e1, e2⟩ := hfollow N t h1 h2
    have h0N : h 0 ≤ h N := hmono_le 0 N (Nat.zero_le _)
    refine ⟨t, by have := hge N; omega, by omega, ?_⟩
    rw [e1, e2]
    exact hs

/-- **The closure criterion implies size-change termination.** -/
theorem sizeChangeTerminating_of_closureCriterion_proof (P : Prog nf k)
    (hcc : ClosureCriterion P) : SizeChangeTerminating P := by
  intro Gs hpath
  let col : Nat → Nat → SCG nf k := fun m n => segComp Gs m (n - m - 1)
  obtain ⟨h, hmono, A, hA⟩ :=
    RamseyProof.ramsey (allSCG nf k) col (fun _ _ _ => mem_allSCG _)
  have hsem : ∀ m n, m < n → ∀ q j b,
      (A.lab q j).Ok b ↔ SegThread Gs (h m) (h n - h m) q j b := by
    intro m n hmn q j b
    rw [← hA m n hmn]
    have hlt := hmono m n hmn
    have := segComp_ok Gs (h m) (h n - h m - 1) q j b
    rwa [show h n - h m - 1 + 1 = h n - h m by omega] at this
  have hsrc : A.src = (Gs (h 1)).src := by
    rw [← hA 1 2 (by omega)]
    exact segComp_src Gs _ _
  have hdst : A.dst = (Gs (h 1)).src := by
    rw [← hA 0 1 (by omega)]
    have hlt := hmono 0 1 (by omega)
    show (segComp Gs (h 0) (h 1 - h 0 - 1)).dst = _
    rw [segComp_dst, show h 0 + (h 1 - h 0 - 1) = h 1 - 1 by omega]
    have := (hpath (h 1 - 1)).2
    rwa [show h 1 - 1 + 1 = h 1 by omega] at this
  have hloop : A.src = A.dst := hsrc.trans hdst.symm
  have h01 := hmono 0 1 (by omega)
  have h12 := hmono 1 2 (by omega)
  have hidem : A.comp A = A := by
    refine SCG.ext_iff'.mpr ⟨rfl, rfl, fun q j => Label.eq_of_ok_iff fun b => ?_⟩
    rw [SCG.comp_ok', hsem 0 2 (by omega),
      show h 2 - h 0 = (h 1 - h 0) + (h 2 - h 1) by omega, segThread_append,
      show h 0 + (h 1 - h 0) = h 1 by omega]
    constructor
    · rintro ⟨l, b1, b2, e1, e2, rfl⟩
      exact ⟨l, b1, b2, (hsem 0 1 (by omega) q l b1).mp e1, (hsem 1 2 (by omega) l j b2).mp e2, rfl⟩
    · rintro ⟨l, b1, b2, e1, e2, rfl⟩
      exact ⟨l, b1, b2, (hsem 0 1 (by omega) q l b1).mpr e1, (hsem 1 2 (by omega) l j b2).mpr e2,
        rfl⟩
  have hinc : InClosure P A := by
    rw [← hA 0 1 (by omega)]
    exact segComp_inClosure hpath _ _
  obtain ⟨q, hq⟩ := hcc A hinc hloop hidem
  refine hasInfDescThread_of_blocks Gs h hmono q fun n => ?_
  exact (hsem n (n + 1) (Nat.lt_succ_self n) q q true).mp ((Label.ok_true _).mpr hq)

/-! ### Soundness of size-change termination over `Nat` -/

/-- A non-increasing sequence of naturals cannot drop strictly infinitely often. -/
theorem nat_no_inf_weak_descent (m : Nat → Nat) (hle : ∀ n, m (n + 1) ≤ m n)
    (hlt : ∀ N, ∃ n, N ≤ n ∧ m (n + 1) < m n) : False := by
  have hmono : ∀ a b, a ≤ b → m b ≤ m a := by
    intro a b hab
    induction hab with
    | refl => exact Nat.le_refl _
    | step _ ih => exact Nat.le_trans (hle _) ih
  have step : ∀ c, ∃ n, m n + c ≤ m 0 := by
    intro c
    induction c with
    | zero => exact ⟨0, by simp⟩
    | succ c ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨n', hnn', hdrop⟩ := hlt n
      have hle' := hmono n n' hnn'
      exact ⟨n' + 1, by omega⟩
  obtain ⟨n, hn⟩ := step (m 0 + 1)
  omega

/-- **Size-change termination is sound over `Nat`**: following an infinitely descending thread
through the values of a consistent run gives a non-increasing sequence of naturals with infinitely
many strict drops. -/
theorem no_consistent_nat_run_of_sizeChangeTerminating_proof (P : Prog nf k)
    (h : SizeChangeTerminating P) : ¬ ConsistentRunIn Nat P := by
  rintro ⟨fs, vs, Gs, hrun⟩
  have hpath : IsCallPath P Gs :=
    fun n => ⟨(hrun n).1, (hrun n).2.2.1.trans (hrun (n + 1)).2.1.symm⟩
  obtain ⟨n0, p, hpres, hstr⟩ := h Gs hpath
  apply nat_no_inf_weak_descent (fun t => vs (n0 + t) (p (n0 + t)))
  · intro t
    have hlab := hpres (n0 + t) (by omega)
    have hres := (hrun (n0 + t)).2.2.2 (p (n0 + t)) (p (n0 + t + 1))
    show vs (n0 + (t + 1)) (p (n0 + (t + 1))) ≤ vs (n0 + t) (p (n0 + t))
    rw [show n0 + (t + 1) = n0 + t + 1 by omega]
    cases hl : (Gs (n0 + t)).lab (p (n0 + t)) (p (n0 + t + 1)) with
    | absent => exact absurd hl hlab
    | nonstrict => exact hres.2 hl
    | strict => exact Nat.le_of_lt (hres.1 hl)
  · intro N
    obtain ⟨n, hNn, hn0, hl⟩ := hstr (n0 + N)
    refine ⟨n - n0, by omega, ?_⟩
    have hlt := ((hrun n).2.2.2 (p n) (p (n + 1))).1 hl
    show vs (n0 + (n - n0 + 1)) (p (n0 + (n - n0 + 1))) < vs (n0 + (n - n0)) (p (n0 + (n - n0)))
    rw [show n0 + (n - n0) = n by omega, show n0 + (n - n0 + 1) = n + 1 by omega]
    exact hlt

end Toy.SCT
