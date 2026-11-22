import ToyLoanFlow.Analyses

/-!
# Certificates

Checkable witnesses for the negative facts that concrete theorems need: a list closed under
the rules of an inductive predicate contains every instance of it. Each `…Closed` function is
a `Bool` test, and each `mem_of_…` theorem turns a passing test into an over-approximation.
-/

namespace Toy.LoanFlow

variable {n m : Nat}

/-! ## Liveness -/

/-- `L` is closed under the rules of `LiveAt`. -/
def liveClosed (p : Prog n m) (L : List (Fin m × Fin n)) : Bool :=
  (List.finRange n).all fun q =>
    (p.stmt q).uses.all (fun v => L.contains (v, q)) &&
    (List.finRange m).all fun v =>
      (p.stmt q).defs.contains v || (p.succ q).all fun q' => !L.contains (v, q') || L.contains (v, q)

theorem mem_of_liveAt {p : Prog n m} {L : List (Fin m × Fin n)} (hL : liveClosed p L = true)
    {v : Fin m} {q : Fin n} (h : LiveAt p v q) : (v, q) ∈ L := by
  induction h with
  | @use q hu =>
    have := List.all_eq_true.1 hL q (List.mem_finRange q)
    simp only [Bool.and_eq_true, List.all_eq_true] at this
    simpa using this.1 _ hu
  | @step q q' hd hs _ ih =>
    have := List.all_eq_true.1 hL q (List.mem_finRange q)
    simp only [Bool.and_eq_true, List.all_eq_true] at this
    have h2 := this.2 v (List.mem_finRange v)
    simp only [Bool.or_eq_true, List.all_eq_true] at h2
    rcases h2 with h2 | h2
    · exact absurd (by simpa using h2) hd
    · have := h2 q' hs
      simp only [Bool.not_eq_true', List.contains_eq_mem] at this
      rcases this with h3 | h3
      · simp at h3; exact absurd ih h3
      · simpa using h3

/-! ## Reachability -/

/-- `R` is closed under the rules of `Reach`. -/
def reachClosed (E : Edges n) (R : List (Fin n × Fin n)) : Bool :=
  (List.finRange n).all fun u =>
    R.contains (u, u) &&
    (E u).all fun v => (List.finRange n).all fun w => !R.contains (v, w) || R.contains (u, w)

theorem mem_of_reach {E : Edges n} {R : List (Fin n × Fin n)} (hR : reachClosed E R = true)
    {u w : Fin n} (h : Reach E u w) : (u, w) ∈ R := by
  induction h with
  | refl u =>
    have := List.all_eq_true.1 hR u (List.mem_finRange u)
    simp only [Bool.and_eq_true] at this
    simpa using this.1
  | @step u v w hv _ ih =>
    have := List.all_eq_true.1 hR u (List.mem_finRange u)
    simp only [Bool.and_eq_true, List.all_eq_true] at this
    have := this.2 v hv w (List.mem_finRange w)
    simp only [Bool.or_eq_true, Bool.not_eq_true', List.contains_eq_mem] at this
    rcases this with h3 | h3
    · simp at h3; exact absurd ih h3
    · simpa using h3

/-! ## Location-sensitive loan flow -/

/-- `T` is closed under the rules of `LS.SubAt vm p`, given an over-approximation `L` of
liveness. -/
def subClosed (vm : VarMode) (p : Prog n m) (L : List (Fin m × Fin n))
    (T : List (Origin m × Origin m × Fin n)) : Bool :=
  ((List.finRange n).all fun q => (gen vm p q).all fun pr => T.contains (pr.1, pr.2, q)) &&
  T.all fun ⟨o₁, o₂, q⟩ =>
    ((p.succ q).all fun q' =>
      !(L.contains (o₁.1, q') && L.contains (o₂.1, q')) || T.contains (o₁, o₂, q')) &&
    T.all fun ⟨a, b, q2⟩ => !(q2 == q && a == o₂) || T.contains (o₁, b, q)

theorem mem_of_subAt {vm : VarMode} {p : Prog n m} {L : List (Fin m × Fin n)}
    {T : List (Origin m × Origin m × Fin n)} (hL : liveClosed p L = true)
    (hT : subClosed vm p L T = true) {o₁ o₂ : Origin m} {q : Fin n}
    (h : LS.SubAt vm p o₁ o₂ q) : (o₁, o₂, q) ∈ T := by
  simp only [subClosed, Bool.and_eq_true] at hT
  obtain ⟨hB, hT⟩ := hT
  induction h with
  | @base o₁ o₂ q hg =>
    simpa using List.all_eq_true.1 (List.all_eq_true.1 hB q (List.mem_finRange q)) _ hg
  | @trans o₁ o₂ o₃ q _ _ ih₁ ih₂ =>
    have := List.all_eq_true.1 hT _ ih₁
    simp only [Bool.and_eq_true, List.all_eq_true] at this
    simpa using this.2 _ ih₂
  | @persist o₁ o₂ q q' _ hq h₁ h₂ ih =>
    have := List.all_eq_true.1 hT _ ih
    simp only [Bool.and_eq_true, List.all_eq_true] at this
    have := this.1 q' hq
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      List.contains_eq_mem, decide_eq_false_iff_not, decide_eq_true_eq] at this
    rcases this with (h3 | h3) | h3
    · exact absurd (mem_of_liveAt hL h₁) h3
    · exact absurd (mem_of_liveAt hL h₂) h3
    · exact h3

/-- `S` is closed under the rules of `LS.Holds km vm p`, with `T` standing for `LS.SubAt`. -/
def lsClosed (km : KillMode) (vm : VarMode) (p : Prog n m)
    (T : List (Origin m × Origin m × Fin n)) (S : List (Fin n × Origin m × Fin n)) : Bool :=
  ((List.finRange n).all fun l =>
    match p.stmt l with
    | .borrow _ d _ => S.contains (l, (d, 0), l)
    | _ => true) &&
  S.all fun ⟨l, o, q⟩ =>
    ((p.succ q).all fun q' =>
      (killsAt km p q' o.1 || S.contains (l, o, q')) &&
      ((p.stmt q').defs.contains o.1 ||
        (gen vm p q').all fun pr => pr.1 != o || S.contains (l, pr.2, q'))) &&
    T.all fun ⟨a, b, q2⟩ => !(q2 == q && a == o) || S.contains (l, b, q)

theorem mem_of_holds {km : KillMode} {vm : VarMode} {p : Prog n m}
    {L : List (Fin m × Fin n)} {T : List (Origin m × Origin m × Fin n)}
    {S : List (Fin n × Origin m × Fin n)} (hL : liveClosed p L = true)
    (hT : subClosed vm p L T = true) (hS : lsClosed km vm p T S = true)
    {l : Fin n} {o : Origin m} {q : Fin n} (h : LS.Holds km vm p l o q) : (l, o, q) ∈ S := by
  simp only [lsClosed, Bool.and_eq_true] at hS
  obtain ⟨hI, hS⟩ := hS
  induction h with
  | @intro mu d s hst =>
    have := List.all_eq_true.1 hI l (List.mem_finRange l)
    rw [hst] at this
    simpa using this
  | @carry o q q' _ hq hk ih =>
    have := List.all_eq_true.1 hS _ ih
    simp only [Bool.and_eq_true, List.all_eq_true] at this
    have := (this.1 q' hq).1
    simp only [Bool.or_eq_true] at this
    rcases this with h1 | h1
    · rw [hk] at h1; exact absurd h1 (by simp)
    · simpa using h1
  | @step o₁ o₂ q q' _ hq hg hd ih =>
    have := List.all_eq_true.1 hS _ ih
    simp only [Bool.and_eq_true, List.all_eq_true] at this
    have := (this.1 q' hq).2
    simp only [Bool.or_eq_true, List.all_eq_true] at this
    rcases this with h1 | h1
    · exact absurd (by simpa using h1) hd
    · simpa using h1 _ hg
  | @sub o₁ o₂ q _ hs ih =>
    have := List.all_eq_true.1 hS _ ih
    simp only [Bool.and_eq_true, List.all_eq_true] at this
    simpa using this.2 _ (mem_of_subAt hL hT hs)

/-- Certificate for `LS.Accepts km vm p`: `L` closed under liveness, `T` closed under the
subset rules, `S` closed under the loan-flow rules, and no conflict at a successor of a fact of
`S` whose origin's local is in `L` there. -/
def lsCert (km : KillMode) (vm : VarMode) (p : Prog n m) (L : List (Fin m × Fin n))
    (T : List (Origin m × Origin m × Fin n)) (S : List (Fin n × Origin m × Fin n)) : Bool :=
  liveClosed p L && subClosed vm p L T && lsClosed km vm p T S &&
  S.all fun ⟨l, o, q₀⟩ => (p.succ q₀).all fun q =>
    !(decide (Conflicts p l q)) || !L.contains (o.1, q)

theorem ls_accepts_of_cert {km : KillMode} {vm : VarMode} {p : Prog n m}
    (L : List (Fin m × Fin n)) (T : List (Origin m × Origin m × Fin n))
    (S : List (Fin n × Origin m × Fin n))
    (h : lsCert km vm p L T S = true) : LS.Accepts km vm p := by
  simp only [lsCert, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hL, hT⟩, hS⟩, hC⟩ := h
  rintro l q hc ⟨o, q₀, ho, hq, hlv⟩
  have h1 := mem_of_holds hL hT hS ho
  have h2 := mem_of_liveAt hL hlv
  have := List.all_eq_true.1 (List.all_eq_true.1 hC _ h1) q hq
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at this
  rcases this with h3 | h3
  · exact h3 hc
  · simp at h3; exact h3 h2

/-! ## Location-insensitive regions -/

/-- `G` is closed under the rules of `NLL.InRegion vm p`, given an over-approximation `L` of
liveness. -/
def regionClosed (vm : VarMode) (p : Prog n m) (L : List (Fin m × Fin n))
    (G : List (Origin m × Fin n)) : Bool :=
  (L.all fun ⟨v, q⟩ => (List.range (p.ty v).length).all fun k => G.contains ((v, k), q)) &&
  ((List.finRange n).all fun b =>
    (match p.stmt b with
     | .ret v => (List.finRange n).all fun q => G.contains ((v, 0), q)
     | _ => true) &&
    (gen vm p b).all fun pr => (List.finRange n).all fun q =>
      !G.contains (pr.2, q) || G.contains (pr.1, q))

theorem mem_of_inRegion {vm : VarMode} {p : Prog n m} {L : List (Fin m × Fin n)}
    {G : List (Origin m × Fin n)} (hL : liveClosed p L = true) (hG : regionClosed vm p L G = true)
    {o : Origin m} {q : Fin n} (h : NLL.InRegion vm p o q) : (o, q) ∈ G := by
  simp only [regionClosed, Bool.and_eq_true] at hG
  obtain ⟨hG1, hG2⟩ := hG
  induction h with
  | @live v k q hl hk =>
    have := List.all_eq_true.1 hG1 _ (mem_of_liveAt hL hl)
    simpa using List.all_eq_true.1 this k (List.mem_range.2 hk)
  | @outlives o₁ o₂ b q hg _ ih =>
    have := List.all_eq_true.1 hG2 b (List.mem_finRange b)
    simp only [Bool.and_eq_true, List.all_eq_true] at this
    have := this.2 _ hg q (List.mem_finRange q)
    simp only [Bool.or_eq_true, Bool.not_eq_true', List.contains_eq_mem] at this
    rcases this with h3 | h3
    · simp at h3; exact absurd ih h3
    · simpa using h3
  | @universal v b q hb =>
    have := List.all_eq_true.1 hG2 b (List.mem_finRange b)
    simp only [Bool.and_eq_true] at this
    have := this.1
    rw [hb] at this
    simpa using List.all_eq_true.1 this q (List.mem_finRange q)

/-- `W` is closed under the rules of `NLL.InScope vm p`, with `G` standing for regions. -/
def scopeClosed (p : Prog n m) (G : List (Origin m × Fin n)) (W : List (Fin n × Fin n)) : Bool :=
  (List.finRange n).all fun l =>
    match loanDst p l with
    | none => true
    | some d =>
      ((p.succ l).all fun q => !G.contains ((d, 0), q) || W.contains (l, q)) &&
      (List.finRange n).all fun q => !W.contains (l, q) ||
        (p.succ q).all fun q' => !G.contains ((d, 0), q') || W.contains (l, q')

theorem mem_of_inScope {vm : VarMode} {p : Prog n m} {L : List (Fin m × Fin n)}
    {G : List (Origin m × Fin n)} {W : List (Fin n × Fin n)} (hL : liveClosed p L = true)
    (hG : regionClosed vm p L G = true) (hW : scopeClosed p G W = true)
    {l q : Fin n} (h : NLL.InScope vm p l q) : (l, q) ∈ W := by
  induction h with
  | @first d q hd hq hr =>
    have := List.all_eq_true.1 hW l (List.mem_finRange l)
    rw [hd] at this
    simp only [Bool.and_eq_true, List.all_eq_true] at this
    have := this.1 q hq
    simp only [Bool.or_eq_true, Bool.not_eq_true', List.contains_eq_mem] at this
    rcases this with h3 | h3
    · simp at h3; exact absurd (mem_of_inRegion hL hG hr) h3
    · simpa using h3
  | @next d q q' hd _ hq hr ih =>
    have := List.all_eq_true.1 hW l (List.mem_finRange l)
    rw [hd] at this
    simp only [Bool.and_eq_true, List.all_eq_true] at this
    have := this.2 q (List.mem_finRange q)
    simp only [Bool.or_eq_true, Bool.not_eq_true', List.contains_eq_mem, List.all_eq_true] at this
    rcases this with h3 | h3
    · simp at h3; exact absurd ih h3
    · have := h3 q' hq
      rcases this with h4 | h4
      · simp at h4; exact absurd (mem_of_inRegion hL hG hr) h4
      · simpa using h4

/-- Certificate for `NLL.Accepts vm p`. -/
def nllCert (vm : VarMode) (p : Prog n m) (L : List (Fin m × Fin n))
    (G : List (Origin m × Fin n)) (W : List (Fin n × Fin n)) : Bool :=
  liveClosed p L && regionClosed vm p L G && scopeClosed p G W &&
  W.all fun ⟨l, q⟩ => !(decide (Conflicts p l q))

theorem nll_accepts_of_cert {vm : VarMode} {p : Prog n m} (L : List (Fin m × Fin n))
    (G : List (Origin m × Fin n)) (W : List (Fin n × Fin n))
    (h : nllCert vm p L G W = true) : NLL.Accepts vm p := by
  simp only [nllCert, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hL, hG⟩, hW⟩, hC⟩ := h
  intro l q hc hs
  have := List.all_eq_true.1 hC _ (mem_of_inScope hL hG hW hs)
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at this
  exact this hc

end Toy.LoanFlow

namespace Toy.LoanFlow

variable {n m : Nat}

/-! ## Safety certificates (inductive invariants over node × state) -/

/-- `certOK p S`: every pair `(x, σ)` in `S` executes without UB, and for every `.ok` step from
such a pair, the pair of each successor and the new state is again in `S`. -/
def certOK (p : Prog n m) (S : List (Fin n × RState n m)) : Bool :=
  S.all fun x =>
    match exec p x.1 x.2 with
    | .ok σ' => (p.succ x.1).all fun y => S.contains (y, σ')
    | .halt => true
    | .ub => false

theorem run_ne_ub_of_cert {p : Prog n m} {S : List (Fin n × RState n m)}
    (hS : certOK p S = true) :
    ∀ (π : List (Fin n)) (x : Fin n) (σ : RState n m), IsWalk p.succ (x :: π) → (x, σ) ∈ S →
      (run p σ (x :: π)).isUB = false := by
  intro π
  induction π with
  | nil =>
    intro x σ _ hx
    have h := List.all_eq_true.1 hS _ hx
    simp only [run]
    revert h
    cases exec p x σ <;> simp [Outcome.isUB]
  | cons y t ih =>
    intro x σ hw hx
    have h := List.all_eq_true.1 hS _ hx
    simp only [run]
    revert h
    cases hex : exec p x σ with
    | ok σ' =>
      intro h
      simp only at h
      have hy : (y, σ') ∈ S := by
        have := List.all_eq_true.1 h y hw.1
        simpa using this
      exact ih y σ' hw.2 hy
    | halt => simp [Outcome.isUB]
    | ub => simp

/-- A certificate containing `(entry, init)` proves safety. -/
theorem safe_of_cert {p : Prog n m} (S : List (Fin n × RState n m)) (hS : certOK p S = true)
    (hinit : (p.entry, RState.init) ∈ S) : Safe p := by
  intro π hw hh
  cases π with
  | nil => exact absurd hw (fun h => h)
  | cons x t =>
    simp at hh; subst hh
    exact run_ne_ub_of_cert hS t p.entry RState.init hw hinit

end Toy.LoanFlow
