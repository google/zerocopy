import ToyLayoutDfa.Tools

/-!
# Proof lemmas for the main results

Fully proved helper lemmas: path concatenation and splitting, facts about `fit`, the
invariants behind soundness and completeness of the two checks for an arbitrary step
budget, and the bound "an accepted word of a layout without cycles through its reachable live
part is no longer than its edge list" that connects the budget `fuelFor` to
`ReachableLiveAcyclic`, which both `FixedSize` and `Acyclic` imply.
None of these is a result of the package; the step-budget lemmas
(`forallAux_complete_fit_of_lt_fuel`, `existsAux_start_of_lang_fit_of_lt_fuel`) are quoted in the report
because they separate the role of the budget from the role of the size hypotheses.
-/

namespace Toy.LayoutDfa
namespace Layout

theorem path_trans {A : Layout} {q1 q2 q3 : Nat} {u v : List Sym}
    (h1 : A.Path q1 u q2) (h2 : A.Path q2 v q3) : A.Path q1 (u ++ v) q3 := by
  induction h1 with
  | nil _ => exact h2
  | cons hq he _ ih => exact Path.cons hq he (ih h2)

theorem path_split {A : Layout} :
    ∀ {q : Nat} {u v : List Sym} {r : Nat}, A.Path q (u ++ v) r → ∃ m, A.Path q u m ∧ A.Path m v r
  | q, [], v, r, h => ⟨q, Path.nil _, h⟩
  | q, a :: u, v, r, h => by
    obtain ⟨hq, q', he, hp⟩ := path_cons_iff.mp h
    obtain ⟨m, h1, h2⟩ := path_split hp
    exact ⟨m, Path.cons hq he h1, h2⟩

/-- A run from the accept state reads nothing (the accept state is terminal). -/
theorem path_from_accept {A : Layout} {w : List Sym} {r : Nat}
    (h : A.Path A.accept w r) : w = [] ∧ r = A.accept := by
  cases w with
  | nil => exact ⟨rfl, (path_nil_iff.mp h).symm⟩
  | cons a w => exact absurd rfl (path_cons_iff.mp h).1

/-- `ReachableLive` implies that the language is non-empty (take the empty run to the
start state). -/
theorem inhabited_of_reachableLive {A : Layout} (h : A.ReachableLive) : ∃ s, A.Lang s :=
  h [] A.start (Path.nil _)

theorem reachableDeterministic_of_deterministic {A : Layout} (h : A.Deterministic) :
    A.ReachableDeterministic :=
  fun _ _ _ _ e₁ he₁ e₂ he₂ hq₁ hq₂ hlbl => h e₁ he₁ e₂ he₂ (hq₁.trans hq₂.symm) hlbl

theorem path_det_from_reachable {B : Layout} (hdet : B.ReachableDeterministic) :
    ∀ {u : List Sym} {p : List Sym} {q r1 r2 : Nat},
      B.Path B.start p q → B.Path q u r1 → B.Path q u r2 → r1 = r2
  | [], _, _, _, _, _, h1, h2 => by
    rw [path_nil_iff] at h1 h2
    exact h1.symm.trans h2
  | a :: u, p, q, r1, r2, hreach, h1, h2 => by
    obtain ⟨hne, q1, he1, hp1⟩ := path_cons_iff.mp h1
    obtain ⟨_, q2, he2, hp2⟩ := path_cons_iff.mp h2
    have hq : q1 = q2 := hdet p q hreach hne (q, a, q1) he1 (q, a, q2) he2 rfl rfl rfl
    subst hq
    exact path_det_from_reachable hdet (path_trans hreach (Path.cons hne he1 (Path.nil _))) hp1 hp2

theorem path_det_start {B : Layout} (hdet : B.ReachableDeterministic)
    {u : List Sym} {r1 r2 : Nat} (h1 : B.Path B.start u r1) (h2 : B.Path B.start u r2) :
    r1 = r2 :=
  path_det_from_reachable hdet (Path.nil B.start) h1 h2

end Layout

open Layout

/-! ### `fit` -/

theorem length_fit (n : Nat) (s : List Sym) : (fit n s).length = n := by
  simp only [fit, List.length_append, List.length_take, List.length_replicate]
  omega

theorem fit_zero (s : List Sym) : fit 0 s = [] := by
  simp [fit]

theorem fit_cons (n : Nat) (a : Sym) (s : List Sym) : fit (n + 1) (a :: s) = a :: fit n s := by
  simp [fit]

theorem fit_nil_succ (n : Nat) : fit (n + 1) [] = Sym.uninit :: fit n [] := by
  simp [fit, List.replicate_succ]

theorem fit_of_length_le {n : Nat} {s : List Sym} (h : s.length ≤ n) :
    fit n s = s ++ List.replicate (n - s.length) Sym.uninit := by
  simp [fit, List.take_of_length_le h]

theorem fit_of_length_eq {n : Nat} {s : List Sym} (h : s.length = n) : fit n s = s := by
  rw [fit_of_length_le (Nat.le_of_eq h)]
  simp [h]

/-! ### Soundness invariants (any step budget) -/

/-- Whenever the universal exploration succeeds from `(qa, qb)`, every word the source
accepts from `qa` has some destination-size view accepted from `qb`. -/
theorem forallAux_sound {A B : Layout} :
    ∀ (fuel qa qb : Nat), forallAux A B fuel qa qb = true →
      ∀ v, A.Accepts qa v → ∃ k, B.Accepts qb (fit k v)
  | 0, _, _, h, _, _ => by simp [forallAux] at h
  | fuel + 1, qa, qb, h, v, hv => by
    unfold forallAux at h
    by_cases hqb : qb = B.accept
    · exact ⟨0, by rw [fit_zero, hqb]; exact Path.nil _⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hqb)] at h
      by_cases hqa : qa = A.accept
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hqa)] at h
        subst hqa
        obtain ⟨hv0, _⟩ := path_from_accept hv
        subst hv0
        simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨s, q'⟩, hmem, hs, h'⟩ := h
        simp only at hs
        subst hs
        obtain ⟨k, hk⟩ := forallAux_sound fuel A.accept q' h' [] (Path.nil _)
        exact ⟨k + 1, by rw [fit_nil_succ]; exact Path.cons hqb (mem_out.mp hmem) hk⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hqa)] at h
        cases v with
        | nil => exact absurd (path_nil_iff.mp hv) hqa
        | cons a v' =>
          obtain ⟨_, qa', hea, hv'⟩ := path_cons_iff.mp hv
          simp only [List.all_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨⟨b, qb'⟩, hmb, hba, h'⟩ := h (a, qa') (mem_out.mpr hea)
          simp only at hba
          subst hba
          obtain ⟨k, hk⟩ := forallAux_sound fuel qa' qb' h' v' hv'
          exact ⟨k + 1, by rw [fit_cons]; exact Path.cons hqb (mem_out.mp hmb) hk⟩

/-- Whenever the existential exploration succeeds from `(qa, qb)` and `qa` is reachable in
a `ReachableLive` source, some word the source accepts from `qa` has some destination-size
view accepted from `qb`. -/
theorem existsAux_sound {A B : Layout} (hlive : A.ReachableLive) :
    ∀ (fuel qa qb : Nat) (u : List Sym), A.Path A.start u qa →
      existsAux A B fuel qa qb = true → ∃ v k, A.Accepts qa v ∧ B.Accepts qb (fit k v)
  | 0, _, _, _, _, h => by simp [existsAux] at h
  | fuel + 1, qa, qb, u, hu, h => by
    unfold existsAux at h
    by_cases hqb : qb = B.accept
    · obtain ⟨v, hv⟩ := hlive u qa hu
      exact ⟨v, 0, hv, by rw [fit_zero, hqb]; exact Path.nil _⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hqb)] at h
      by_cases hqa : qa = A.accept
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hqa)] at h
        subst hqa
        simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨s, q'⟩, hmem, hs, h'⟩ := h
        simp only at hs
        subst hs
        obtain ⟨v, k, hv, hk⟩ := existsAux_sound hlive fuel A.accept q' u hu h'
        obtain ⟨hv0, _⟩ := path_from_accept hv
        subst hv0
        exact ⟨[], k + 1, hv, by rw [fit_nil_succ]; exact Path.cons hqb (mem_out.mp hmem) hk⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hqa)] at h
        simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨a, qa'⟩, hma, ⟨b, qb'⟩, hmb, hba, h'⟩ := h
        simp only at hba
        subst hba
        have hu' : A.Path A.start (u ++ [b]) qa' :=
          path_trans hu (Path.cons hqa (mem_out.mp hma) (Path.nil _))
        obtain ⟨v, k, hv, hk⟩ := existsAux_sound hlive fuel qa' qb' (u ++ [b]) hu' h'
        exact ⟨b :: v, k + 1, Path.cons hqa (mem_out.mp hma) hv,
          by rw [fit_cons]; exact Path.cons hqb (mem_out.mp hmb) hk⟩

/-! ### Completeness invariants (any step budget) -/

theorem forallAux_uninit_tail {A B : Layout} :
    ∀ (r q f : Nat), B.Path q (List.replicate r Sym.uninit) B.accept →
      r + 1 ≤ f → forallAux A B f A.accept q = true
  | 0, q, f, hp, hf => by
    cases f with
    | zero => omega
    | succ f =>
      have hq := path_nil_iff.mp hp
      simp [forallAux, hq]
  | r + 1, q, f, hp, hf => by
    cases f with
    | zero => omega
    | succ f =>
      obtain ⟨hq, q', he', hp''⟩ := path_cons_iff.mp hp
      unfold forallAux
      simp only [hq, ite_false, ite_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
      exact ⟨(Sym.uninit, q'), mem_out.mpr he', rfl, forallAux_uninit_tail r q' f hp'' (by omega)⟩

theorem forallAux_complete_aux {A B : Layout} {nB : Nat}
    (hdet : B.ReachableDeterministic) (hlive : A.ReachableLive) (hfit : FitSubset A B nB) :
    ∀ (k fuel qa qb : Nat) (u : List Sym), u.length + k = nB → k + 1 ≤ fuel →
      A.Path A.start u qa → B.Path B.start u qb →
      forallAux A B fuel qa qb = true
  | 0, fuel, qa, qb, u, hlen, hfuel, hpa, hpb => by
    cases fuel with
    | zero => omega
    | succ fuel =>
      obtain ⟨v, hv⟩ := hlive u qa hpa
      have hbl : B.Lang (fit nB (u ++ v)) := hfit (u ++ v) (path_trans hpa hv)
      have hfit_eq : fit nB (u ++ v) = u := by
        have hu : u.length = nB := by omega
        simp [fit, hu]
      rw [hfit_eq] at hbl
      have hqb : qb = B.accept := path_det_start hdet hpb hbl
      simp [forallAux, hqb]
  | k + 1, fuel, qa, qb, u, hlen, hfuel, hpa, hpb => by
    cases fuel with
    | zero => omega
    | succ fuel =>
      unfold forallAux
      split
      · rfl
      · rename_i hqb
        split
        · rename_i hqa
          subst hqa
          have hbl : B.Lang (fit nB u) := hfit u hpa
          have hfit_eq : fit nB u = u ++ List.replicate (k + 1) Sym.uninit := by
            have hu : u.length ≤ nB := by omega
            have hsub : nB - u.length = k + 1 := by omega
            simp [fit, List.take_of_length_le hu, hsub]
          rw [hfit_eq] at hbl
          obtain ⟨m, hpm, htail⟩ := path_split hbl
          have hm : m = qb := path_det_start hdet hpm hpb
          subst hm
          simp only [List.replicate_succ] at htail
          obtain ⟨_, qb', he, hp'⟩ := path_cons_iff.mp htail
          simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
          exact ⟨(Sym.uninit, qb'), mem_out.mpr he, rfl,
            forallAux_uninit_tail k qb' fuel hp' (by omega)⟩
        · rename_i hqa
          simp only [List.all_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
          rintro ⟨a, qa'⟩ hma
          have hpa' : A.Path A.start (u ++ [a]) qa' :=
            path_trans hpa (Path.cons hqa (mem_out.mp hma) (Path.nil _))
          obtain ⟨v, hv⟩ := hlive (u ++ [a]) qa' hpa'
          have hbl : B.Lang (fit nB ((u ++ [a]) ++ v)) := hfit _ (path_trans hpa' hv)
          have hlen1 : (u ++ [a]).length ≤ nB := by simp; omega
          have hpref : ∃ w, fit nB ((u ++ [a]) ++ v) = (u ++ [a]) ++ w := by
            refine ⟨v.take (nB - (u ++ [a]).length) ++
              List.replicate (nB - ((u ++ [a]) ++ v).length) Sym.uninit, ?_⟩
            simp only [fit]
            rw [List.take_append, List.take_of_length_le hlen1, List.append_assoc]
          obtain ⟨w, hw⟩ := hpref
          rw [hw, List.append_assoc] at hbl
          obtain ⟨m, hpm, htail⟩ := path_split hbl
          have hm : m = qb := path_det_start hdet hpm hpb
          subst hm
          obtain ⟨_, qb', he, _⟩ := path_cons_iff.mp htail
          have hpb' : B.Path B.start (u ++ [a]) qb' :=
            path_trans hpb (Path.cons hqb he (Path.nil _))
          exact ⟨(a, qb'), mem_out.mpr he, rfl,
            forallAux_complete_aux hdet hlive hfit k fuel qa' qb' (u ++ [a])
              (by simp; omega) (by omega) hpa' hpb'⟩

/-- Completeness of the universal exploration for an explicit step budget: with a
destination that is deterministic at its reachable non-accept states, a `ReachableLive`
source, and a budget larger than the destination size `nB`, the exploration from the two
start states accepts every pair satisfying `FitSubset A B nB`. -/
theorem forallAux_complete_fit_of_lt_fuel {A B : Layout} {nB fuel : Nat}
    (hfuel : nB < fuel) (hdet : B.ReachableDeterministic) (hlive : A.ReachableLive) :
    FitSubset A B nB → forallAux A B fuel A.start B.start = true :=
  fun hfit => forallAux_complete_aux hdet hlive hfit nB fuel A.start B.start []
    (by simp) (by omega) (Path.nil _) (Path.nil _)

/-- The existential exploration for an explicit step budget: if the source accepts `v` from
`qa` and the destination accepts the size-`k` view `fit k v` from `qb`, and the budget is
larger than `k`, the exploration from `(qa, qb)` succeeds. -/
theorem existsAux_of_accepts_fit {A B : Layout} :
    ∀ {k fuel qa qb : Nat} {v : List Sym},
      A.Accepts qa v → B.Accepts qb (fit k v) → k + 1 ≤ fuel →
      existsAux A B fuel qa qb = true
  | 0, fuel, qa, qb, v, _, hpb, hfuel => by
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [fit_zero] at hpb
      have hqb := path_nil_iff.mp hpb
      simp [existsAux, hqb]
  | k + 1, fuel, qa, qb, v, hpa, hpb, hfuel => by
    cases fuel with
    | zero => omega
    | succ fuel =>
      unfold existsAux
      split
      · rfl
      · rename_i hqb
        cases v with
        | nil =>
          have hqa := path_nil_iff.mp hpa
          subst hqa
          simp only [ite_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
          rw [fit_nil_succ] at hpb
          obtain ⟨_, qb', he, hp'⟩ := path_cons_iff.mp hpb
          exact ⟨(Sym.uninit, qb'), mem_out.mpr he, rfl,
            existsAux_of_accepts_fit (k := k) (v := []) (Path.nil _) hp' (by omega)⟩
        | cons a v' =>
          obtain ⟨hqa, qa', hea, hpa'⟩ := path_cons_iff.mp hpa
          simp only [hqa, ite_false, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
          rw [fit_cons] at hpb
          obtain ⟨_, qb', heb, hpb'⟩ := path_cons_iff.mp hpb
          exact ⟨(a, qa'), mem_out.mpr hea, (a, qb'), mem_out.mpr heb, rfl,
            existsAux_of_accepts_fit hpa' hpb' (by omega)⟩

/-- The existential exploration from the two start states, for an explicit step budget: it
succeeds whenever some source word `s` has a size-`k` view accepted by the destination and
the budget is larger than `k`. -/
theorem existsAux_start_of_lang_fit_of_lt_fuel {A B : Layout} {k fuel : Nat} {s : List Sym}
    (hs : A.Lang s) (hb : B.Lang (fit k s)) (hk : k < fuel) :
    existsAux A B fuel A.start B.start = true :=
  existsAux_of_accepts_fit hs hb hk

/-! ### Accepted words are no longer than the edge list (fixed size or acyclic) -/

theorem length_le_of_nodup_subset {α : Type} [DecidableEq α] :
    ∀ {l1 l2 : List α}, l1.Nodup → (∀ x ∈ l1, x ∈ l2) → l1.length ≤ l2.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, l2, hnd, hsub => by
    obtain ⟨hx_not, hnd'⟩ := List.nodup_cons.mp hnd
    have hx_mem : x ∈ l2 := hsub x (List.mem_cons_self ..)
    have hsub' : ∀ y ∈ xs, y ∈ l2.erase x := by
      intro y hy
      have hne : y ≠ x := fun h => hx_not (h ▸ hy)
      exact (List.mem_erase_of_ne hne).mpr (hsub y (List.mem_cons_of_mem _ hy))
    have ih := length_le_of_nodup_subset hnd' hsub'
    have herase : (l2.erase x).length + 1 = l2.length := by
      rw [List.length_erase_of_mem hx_mem]
      have : 0 < l2.length := List.length_pos_of_mem hx_mem
      omega
    simp only [List.length_cons]
    omega

/-- If no state of the reachable live part lies on a non-empty cycle, the states read along
an accepting run are pairwise distinct sources of edges. -/
theorem accepting_sources_nodup {B : Layout} (hno : B.ReachableLiveAcyclic) :
    ∀ {w pre : List Sym} {q : Nat}, B.Path B.start pre q → B.Accepts q w →
      ∃ qs : List Nat, qs.length = w.length ∧ (∀ x ∈ qs, x ∈ B.edges.map Prod.fst) ∧
        qs.Nodup ∧ (∀ x ∈ qs, (∃ u, B.Path q u x) ∧ ∃ v, B.Accepts x v)
  | [], _, _, _, _ => ⟨[], rfl, by simp, List.nodup_nil, by simp⟩
  | a :: w, pre, q, hpre, hacc => by
    obtain ⟨hq, q', he, hp⟩ := path_cons_iff.mp hacc
    have hpre' : B.Path B.start (pre ++ [a]) q' :=
      path_trans hpre (Path.cons hq he (Path.nil _))
    obtain ⟨qs, hlen, hmem, hnd, hreach⟩ := accepting_sources_nodup hno hpre' hp
    have hq_not_mem : q ∉ qs := by
      intro hmq
      obtain ⟨⟨u, hu⟩, _⟩ := hreach q hmq
      exact hno pre q (a :: u) (a :: w) (by simp) hpre (Path.cons hq he hu) hacc
    refine ⟨q :: qs, by simp [hlen], ?_, List.nodup_cons.mpr ⟨hq_not_mem, hnd⟩, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact List.mem_map.mpr ⟨(x, a, q'), he, rfl⟩
      · exact hmem x hx'
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨⟨[], Path.nil _⟩, ⟨a :: w, hacc⟩⟩
      · obtain ⟨⟨u, hu⟩, hlx⟩ := hreach x hx'
        exact ⟨⟨a :: u, Path.cons hq he hu⟩, hlx⟩

/-- If `B` has no non-empty cycle through its reachable live part, every accepted word is no
longer than the edge list. -/
theorem length_le_edges_of_reachableLiveAcyclic {B : Layout} (hno : B.ReachableLiveAcyclic)
    {w : List Sym} (hw : B.Lang w) : w.length ≤ B.edges.length := by
  obtain ⟨qs, hlen, hmem, hnd, _⟩ := accepting_sources_nodup hno (Path.nil B.start) hw
  have hle := length_le_of_nodup_subset hnd hmem
  rw [List.length_map] at hle
  omega

/-- A fixed-size layout has no non-empty cycle through its reachable live part (such a cycle
could be pumped into a longer accepted word). -/
theorem reachableLiveAcyclic_of_fixedSize {B : Layout} {n : Nat} (hB : B.FixedSize n) :
    B.ReachableLiveAcyclic := by
  intro pre p c v hc hpre hcyc hacc
  have h1 := hB (pre ++ v) (path_trans hpre hacc)
  have h2 := hB (pre ++ (c ++ v)) (path_trans hpre (path_trans hcyc hacc))
  have hpos : 0 < c.length := List.length_pos_iff.mpr hc
  simp only [List.length_append] at h1 h2
  omega

theorem reachableLiveAcyclic_of_acyclic {B : Layout} (hB : B.Acyclic) : B.ReachableLiveAcyclic :=
  fun _ p c _ hc _ hcyc _ => hB p c hc hcyc

/-- In a fixed-size layout every accepted word is no longer than the edge list. -/
theorem length_le_edges_of_fixedSize {B : Layout} {n : Nat} (hB : B.FixedSize n)
    {w : List Sym} (hw : B.Lang w) : w.length ≤ B.edges.length :=
  length_le_edges_of_reachableLiveAcyclic (reachableLiveAcyclic_of_fixedSize hB) hw

/-- In an acyclic layout every accepted word is no longer than the edge list. -/
theorem length_le_edges_of_acyclic {B : Layout} (hB : B.Acyclic)
    {w : List Sym} (hw : B.Lang w) : w.length ≤ B.edges.length :=
  length_le_edges_of_reachableLiveAcyclic (reachableLiveAcyclic_of_acyclic hB) hw

/-! ### Certificates for `Acyclic` -/

/-- A decreasing-rank certificate: every edge out of a non-accept state goes to a state of
strictly smaller rank. -/
def DecrCert (A : Layout) (rank : Nat → Nat) : Prop :=
  ∀ e ∈ A.edges, e.1 ≠ A.accept → rank e.2.2 < rank e.1

instance (A : Layout) (rank : Nat → Nat) : Decidable (DecrCert A rank) := by
  unfold DecrCert
  infer_instance

theorem rank_lt_of_path_of_decrCert {A : Layout} {rank : Nat → Nat} (h : DecrCert A rank) :
    ∀ {q : Nat} {w : List Sym} {r : Nat}, A.Path q w r → w ≠ [] → rank r < rank q
  | q, [], r, _, hw => absurd rfl hw
  | q, a :: w, r, hp, _ => by
    obtain ⟨hq, q', he, hp'⟩ := path_cons_iff.mp hp
    have h1 : rank q' < rank q := h (q, a, q') he hq
    cases w with
    | nil =>
      have := path_nil_iff.mp hp'
      subst this
      exact h1
    | cons b w =>
      have h2 := rank_lt_of_path_of_decrCert h hp' (by simp)
      omega

theorem acyclic_of_decrCert {A : Layout} {rank : Nat → Nat} (h : DecrCert A rank) :
    A.Acyclic :=
  fun _ _ hw hp => Nat.lt_irrefl _ (rank_lt_of_path_of_decrCert h hp hw)

end Toy.LayoutDfa
