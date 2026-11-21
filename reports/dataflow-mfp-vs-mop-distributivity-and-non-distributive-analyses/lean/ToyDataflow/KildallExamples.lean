import ToyDataflow.ExactnessExamples

/-!
# Further witnesses for the worklist solver

* the fuel bound `n * (h + 1) + 1` is attained for every `n ≥ 1` and `h ≥ 0`;
* the ascending chain condition alone gives no uniform fuel bound;
* non-vacuity and canonical counterexamples for the end-to-end theorem
  `kildall_eq_some_isMOPAt_of_distributive_of_unreachableStrict_of_heightLe`.
-/

namespace Toy.Dataflow

/-- Saturating successor on the chain `0 < 1 < ⋯ < h`. -/
def satSucc (h : Nat) (a : Fin (h + 1)) : Fin (h + 1) :=
  if ha : a.val < h then ⟨a.val + 1, by omega⟩ else a

theorem satSucc_monotone (h : Nat) : Monotone (finChainLat h) (satSucc h) := by
  intro a b hab
  simp only [finChainLat, satSucc] at hab ⊢
  split <;> split <;> simp_all <;> omega

/-- `m + 1` nodes, each with a self-loop, transfer `satSucc h`. -/
def selfLoopsCFG (m h : Nat) : CFG (m + 1) (Fin (h + 1)) where
  edges := (List.finRange (m + 1)).map (fun u => (u, u))
  entry := 0
  init := ⟨0, Nat.zero_lt_succ h⟩
  f := fun _ => satSucc h

theorem filter_false_nil {β : Type} (l : List β) (p : β → Bool) (hp : ∀ x ∈ l, p x = false) :
    l.filter p = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.filter_cons, hp a (List.mem_cons_self ..)]
    exact ih (fun x hx => hp x (List.mem_cons_of_mem _ hx))

theorem succs_selfLoopsCFG_aux {n : Nat} (l : List (Fin n)) (hn : l.Nodup) (u : Fin n) (hu : u ∈ l) :
    ((l.map (fun v => (v, v))).filter (fun e => decide (e.1 = u))).map Prod.snd = [u] := by
  induction l with
  | nil => simp at hu
  | cons a l ih =>
    rw [List.nodup_cons] at hn
    simp only [List.map_cons, List.filter_cons]
    rcases List.mem_cons.1 hu with hEq | hu
    · subst hEq
      have hf : (l.map (fun v => (v, v))).filter (fun e => decide (e.1 = u)) = [] := by
        apply filter_false_nil
        intro ⟨x, y⟩ hxy
        simp only [List.mem_map] at hxy
        obtain ⟨v, hv, he⟩ := hxy
        cases he
        simp only [decide_eq_false_iff_not]
        intro e; subst e; exact hn.1 hv
      simp [hf]
    · have hne : a ≠ u := fun e => hn.1 (e ▸ hu)
      simp [hne, ih hn.2 hu]

theorem succs_selfLoopsCFG (m h : Nat) (u : Fin (m + 1)) :
    succs (selfLoopsCFG m h) u = [u] :=
  succs_selfLoopsCFG_aux (List.finRange (m + 1)) (List.nodup_finRange (m + 1)) u (List.mem_finRange u)

theorem drain_selfLoop (m h : Nat) (u : Fin (m + 1)) (rest : List (Fin (m + 1))) :
    ∀ d k (x : Fin (m + 1) → Fin (h + 1)),
      k ≤ h → (x u).val = k → k + d = h + 1 →
      kildallLoop (finChainLat h) (selfLoopsCFG m h) (d + rest.length * (h + 1)) x (u :: rest) =
        kildallLoop (finChainLat h) (selfLoopsCFG m h) (rest.length * (h + 1))
          (upd x u ⟨h, Nat.lt_succ_self h⟩) rest
  | 0, k, _, hk, _, hkd => by omega
  | d + 1, k, x, hk, hxu, hkd => by
    by_cases hlt : k < h
    · have hsat : satSucc h (x u) = ⟨k + 1, by omega⟩ := by
        simp [satSucc, hxu, hlt]
      have hnle : ¬ (finChainLat h).le ⟨k + 1, by omega⟩ (x u) := by
        simp [finChainLat, hxu]
      have hjoin : (finChainLat h).join (x u) ⟨k + 1, by omega⟩ = ⟨k + 1, by omega⟩ := by
        simp [finChainLat, hxu]
      have hupd2 : upd (upd x u ⟨k + 1, by omega⟩) u ⟨h, Nat.lt_succ_self h⟩ =
          upd x u ⟨h, Nat.lt_succ_self h⟩ := by
        funext v
        by_cases hv : v = u <;> simp [upd, hv]
      have hstep : kildallLoop (finChainLat h) (selfLoopsCFG m h)
            ((d + 1) + rest.length * (h + 1)) x (u :: rest) =
          kildallLoop (finChainLat h) (selfLoopsCFG m h)
            (d + rest.length * (h + 1)) (upd x u ⟨k + 1, by omega⟩) (u :: rest) := by
        rw [Nat.succ_add]
        simp only [kildallLoop]
        rw [succs_selfLoopsCFG m h u]
        change kildallLoop (finChainLat h) (selfLoopsCFG m h) (d + rest.length * (h + 1))
          (propagate (finChainLat h) (satSucc h (x u)) [u] x rest).1
          (propagate (finChainLat h) (satSucc h (x u)) [u] x rest).2 = _
        simp only [hsat, propagate, hnle, ↓reduceIte, hjoin]
      rw [hstep, drain_selfLoop m h u rest d (k + 1) (upd x u ⟨k + 1, by omega⟩)
        (by omega) (by simp [upd]) (by omega), hupd2]
    · have hkh : k = h := by omega
      have hd0 : d = 0 := by omega
      subst hd0
      have hsat : satSucc h (x u) = x u := by simp [satSucc, hxu, hkh]
      have hle : (finChainLat h).le (x u) (x u) := Nat.le_refl _
      have hupd_eq : upd x u ⟨h, Nat.lt_succ_self h⟩ = x := by
        funext v
        by_cases hv : v = u
        · subst hv; exact Fin.ext (by simp [upd, hxu, hkh])
        · simp [upd, hv]
      rw [Nat.zero_add, Nat.add_comm 1 (rest.length * (h + 1))]
      simp only [kildallLoop]
      rw [succs_selfLoopsCFG m h u]
      change kildallLoop (finChainLat h) (selfLoopsCFG m h) (rest.length * (h + 1))
        (propagate (finChainLat h) (satSucc h (x u)) [u] x rest).1
        (propagate (finChainLat h) (satSucc h (x u)) [u] x rest).2 = _
      rw [hsat]
      simp only [propagate, hle, ↓reduceIte, hupd_eq]

theorem kildallLoop_selfLoops_suffix (m h : Nat) :
    ∀ (wl : List (Fin (m + 1))) (x : Fin (m + 1) → Fin (h + 1)),
      wl.Nodup → (∀ v ∈ wl, x v = ⟨0, Nat.zero_lt_succ h⟩) →
      kildallLoop (finChainLat h) (selfLoopsCFG m h) (wl.length * (h + 1)) x wl = none
  | [], _, _, _ => by simp [kildallLoop]
  | u :: rest, x, hnod, hzero => by
    rw [List.nodup_cons] at hnod
    have hlen : (u :: rest).length * (h + 1) = (h + 1) + rest.length * (h + 1) := by
      rw [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [hlen]
    have hxu : (x u).val = 0 := by rw [hzero u (List.mem_cons_self ..)]
    rw [drain_selfLoop m h u rest (h + 1) 0 x (Nat.zero_le h) hxu (Nat.zero_add _)]
    apply kildallLoop_selfLoops_suffix m h rest (upd x u ⟨h, Nat.lt_succ_self h⟩) hnod.2
    intro v hv
    have hne : v ≠ u := fun e => hnod.1 (e ▸ hv)
    simp [upd, hne, hzero v (List.mem_cons_of_mem _ hv)]

/-- The fuel bound `n * (h + 1) + 1` is attained for every `n = m + 1 ≥ 1` and
every `h ≥ 0`: on the chain of height `h`, with `n` self-loops whose transfer is the
saturating successor, fuel `n * (h + 1)` runs out while fuel `n * (h + 1) + 1`
succeeds. -/
theorem kildall_fuel_bound_attained (m h : Nat) :
    (finChainLat h).IsJSL ∧
    (∀ u, Monotone (finChainLat h) ((selfLoopsCFG m h).f u)) ∧
    (finChainLat h).HeightLe h ∧
    ¬ ((m + 1) * (h + 1) + 1 ≤ (m + 1) * (h + 1)) ∧
    kildall (finChainLat h) (selfLoopsCFG m h) ((m + 1) * (h + 1)) = none ∧
    (kildall (finChainLat h) (selfLoopsCFG m h) ((m + 1) * (h + 1) + 1)).isSome = true := by
  refine ⟨finChainLat_isJSL h, fun _ => satSucc_monotone h, finChainLat_heightLe h, by omega,
    ?_, ?_⟩
  · have hinit : kildallInit (finChainLat h) (selfLoopsCFG m h) = fun _ => ⟨0, Nat.zero_lt_succ h⟩ := by
      funext v
      by_cases hv : v = 0 <;> simp [kildallInit, selfLoopsCFG, finChainLat, hv]
    have hlen : (List.finRange (m + 1)).length * (h + 1) = (m + 1) * (h + 1) := by
      simp [List.length_finRange]
    unfold kildall
    rw [hinit, ← hlen]
    exact kildallLoop_selfLoops_suffix m h (List.finRange (m + 1)) _
      (List.nodup_finRange (m + 1)) (fun _ _ => rfl)
  · exact kildall_isSome_of_heightLe (finChainLat_isJSL h) (selfLoopsCFG m h)
      (finChainLat_heightLe h) (Nat.le_refl _)

/-- Climb the chain `mid m 0 < ⋯ < mid m m` one step at a time. -/
def stepMid (m : Nat) : UnboundedChains → UnboundedChains
  | .bot => .bot
  | .mid m' k =>
    if m' = m then
      if k < m then .mid m (k + 1)
      else if k = m then .mid m m
      else .top
    else .top
  | .top => .top

theorem stepMid_monotone (m : Nat) : Monotone unboundedChainsLat (stepMid m) := by
  intro a b hab
  cases a with
  | bot => simp [stepMid, unboundedChainsLat, UnboundedChains.le]
  | top =>
    cases b <;> simp [unboundedChainsLat, UnboundedChains.le] at hab
    simp [stepMid, unboundedChainsLat, UnboundedChains.le]
  | mid m₁ k₁ =>
    cases b with
    | bot => simp [unboundedChainsLat, UnboundedChains.le] at hab
    | top =>
      cases h : stepMid m (.mid m₁ k₁) <;> simp [stepMid, unboundedChainsLat, UnboundedChains.le]
    | mid m₂ k₂ =>
      simp only [unboundedChainsLat, UnboundedChains.le] at hab
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, h12, h2m⟩
      · exact unboundedChainsLat_isJSL.refl _
      · by_cases hm : m₁ = m
        · subst hm
          by_cases hk1 : k₁ < m₁
          · by_cases hk2 : k₂ < m₁
            · simp [stepMid, hk1, hk2, unboundedChainsLat, UnboundedChains.le]; right; omega
            · have hk2eq : k₂ = m₁ := by omega
              subst hk2eq
              simp [stepMid, hk1, unboundedChainsLat, UnboundedChains.le]; right; omega
          · have hk1eq : k₁ = m₁ := by omega
            have hk2eq : k₂ = m₁ := by omega
            subst hk1eq; subst hk2eq
            exact unboundedChainsLat_isJSL.refl _
        · simp [stepMid, hm, unboundedChainsLat, UnboundedChains.le]

def stepMidCFG (m : Nat) : CFG 1 UnboundedChains :=
  ⟨[(0, 0)], 0, .mid m 0, fun _ => stepMid m⟩

theorem kildallLoop_stepMid (m : Nat) : ∀ fuel k, k + fuel ≤ m →
    kildallLoop unboundedChainsLat (stepMidCFG m) fuel (fun _ => .mid m k) [0] = none
  | 0, _, _ => rfl
  | fuel + 1, k, hk => by
    have hklt : k < m := by omega
    have hsucc : succs (stepMidCFG m) 0 = [0] := rfl
    have hnot : ¬ unboundedChainsLat.le (stepMid m (.mid m k)) (.mid m k) := by
      simp [stepMid, hklt, unboundedChainsLat, UnboundedChains.le]
      omega
    have hupd : upd (fun _ : Fin 1 => UnboundedChains.mid m k) 0
        (unboundedChainsLat.join (.mid m k) (stepMid m (.mid m k))) = fun _ => .mid m (k + 1) := by
      funext v
      have : v = 0 := by revert v; decide
      subst this
      simp [upd, stepMid, hklt, unboundedChainsLat, UnboundedChains.join]
      omega
    show kildallLoop unboundedChainsLat (stepMidCFG m) fuel
      (propagate unboundedChainsLat ((stepMidCFG m).f 0 (.mid m k)) (succs (stepMidCFG m) 0)
        (fun _ => .mid m k) []).1
      (propagate unboundedChainsLat ((stepMidCFG m).f 0 (.mid m k)) (succs (stepMidCFG m) 0)
        (fun _ => .mid m k) []).2 = none
    rw [hsucc]
    change kildallLoop unboundedChainsLat (stepMidCFG m) fuel
      (propagate unboundedChainsLat (stepMid m (.mid m k)) [0] (fun _ => .mid m k) []).1
      (propagate unboundedChainsLat (stepMid m (.mid m k)) [0] (fun _ => .mid m k) []).2 = none
    simp only [propagate, hnot, ↓reduceIte, hupd]
    exact kildallLoop_stepMid m fuel (k + 1) (by omega)

/-- The ascending chain condition gives no uniform fuel bound: on `unboundedChainsLat`
(ascending chain condition, no finite height), for every amount of fuel there is a
one-node CFG with a monotone transfer on which the solver runs out of fuel. -/
theorem kildall_acc_has_no_uniform_fuel :
    unboundedChainsLat.IsJSL ∧ unboundedChainsLat.AscendingChainCondition ∧
      ∀ fuel : Nat, ∃ G : CFG 1 UnboundedChains,
        (∀ u, Monotone unboundedChainsLat (G.f u)) ∧ kildall unboundedChainsLat G fuel = none := by
  refine ⟨unboundedChainsLat_isJSL, unboundedChainsLat_acc, fun fuel => ?_⟩
  refine ⟨stepMidCFG fuel, fun _ => stepMid_monotone fuel, ?_⟩
  have hinit : kildallInit unboundedChainsLat (stepMidCFG fuel) = fun _ => .mid fuel 0 := by
    funext v
    have : v = 0 := by revert v; decide
    subst this; rfl
  have hrange : List.finRange 1 = [0] := by decide
  unfold kildall
  rw [hinit, hrange]
  exact kildallLoop_stepMid fuel fuel 0 (Nat.le_of_eq (Nat.zero_add fuel))

theorem satSucc_distributive (h : Nat) : Distributive (finChainLat h) (satSucc h) := by
  intro a b
  apply Fin.ext
  simp only [finChainLat, satSucc]
  split <;> split <;> split <;> simp_all <;> split <;> simp_all <;> omega

/-- Non-vacuity of the end-to-end theorem on the gen/kill loop: distributive
transfers, all nodes reachable (so `UnreachableStrict`), height `2`, fuel
`7 = 2 * (2 + 1) + 1`; the solver's result is the least solution and the MOP value at
every node. -/
theorem kildall_isMOPAt_nonvacuous :
    (bvLat 2).IsJSL ∧ (∀ u, Distributive (bvLat 2) (loopGK.f u)) ∧
      UnreachableStrict (bvLat 2) loopGK ∧ (bvLat 2).HeightLe 2 ∧ 2 * (2 + 1) + 1 ≤ 7 ∧
      ∃ x, kildall (bvLat 2) loopGK 7 = some x ∧ IsLeastSolution (bvLat 2) loopGK x ∧
        ∀ v, IsMOPAt (bvLat 2) loopGK v (x v) :=
  ⟨bvLat_isJSL 2, fun _ => genKill_distributive _ _,
    unreachableStrict_of_allReachable _ loopGK_allReachable, bvLat_heightLe 2, by decide,
    kildall_eq_some_isMOPAt_of_distributive_of_unreachableStrict_of_heightLe (bvLat_isJSL 2) loopGK
      (fun _ => genKill_distributive _ _) (unreachableStrict_of_allReachable _ loopGK_allReachable)
      (bvLat_heightLe 2) (by decide)⟩

/-- Canonical counterexamples for the end-to-end theorem, one per hypothesis:
* distributivity: the constant-propagation diamond (height `6`, fuel `36`), monotone
  transfers, all nodes reachable;
* strictness at unreachable nodes: `ugCFG` (height `1`, fuel `7`), gen/kill transfers;
* height bound: the successor loop on `ℕ` (distributive, all nodes reachable), where
  the solver returns `none` for every fuel;
* fuel: one self-loop on the chain of height `h` (distributive, all nodes reachable),
  with fuel `1 * (h + 1)`.
In each case the conclusion `∃ x, kildall L G fuel = some x ∧ IsLeastSolution L G x ∧
∀ v, IsMOPAt L G v (x v)` fails. -/
theorem kildall_isMOPAt_counterexamples :
    (cpLat.IsJSL ∧ cpLat.HeightLe 6 ∧ 5 * (6 + 1) + 1 ≤ 36 ∧
        AllReachable (cpDiamond ⟨.top, .top, .top⟩) ∧
        UnreachableStrict cpLat (cpDiamond ⟨.top, .top, .top⟩) ∧
        ¬ (∀ u, Distributive cpLat ((cpDiamond ⟨.top, .top, .top⟩).f u)) ∧
        ¬ ∃ x, kildall cpLat (cpDiamond ⟨.top, .top, .top⟩) 36 = some x ∧
          IsLeastSolution cpLat (cpDiamond ⟨.top, .top, .top⟩) x ∧
          ∀ v, IsMOPAt cpLat (cpDiamond ⟨.top, .top, .top⟩) v (x v)) ∧
      ((bvLat 1).IsJSL ∧ (bvLat 1).HeightLe 1 ∧ 3 * (1 + 1) + 1 ≤ 7 ∧
        (∀ u, Distributive (bvLat 1) (ugCFG.f u)) ∧ ¬ UnreachableStrict (bvLat 1) ugCFG ∧
        ¬ ∃ x, kildall (bvLat 1) ugCFG 7 = some x ∧ IsLeastSolution (bvLat 1) ugCFG x ∧
          ∀ v, IsMOPAt (bvLat 1) ugCFG v (x v)) ∧
      (natMaxLat.IsJSL ∧ (∀ u, Distributive natMaxLat (succCFG.f u)) ∧ AllReachable succCFG ∧
        UnreachableStrict natMaxLat succCFG ∧
        (∀ h, ¬ natMaxLat.HeightLe h) ∧
        ∀ fuel, ¬ ∃ x, kildall natMaxLat succCFG fuel = some x ∧
          IsLeastSolution natMaxLat succCFG x ∧ ∀ v, IsMOPAt natMaxLat succCFG v (x v)) ∧
      (∀ h, (finChainLat h).IsJSL ∧ (∀ u, Distributive (finChainLat h) ((selfLoopsCFG 0 h).f u)) ∧
        AllReachable (selfLoopsCFG 0 h) ∧ UnreachableStrict (finChainLat h) (selfLoopsCFG 0 h) ∧
        (finChainLat h).HeightLe h ∧
        ¬ (1 * (h + 1) + 1 ≤ 1 * (h + 1)) ∧
        ¬ ∃ x, kildall (finChainLat h) (selfLoopsCFG 0 h) (1 * (h + 1)) = some x ∧
          IsLeastSolution (finChainLat h) (selfLoopsCFG 0 h) x ∧
          ∀ v, IsMOPAt (finChainLat h) (selfLoopsCFG 0 h) v (x v)) := by
  obtain ⟨_, _, hall, _, hmono, hnd, _, _⟩ := exactness_needs_distributive
  obtain ⟨_, _, hdu, _, _, hnus, hls, _, hnot⟩ := exactness_needs_unreachableStrict
  refine ⟨⟨cpLat_isJSL, cpLat_heightLe, by decide, hall, unreachableStrict_of_allReachable _ hall, hnd, ?_⟩,
    ⟨bvLat_isJSL 1, bvLat_heightLe 1, by decide, hdu, hnus, ?_⟩,
    ⟨natMaxLat_isJSL, kildall_needs_heightLe.2.2.1, kildall_needs_heightLe.2.2.2.1,
      unreachableStrict_of_allReachable _ kildall_needs_heightLe.2.2.2.1,
      kildall_needs_heightLe.2.2.2.2.2.1, fun fuel ⟨x, hk, _⟩ => ?_⟩, fun h => ?_⟩
  · rintro ⟨x, _, hx, hm⟩
    exact (cpDiamond_mfp_x_top_ne_mop_x_const3 _ hx).2.2 (hm 4)
  · rintro ⟨x, _, hx, hm⟩
    have e := IsLeastSolution.unique (bvLat_isJSL 1) hx hls
    exact hnot (e ▸ hm 2)
  · rw [kildall_needs_heightLe.2.2.2.2.2.2 fuel] at hk
    simp at hk
  · obtain ⟨_, _, hh, _, hnone, _⟩ := kildall_fuel_bound_attained 0 h
    have hall0 : AllReachable (selfLoopsCFG 0 h) := fun v => by
      have : v = 0 := by revert v; decide
      subst this; exact ⟨.nil⟩
    refine ⟨finChainLat_isJSL h, fun _ => satSucc_distributive h, hall0,
      unreachableStrict_of_allReachable _ hall0, hh, by omega, fun ⟨x, hk, _⟩ => ?_⟩
    · rw [hnone] at hk
      simp at hk

end Toy.Dataflow
