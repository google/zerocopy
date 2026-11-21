import MonoShim.AdequacyTightness

/-!
# Termination of collection
-/

namespace Toy.MonoShim

/-- `box` applied `k` times. -/
def boxIter : Nat → Ty → Ty
  | 0, t => t
  | k + 1, t => .box (boxIter k t)

/-- Size of a type (number of constructors). -/
def Ty.size : Ty → Nat
  | .box t => t.size + 1
  | .pair a b => a.size + b.size + 1
  | .proj _ t => t.size + 1
  | _ => 1

theorem Ty.norm_nil : ∀ t : Ty, t.norm [] = t := by
  intro t
  induction t with
  | box t ih => simp [Ty.norm, ih]
  | pair a b iha ihb => simp [Ty.norm, iha, ihb]
  | proj tr t ih => simp [Ty.norm, ih, assocLookup]
  | _ => rfl

/-- Polymorphic recursion under a value guard: `main` calls `f::<base 0>`, and `f<T>` calls
`f::<Box<T>>` when the guard counter is nonzero. -/
def P5 : Program where
  fns := [⟨false, .call 1 [.base 0]⟩, ⟨false, .guard (.call 1 [.box (.param 0)])⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := []

theorem P5_srcDef_f (t : Ty) : srcDef P5 (.inst 1 [t]) = some (.guard (.call 1 [.box t])) := by
  simp [srcDef, Key.norm, Ty.norm_nil, srcDef0, P5, Stmt.subst, Ty.subst, Stmt.norm, Ty.norm]

theorem P5_srcDef_main : srcDef P5 (.inst 0 []) = some (.call 1 [.base 0]) := by
  simp [srcDef, Key.norm, srcDef0, P5, Stmt.subst, Ty.subst, Stmt.norm, Ty.norm]

theorem P5_f_step (n : Nat) (t : Ty) (st : St) :
    runS P5 (n + 1) (.inst 1 [t]) st =
      if st.ctr = 0 then (.ok, st) else runS P5 n (.inst 1 [.box t]) { st with ctr := st.ctr - 1 } := by
  simp only [runS, runKey, P5_srcDef_f]
  by_cases h : st.ctr = 0
  · simp [execS, h]
  · simp [execS, h]

theorem P5_f_run_ok : ∀ (c : Nat) (t : Ty) (evs : List Nat),
    (runS P5 (c + 2) (.inst 1 [t]) ⟨evs, c⟩).1 = .ok := by
  intro c
  induction c with
  | zero => intro t evs; rw [P5_f_step]; simp
  | succ c ih =>
    intro t evs
    rw [show c + 1 + 2 = (c + 2) + 1 by omega, P5_f_step]
    simpa using ih (.box t) evs

/-- **Polymorphic recursion has finite runs**: from every initial counter value `c`, the run of
`main` with `c + 3` units of fuel completes normally. -/
theorem polyrec_runs_finite (c : Nat) (evs : List Nat) :
    (runS P5 (c + 3) (.inst 0 []) ⟨evs, c⟩).1 = .ok := by
  have h := P5_f_run_ok c (.base 0) evs
  simp only [runS] at h
  simp only [runS, runKey, P5_srcDef_main, execS]
  exact h

/-- **…but an infinite instance set**: every `f::<Box^k<base 0>>` is reachable. -/
theorem polyrec_instances_reachable (k : Nat) :
    Reach (edgesM P5 (stdCfg P5)) [.inst 0 []] (.inst 1 [boxIter k (.base 0)]) := by
  induction k with
  | zero =>
    exact Reach.step (k := .inst 0 []) (Reach.root (by simp)) (by decide)
  | succ k ih =>
    refine Reach.step ih ?_
    simp [edgesM, bodyM, Key.isShim, srcDef0, P5, Stmt.subst, stdCfg, refs, Key.norm, Ty.norm_nil,
      boxIter, Ty.subst, Stmt.norm, Ty.norm]

def keyDepth : Key → Nat
  | .inst _ [t] => t.size
  | _ => 0

theorem list_keyDepth_bounded : ∀ T : List Key, ∃ N, ∀ k ∈ T, keyDepth k < N := by
  intro T
  induction T with
  | nil => exact ⟨0, by simp⟩
  | cons k T ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨N + keyDepth k + 1, ?_⟩
    intro k' hk'
    rcases List.mem_cons.mp hk' with rfl | hk'
    · omega
    · have := hN k' hk'; omega

theorem boxIter_size (k : Nat) : (boxIter k (.base 0)).size = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [boxIter, Ty.size, ih]

/-- **The collector diverges on polymorphic recursion**: for every admissible scheduler and every
fuel, the worklist collector fails to finish. (With `polyrec_runs_finite` and `polyrec_instances_reachable`, this refutes, in the
toy, the claim that every program whose runs are finite has a finite set of reachable
instances; the toy has no type system.) -/
theorem polyrec_collector_diverges (sched : List Key → List Key → List Key) (hs : SchedOK sched)
    (fuel : Nat) : collect (edgesM P5 (stdCfg P5)) sched [.inst 0 []] fuel = none := by
  rcases h : collect (edgesM P5 (stdCfg P5)) sched [.inst 0 []] fuel with _ | T
  · rfl
  · exfalso
    obtain ⟨N, hN⟩ := list_keyDepth_bounded T
    have hr := polyrec_instances_reachable N
    have hm := (collect_mem_iff_reach _ sched hs _ fuel T h _).mpr hr
    have := hN _ hm
    simp [keyDepth, boxIter_size] at this
    omega

/-! ## A decidable rank check -/

def Ty.hasParam : Ty → Bool
  | .param _ => true
  | .box t => t.hasParam
  | .pair a b => a.hasParam || b.hasParam
  | .proj _ t => t.hasParam
  | _ => false

/-- A type argument grows when it mentions a parameter strictly inside `box`, `pair` or `proj`
(a bare parameter does not grow; a projection of a parameter counts as growing). -/
def Ty.grows : Ty → Bool
  | .param _ => false
  | t => t.hasParam

/-- Function-instance references of a statement: calls, reifications, and directly invoked
instance or reify-shim keys. -/
def instRefs : Stmt → List (Nat × List Ty)
  | .seq a b => instRefs a ++ instRefs b
  | .onUnwind a b => instRefs a ++ instRefs b
  | .guard s => instRefs s
  | .call f τs => [(f, τs)]
  | .reify _ f τs => [(f, τs)]
  | .invoke (.inst f τs) => [(f, τs)]
  | .invoke (.reifyShim f τs) => [(f, τs)]
  | _ => []

/-- Rank check (a function-level no-growing-cycle certificate): every function-instance
reference from `f` to `g` has `rank g ≤ rank f`, strictly when some type argument grows. -/
def rankCheck (P : Program) (rank : Nat → Nat) : Bool :=
  (List.range P.fns.length).all fun f =>
    match P.fns[f]? with
    | none => true
    | some fd => (instRefs fd.body).all fun r =>
        if r.2.any Ty.grows then decide (rank r.1 < rank f) else decide (rank r.1 ≤ rank f)

/-- Positive control / non-vacuity: growth along a non-recursive chain passes the check and the
collector terminates. `main` calls `f::<base 0>`, `f<T>` calls `g::<Box<T>>`, `g<U>` drops a
`U`. -/
def P5ok : Program where
  fns := [⟨false, .call 1 [.base 0]⟩, ⟨false, .call 2 [.box (.param 0)]⟩, ⟨false, .drop (.param 0)⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := []

def rank5ok : Nat → Nat
  | 0 => 2
  | 1 => 1
  | _ => 0

theorem P5ok_rankCheck_and_collects :
    rankCheck P5ok rank5ok = true ∧ assocNormal P5ok = true ∧ SchedOK fifo ∧
    collect (edgesM P5ok (stdCfg P5ok)) fifo [.inst 0 []] 20 =
      some [.dropGlue (.base 0), .dropGlue (.box (.base 0)), .inst 2 [.box (.base 0)],
        .inst 1 [.base 0], .inst 0 []] := by
  exact ⟨by decide, by decide, fifo_ok, by decide⟩

/-- The polymorphic-recursion program fails the rank check for every rank. -/
theorem P5_fails_rankCheck (rank : Nat → Nat) : rankCheck P5 rank = false := by
  simp [rankCheck, P5, instRefs, Ty.grows, Ty.hasParam, List.range, List.range.loop]

/-- Positive control for divergence: non-growing self-recursion (`f<T>` calls `f::<T>`) collects
a finite set. -/
def P5flat : Program where
  fns := [⟨false, .call 1 [.base 0]⟩, ⟨false, .guard (.call 1 [.param 0])⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := []

theorem P5flat_collects : collect (edgesM P5flat (stdCfg P5flat)) fifo [.inst 0 []] 10 =
    some [.inst 1 [.base 0], .inst 0 []] := by
  decide

/-- The rank check is conservative: `f<T>` calls `g::<Box<T>>` and `g<U>` calls `f::<base 0>`.
The function-level cycle contains a growing edge, so every rank fails, yet collection terminates
(the parameter does not flow around the cycle). -/
def P5mut : Program where
  fns := [⟨false, .call 1 [.base 0]⟩, ⟨false, .call 2 [.box (.param 0)]⟩,
    ⟨false, .call 1 [.base 0]⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := []

theorem rankCheck_not_necessary :
    (∀ rank, rankCheck P5mut rank = false) ∧
    collect (edgesM P5mut (stdCfg P5mut)) fifo [.inst 0 []] 10 =
      some [.inst 2 [.box (.base 0)], .inst 1 [.base 0], .inst 0 []] := by
  refine ⟨?_, by decide⟩
  intro rank
  simp [rankCheck, P5mut, instRefs, Ty.grows, Ty.hasParam, List.range, List.range.loop]

/-! ## Tightness witnesses for the termination theorem -/

/-- Tightness of the rank check: the polymorphic-recursion program fails `rankCheck` for every
rank, its associated-type table is (vacuously) normal, FIFO is admissible, and the collector
returns no set at any fuel. -/
theorem polyrec_fails_rankCheck_and_diverges :
    (∀ rank, rankCheck P5 rank = false) ∧ assocNormal P5 = true ∧ SchedOK fifo ∧
    ¬ ∃ fuel T, collect (edgesM P5 (stdCfg P5)) fifo [.inst 0 []] fuel = some T := by
  refine ⟨P5_fails_rankCheck, by decide, fifo_ok, ?_⟩
  rintro ⟨fuel, T, hT⟩
  rw [polyrec_collector_diverges fifo fifo_ok fuel] at hT
  cases hT

theorem boxIter_norm (A : List (Nat × Ty × Ty)) (k : Nat) (t : Ty) :
    (boxIter k t).norm A = boxIter k (t.norm A) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [boxIter, Ty.norm, ih]

theorem boxIter_succ' (k : Nat) (t : Ty) : boxIter k (.box t) = boxIter (k + 1) t := by
  induction k with
  | zero => rfl
  | succ k ih => simp [boxIter, ih]

theorem boxIter_size_gen (k : Nat) (t : Ty) : (boxIter k t).size = k + t.size := by
  induction k with
  | zero => simp [boxIter]
  | succ k ih => simp [boxIter, Ty.size, ih]; omega

/-- `main` calls `f::<<base 0 as 0>::Out>` and `f<T>` calls `f::<T>` (no growing type argument,
so `rankCheck` holds with the zero rank), but `<base 0 as 0>::Out = Box<<base 0 as 0>::Out>`:
the associated-type table is not normal, and every normalization adds a `box`. -/
def P9assoc : Program where
  fns := [⟨false, .call 1 [.proj 0 (.base 0)]⟩, ⟨false, .call 1 [.param 0]⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := [(0, .base 0, .box (.proj 0 (.base 0)))]

theorem P9assoc_proj_norm :
    (Ty.proj 0 (.base 0)).norm P9assoc.assoc = .box (.proj 0 (.base 0)) := by decide

theorem P9assoc_reach (k : Nat) :
    Reach (edgesM P9assoc (stdCfg P9assoc)) [.inst 0 []]
      (.inst 1 [boxIter (2 * k + 2) (.proj 0 (.base 0))]) := by
  induction k with
  | zero => exact Reach.step (k := .inst 0 []) (Reach.root (by simp)) (by decide)
  | succ k ih =>
    refine Reach.step ih ?_
    have h1 : (boxIter (2 * k + 2) (.proj 0 (.base 0))).norm P9assoc.assoc =
        boxIter (2 * k + 3) (.proj 0 (.base 0)) := by
      rw [boxIter_norm, P9assoc_proj_norm, boxIter_succ']
    have h2 : (boxIter (2 * k + 3) (.proj 0 (.base 0))).norm P9assoc.assoc =
        boxIter (2 * (k + 1) + 2) (.proj 0 (.base 0)) := by
      rw [boxIter_norm, P9assoc_proj_norm, boxIter_succ',
        show 2 * (k + 1) + 2 = 2 * k + 3 + 1 by omega]
    simp only [edgesM, bodyM, Key.isShim, Bool.false_eq_true, ite_false, srcDef0, stdCfg]
    simp [P9assoc, Stmt.subst, Ty.subst, Stmt.norm, refs, Key.norm]
    rw [show (P9assoc.assoc) = [(0, .base 0, .box (.proj 0 (.base 0)))] from rfl] at h1 h2
    rw [h1, h2]

/-- Tightness of `assocNormal`: `P9assoc` passes the rank check with the zero rank and its root
is in normal form, FIFO is admissible, but the table is not normal and the collector returns no
set at any fuel. -/
theorem nonnormal_assoc_breaks_termination :
    rankCheck P9assoc (fun _ => 0) = true ∧ assocNormal P9assoc = false ∧ SchedOK fifo ∧
    CanonicalKeys P9assoc [.inst 0 []] ∧
    ¬ ∃ fuel T, collect (edgesM P9assoc (stdCfg P9assoc)) fifo [.inst 0 []] fuel = some T := by
  refine ⟨by decide, by decide, fifo_ok, by decide, ?_⟩
  rintro ⟨fuel, T, hT⟩
  obtain ⟨N, hN⟩ := list_keyDepth_bounded T
  have hm := (collect_mem_iff_reach _ fifo fifo_ok _ fuel T hT _).mpr (P9assoc_reach N)
  have := hN _ hm
  simp [keyDepth, boxIter_size_gen, Ty.size] at this
  omega

/-- The empty program. -/
def Pempty : Program where
  fns := []
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := []

/-- An inadmissible scheduler that replaces the worklist by two fresh keys. -/
def schedBump : List Key → List Key → List Key
  | .userDrop n :: _, _ => [.userDrop (n + 1), .userDrop (n + 2)]
  | _, _ => []

theorem schedBump_not_ok : ¬ SchedOK schedBump := by
  intro h
  have := (h [.userDrop 0] [] (.userDrop 0)).mpr (Or.inl (by simp))
  simp [schedBump] at this

theorem collectGo_schedBump_none :
    ∀ (fuel m : Nat) (done : List Key), (∀ x ∈ done, ∃ j, j < m ∧ x = .userDrop j) →
      collectGo (edgesM Pempty (stdCfg Pempty)) schedBump fuel
        [.userDrop m, .userDrop (m + 1)] done = none := by
  intro fuel
  induction fuel with
  | zero => intro m done _; rfl
  | succ fuel ih =>
    intro m done hdone
    have hnot : Key.userDrop m ∉ done := by
      intro hm
      obtain ⟨j, hj, heq⟩ := hdone _ hm
      cases heq
      omega
    simp only [collectGo, hnot, ite_false, schedBump]
    apply ih (m + 2) (.userDrop m :: done)
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨m, by omega, rfl⟩
    · obtain ⟨j, hj, heq⟩ := hdone x hx
      exact ⟨j, by omega, heq⟩

/-- Tightness of scheduler admissibility: the empty program passes the rank check and has a normal
table, but with the inadmissible `schedBump` the collector returns no set at any fuel. -/
theorem inadmissible_scheduler_breaks_termination :
    rankCheck Pempty (fun _ => 0) = true ∧ assocNormal Pempty = true ∧ ¬ SchedOK schedBump ∧
    ¬ ∃ fuel T, collect (edgesM Pempty (stdCfg Pempty)) schedBump
        [.userDrop 0, .userDrop 1] fuel = some T := by
  refine ⟨rfl, rfl, schedBump_not_ok, ?_⟩
  rintro ⟨fuel, T, hT⟩
  have hnone := collectGo_schedBump_none fuel 0 [] (by simp)
  unfold collect at hT
  rw [hnone] at hT
  cases hT

end Toy.MonoShim
