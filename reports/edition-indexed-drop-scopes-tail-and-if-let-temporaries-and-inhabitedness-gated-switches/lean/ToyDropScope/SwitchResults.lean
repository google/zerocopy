import ToyDropScope.Examples

/-!
Results about inhabitedness-gated switch specialization. Main theorems, counterexamples,
non-vacuity witnesses and positive controls are fully proved.

These are statements about the toy switch model; they neither establish nor refute the
corresponding claims about Rust's operational semantics, MIR `Rvalue::Discriminant` and `SwitchInt`,
or rustc's unreachable-enum-branching pass. Model–system relation: none proved.
-/

namespace Toy.DropScope

/-- The discriminant semantics that rejects both uninhabited-variant tags and invalid tags. -/
def rejectBoth : DiscrSem := ⟨.rejectUninhabited, .rejectInvalid⟩

/-- The discriminant semantics that is permissive for uninhabited-variant tags and rejects
invalid tags. -/
def permissiveRejectInvalid : DiscrSem := ⟨.permissive, .rejectInvalid⟩

/-- An enum with an uninhabited variant between two inhabited ones (for example
`enum E { A(bool), B(Never), C }` with variant `A` holding the niche). -/
def deadNicheEnum : Enum := [true, false, true]

/-- `match e { A(_) => 0, C => 2, _ => 1 }` on `deadNicheEnum` (tags `A = 0`, `B = 1`, `C = 2`). -/
def deadNicheSwitch : Switch := ⟨[(0, .goto 0), (2, .goto 2)], .goto 1⟩

/-- A switch on `deadNicheEnum` with one explicit arm, on the uninhabited tag `1`. -/
def explicitUninhabitedArmSwitch : Switch := ⟨[(1, .goto 1)], .goto 0⟩

/-- A switch on `deadNicheEnum` whose wildcard (reached by the uninhabited tag `1`) uses the
variant's payload. -/
def usePayloadSwitch : Switch := ⟨[(0, .goto 0), (2, .goto 2)], .usePayload 1⟩

/-! ## Supporting lemmas -/

/-- Under `rejectBoth`, every tag that is not an inhabited variant's tag is read as undefined
behaviour (the condition of R5-eq and R5-iff for the enum-derived allowed set). -/
theorem readUB_rejectBoth_of_allowedTag_eq_false (E : Enum) (t : Nat)
    (h : allowedTag E.length E.inhabitedTag t = false) : readUB rejectBoth E t = true := by
  unfold readUB rejectBoth
  by_cases ht : t < E.length
  · simp only [allowedTag, ht, decide_true, Bool.true_and] at h
    simp [ht, h]
  · simp [ht]

private theorem target_pruneArms_of_allowed (n : Nat) (A : Nat → Bool) (sw : Switch) (t : Nat)
    (ht : allowedTag n A t = true) :
    (pruneArms n A sw).target t = sw.target t := by
  unfold Switch.target pruneArms
  suffices h : (sw.arms.map fun a => if allowedTag n A a.1 then a else (a.1, .unreachable)).find?
      (fun a => a.1 == t) = sw.arms.find? (fun a => a.1 == t) by
    rw [h]
  induction sw.arms with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, List.find?_cons]
    cases heq : (a.1 == t) with
    | true =>
      have h1 : a.1 = t := eq_of_beq heq
      have hall : allowedTag n A a.1 = true := h1 ▸ ht
      simp [hall, heq]
    | false =>
      cases hall : allowedTag n A a.1 <;> simp [heq, ih]

private theorem target_lastVariant_of_allowed (n : Nat) (A : Nat → Bool) (sw : Switch) (t : Nat)
    (ht : allowedTag n A t = true) :
    (lastVariantTakesWildcard n A sw).target t = sw.target t := by
  unfold lastVariantTakesWildcard
  cases hrem : remainingAllowed n A sw with
  | nil =>
    have hany : sw.arms.any (fun a => a.1 == t) = true := by
      cases hno : sw.arms.any (fun a => a.1 == t) with
      | true => rfl
      | false =>
        have hlt : t < n := by simp [allowedTag] at ht; exact ht.1
        have hAt : A t = true := by simp [allowedTag] at ht; exact ht.2
        have hmem : t ∈ remainingAllowed n A sw := by
          unfold remainingAllowed
          rw [List.mem_filter]
          exact ⟨List.mem_range.mpr hlt, by simp [hAt, hno]⟩
        rw [hrem] at hmem
        simp at hmem
    unfold Switch.target
    rcases List.any_eq_true.mp hany with ⟨a, ha, heq⟩
    cases hf : sw.arms.find? (fun a => a.1 == t) with
    | some x => simp
    | none =>
      have := List.find?_eq_none.mp hf a ha
      simp [heq] at this
  | cons j rest =>
    cases rest with
    | nil =>
      unfold Switch.target
      cases hf : sw.arms.find? (fun a => a.1 == t) with
      | some x => simp [List.find?_append, hf]
      | none =>
        have hfalse : sw.arms.any (fun a => a.1 == t) = false := by
          cases hany : sw.arms.any (fun a => a.1 == t) with
          | false => rfl
          | true =>
            rcases List.any_eq_true.mp hany with ⟨a, ha, heq⟩
            have := List.find?_eq_none.mp hf a ha
            simp [heq] at this
        have hlt : t < n := by simp [allowedTag] at ht; exact ht.1
        have hAt : A t = true := by simp [allowedTag] at ht; exact ht.2
        have hmem : t ∈ remainingAllowed n A sw := by
          unfold remainingAllowed
          rw [List.mem_filter]
          exact ⟨List.mem_range.mpr hlt, by simp [hAt, hfalse]⟩
        rw [hrem] at hmem
        simp at hmem
        subst hmem
        rw [List.find?_append, hf]
        simp
    | cons k rest' => rfl

/-! ## R5: parametric characterization -/

/-- R5-eq. For any number of variant tags `n`, allowed-tag predicate `A`, read-UB predicate `R`
and payload predicate `P`: if every tag `t` that is not an allowed tag (`allowedTag n A t = false`)
is read as undefined behaviour (`R t = true`), then the specialized switch has the same outcome as
the original on every switch and every tag. -/
theorem exec_specializeSwitch_eq_of_readUB_of_not_allowedTag (n : Nat) (A R P : Nat → Bool)
    (hR : ∀ t, allowedTag n A t = false → R t = true) (sw : Switch) (t : Nat) :
    exec R P (specializeSwitch n A sw) t = exec R P sw t := by
  unfold exec specializeSwitch
  cases hall : allowedTag n A t with
  | false => simp [hR t hall]
  | true =>
    rw [target_lastVariant_of_allowed n A _ t hall, target_pruneArms_of_allowed n A sw t hall]

/-- R5-iff. For any `n`, `A`, `R`, `P`: the specialization refines the original for every switch
and every tag iff every tag that is not an allowed tag is read as undefined behaviour. -/
theorem specializeSwitch_refines_all_iff (n : Nat) (A R P : Nat → Bool) :
    (∀ (sw : Switch) (t : Nat), Refines (exec R P (specializeSwitch n A sw) t) (exec R P sw t)) ↔
      ∀ t, allowedTag n A t = false → R t = true := by
  constructor
  · intro h t hall
    cases hRf : R t with
    | true => rfl
    | false =>
      have href := h ⟨[(t, .goto 0)], .goto 0⟩ t
      have hsrc : exec R P ⟨[(t, .goto 0)], .goto 0⟩ t = .ret 0 := by
        simp [exec, hRf, Switch.target, runArm]
      have htgt : exec R P (specializeSwitch n A ⟨[(t, .goto 0)], .goto 0⟩) t = .ub := by
        unfold exec specializeSwitch lastVariantTakesWildcard Switch.target pruneArms
        simp only [hRf, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, hall]
        cases remainingAllowed n A _ with
        | nil => simp [runArm]
        | cons j rs => cases rs <;> simp [runArm]
      rw [hsrc, htgt] at href
      simp [Refines] at href
  · intro hR sw t
    exact Or.inr (exec_specializeSwitch_eq_of_readUB_of_not_allowedTag n A R P hR sw t)

/-- R5-iff (shape 1 alone). The same characterization holds for `pruneArms` alone. -/
theorem pruneArms_refines_all_iff (n : Nat) (A R P : Nat → Bool) :
    (∀ (sw : Switch) (t : Nat), Refines (exec R P (pruneArms n A sw) t) (exec R P sw t)) ↔
      ∀ t, allowedTag n A t = false → R t = true := by
  constructor
  · intro h t hall
    cases hRf : R t with
    | true => rfl
    | false =>
      have href := h ⟨[(t, .goto 0)], .goto 0⟩ t
      simp [exec, hRf, pruneArms, hall, Switch.target, runArm, Refines] at href
  · intro hR sw t
    cases hall : allowedTag n A t with
    | false => exact Or.inl (by simp [exec, hR t hall])
    | true =>
      exact Or.inr (by unfold exec; rw [target_pruneArms_of_allowed n A sw t hall])

/-- R5-iff (shape 2 alone). The same characterization holds for `lastVariantTakesWildcard` alone
(both of its changing branches: zero remaining allowed tags without an explicit arm, and exactly
one). -/
theorem lastVariantTakesWildcard_refines_all_iff (n : Nat) (A R P : Nat → Bool) :
    (∀ (sw : Switch) (t : Nat),
        Refines (exec R P (lastVariantTakesWildcard n A sw) t) (exec R P sw t)) ↔
      ∀ t, allowedTag n A t = false → R t = true := by
  constructor
  · intro h t hall
    cases hRf : R t with
    | true => rfl
    | false =>
      let arms := ((List.range n).filter A).map fun i => (i, Arm.goto 0)
      let sw : Switch := ⟨arms, .goto 0⟩
      have hrem : remainingAllowed n A sw = [] := by
        unfold remainingAllowed
        rw [List.filter_eq_nil_iff]
        intro i hi
        simp only [Bool.and_eq_true, Bool.not_eq_true']
        rintro ⟨hAi, hno⟩
        have hmem : (i, Arm.goto 0) ∈ arms :=
          List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨hi, hAi⟩, rfl⟩
        have hany : arms.any (fun a => a.1 == i) = true :=
          List.any_eq_true.mpr ⟨(i, .goto 0), hmem, beq_self_eq_true i⟩
        exact absurd hany (by simp [sw, hno])
      have hnotmem : arms.find? (fun a => a.1 == t) = none := by
        rw [List.find?_eq_none]
        intro a ha
        rcases List.mem_map.mp ha with ⟨i, hi, rfl⟩
        rcases List.mem_filter.mp hi with ⟨hlt, hAi⟩
        have hlt' : i < n := List.mem_range.mp hlt
        simp only [beq_iff_eq]
        rintro rfl
        simp [allowedTag, hlt', hAi] at hall
      have href := h sw t
      have hsrc : exec R P sw t = .ret 0 := by
        simp [exec, hRf, Switch.target, sw, hnotmem, runArm]
      have htgt : exec R P (lastVariantTakesWildcard n A sw) t = .ub := by
        simp [exec, hRf, lastVariantTakesWildcard, hrem, Switch.target, sw, hnotmem, runArm]
      rw [hsrc, htgt] at href
      simp [Refines] at href
  · intro hR sw t
    cases hall : allowedTag n A t with
    | false => exact Or.inl (by simp [exec, hR t hall])
    | true =>
      exact Or.inr (by unfold exec; rw [target_lastVariant_of_allowed n A sw t hall])

/-- R5-eq non-vacuity: for `deadNicheEnum` (which has an uninhabited variant) with the
enum-derived allowed set, `rejectBoth` satisfies the hypothesis. -/
theorem deadNicheEnum_rejectBoth_satisfies_hypothesis :
    ∀ t, allowedTag deadNicheEnum.length deadNicheEnum.inhabitedTag t = false →
      readUB rejectBoth deadNicheEnum t = true :=
  readUB_rejectBoth_of_allowedTag_eq_false deadNicheEnum

/-- R5-eq tightness: with `R` the `permissiveRejectInvalid` read on `deadNicheEnum`, the
hypothesis fails (at the uninhabited tag `1`) and the outcomes differ on `deadNicheSwitch` at
tag `1`. -/
theorem specializeSwitch_eq_hypothesis_tight :
    ¬ (∀ t, allowedTag 3 deadNicheEnum.inhabitedTag t = false →
        readUB permissiveRejectInvalid deadNicheEnum t = true) ∧
    exec (readUB permissiveRejectInvalid deadNicheEnum) deadNicheEnum.inhabitedTag
        (specializeSwitch 3 deadNicheEnum.inhabitedTag deadNicheSwitch) 1 ≠
      exec (readUB permissiveRejectInvalid deadNicheEnum) deadNicheEnum.inhabitedTag
        deadNicheSwitch 1 := by
  refine ⟨fun h => ?_, by decide⟩
  have := h 1 (by decide)
  exact absurd this (by decide)

/-- R5-iff, right side false and refinement false: with the `permissiveRejectInvalid` read on
`deadNicheEnum`, the condition fails and the specialization of `deadNicheSwitch` does not refine
the original at tag `1` (`Refines` itself fails, not only equality). -/
theorem specializeSwitch_deadNicheSwitch_permissive_not_refines :
    ¬ (∀ t, allowedTag 3 deadNicheEnum.inhabitedTag t = false →
        readUB permissiveRejectInvalid deadNicheEnum t = true) ∧
    ¬ Refines
        (exec (readUB permissiveRejectInvalid deadNicheEnum) deadNicheEnum.inhabitedTag
          (specializeSwitch 3 deadNicheEnum.inhabitedTag deadNicheSwitch) 1)
        (exec (readUB permissiveRejectInvalid deadNicheEnum) deadNicheEnum.inhabitedTag
          deadNicheSwitch 1) := by
  refine ⟨specializeSwitch_eq_hypothesis_tight.1, ?_⟩
  unfold Refines
  decide

/-- R5-iff-shapes, shape 1 exercised directly: `pruneArms` changes `explicitUninhabitedArmSwitch`
(its explicit arm on the uninhabited tag `1` becomes `unreachable`), and under
`permissiveRejectInvalid` the pruned switch does not refine the original at tag `1`. -/
theorem pruneArms_explicitUninhabitedArm_permissive_not_refines :
    pruneArms 3 deadNicheEnum.inhabitedTag explicitUninhabitedArmSwitch ≠
      explicitUninhabitedArmSwitch ∧
    ¬ Refines
        (exec (readUB permissiveRejectInvalid deadNicheEnum) deadNicheEnum.inhabitedTag
          (pruneArms 3 deadNicheEnum.inhabitedTag explicitUninhabitedArmSwitch) 1)
        (exec (readUB permissiveRejectInvalid deadNicheEnum) deadNicheEnum.inhabitedTag
          explicitUninhabitedArmSwitch 1) := by
  refine ⟨by decide, ?_⟩
  unfold Refines
  decide

/-- R5-iff-shapes, shape 2 exercised directly in both changing branches, under
`permissiveRejectInvalid`: on `deadNicheSwitch` zero allowed tags lack an explicit arm and the
narrowed switch does not refine the original at the uninhabited tag `1`; on the enum
`[true, false, true, true]` exactly one allowed tag (`3`) lacks an explicit arm and the narrowed
switch does not refine the original at the uninhabited tag `1`. -/
theorem lastVariantTakesWildcard_permissive_not_refines_both_branches :
    remainingAllowed 3 deadNicheEnum.inhabitedTag deadNicheSwitch = [] ∧
    ¬ Refines
        (exec (readUB permissiveRejectInvalid deadNicheEnum) deadNicheEnum.inhabitedTag
          (lastVariantTakesWildcard 3 deadNicheEnum.inhabitedTag deadNicheSwitch) 1)
        (exec (readUB permissiveRejectInvalid deadNicheEnum) deadNicheEnum.inhabitedTag
          deadNicheSwitch 1) ∧
    remainingAllowed 4 (Enum.inhabitedTag [true, false, true, true])
        ⟨[(0, .goto 1), (2, .goto 2)], .goto 3⟩ = [3] ∧
    ¬ Refines
        (exec (readUB permissiveRejectInvalid [true, false, true, true])
          (Enum.inhabitedTag [true, false, true, true])
          (lastVariantTakesWildcard 4 (Enum.inhabitedTag [true, false, true, true])
            ⟨[(0, .goto 1), (2, .goto 2)], .goto 3⟩) 1)
        (exec (readUB permissiveRejectInvalid [true, false, true, true])
          (Enum.inhabitedTag [true, false, true, true])
          ⟨[(0, .goto 1), (2, .goto 2)], .goto 3⟩ 1) := by
  refine ⟨by decide, ?_, by decide, ?_⟩ <;> (unfold Refines; decide)

/-- Refutation of the reading "the specialization retargets exactly the non-allowed tags to
`unreachable`": on `deadNicheEnum`, the switch with no explicit arm and wildcard `goto 7` has two allowed
tags without an explicit arm, so the specialization leaves the wildcard unchanged and the
non-allowed tag `1` keeps the target `goto 7`. -/
theorem refuted_specializeSwitch_retargets_every_nonAllowed_tag :
    allowedTag 3 deadNicheEnum.inhabitedTag 1 = false ∧
    (specializeSwitch 3 deadNicheEnum.inhabitedTag ⟨[], .goto 7⟩).target 1 = .goto 7 := by decide

/-- Refutation of the reading "on an all-inhabited enum the specialization has nothing to change":
on `[true, true, true]` it changes `orderingSwitch` (the wildcard becomes `unreachable` after the
last variant takes its target). -/
theorem refuted_allInhabited_specializeEnum_changes_nothing :
    specializeEnum [true, true, true] orderingSwitch ≠ orderingSwitch := by decide

/-! ## R5: named discriminant semantics -/

/-- R5-reject (corollary of R5-eq). Under `rejectBoth`, the enum-derived specialization has the
same outcome as the original on every enum, switch and tag. -/
theorem runSwitch_specializeEnum_eq_of_rejectBoth (E : Enum) (sw : Switch) (t : Nat) :
    runSwitch rejectBoth E (specializeEnum E sw) t = runSwitch rejectBoth E sw t :=
  exec_specializeSwitch_eq_of_readUB_of_not_allowedTag E.length E.inhabitedTag _ _
    (readUB_rejectBoth_of_allowedTag_eq_false E) sw t

/-- R5-valid. For every discriminant semantics `D`: the enum-derived specialization refines the
original on every enum, every switch and every valid tag (`t < E.length`) iff `D` rejects
uninhabited-variant tags. -/
theorem specializeEnum_refines_validTags_iff_rejectUninhabited (D : DiscrSem) :
    (∀ (E : Enum) (sw : Switch) (t : Nat), t < E.length →
        Refines (runSwitch D E (specializeEnum E sw) t) (runSwitch D E sw t)) ↔
      D.uninh = .rejectUninhabited := by
  constructor
  · intro h
    cases hu : D.uninh with
    | rejectUninhabited => rfl
    | permissive =>
      have href := h [false] ⟨[], .goto 0⟩ 0 (by decide)
      cases hi : D.invalid <;>
        simp [runSwitch, exec, readUB, hu, specializeEnum, specializeSwitch,
              pruneArms, lastVariantTakesWildcard, remainingAllowed, Switch.target,
              runArm, Refines, Enum.inhabitedTag] at href
  · intro hu E sw t ht
    cases hinh : E.inhabitedTag t with
    | false =>
      exact Or.inl (by simp [runSwitch, exec, readUB, ht, hu, hinh])
    | true =>
      have hall : allowedTag E.length E.inhabitedTag t = true := by
        simp [allowedTag, ht, hinh]
      exact Or.inr (by
        unfold runSwitch exec specializeEnum specializeSwitch
        rw [target_lastVariant_of_allowed _ _ _ _ hall, target_pruneArms_of_allowed _ _ _ _ hall])

/-- R5-permissive. For every invalid-tag choice `inv` and every enum `E`, under the permissive
uninhabited-tag semantics: the enum-derived specialization refines the original on every switch
and every valid tag iff every variant of `E` is inhabited. -/
theorem specializeEnum_refines_validTags_permissive_iff_allInhabited (inv : InvalidRead) (E : Enum) :
    (∀ (sw : Switch) (t : Nat), t < E.length →
        Refines (runSwitch ⟨.permissive, inv⟩ E (specializeEnum E sw) t)
          (runSwitch ⟨.permissive, inv⟩ E sw t)) ↔
      ∀ t, t < E.length → E.inhabitedTag t = true := by
  constructor
  · intro h t ht
    cases hinh : E.inhabitedTag t with
    | true => rfl
    | false =>
      have href := h ⟨[(t, .goto 0)], .goto 0⟩ t ht
      have hall : allowedTag E.length E.inhabitedTag t = false := by simp [allowedTag, hinh]
      have hsrc : runSwitch ⟨.permissive, inv⟩ E ⟨[(t, .goto 0)], .goto 0⟩ t = .ret 0 := by
        simp [runSwitch, exec, readUB, ht, Switch.target, runArm]
      have htgt : runSwitch ⟨.permissive, inv⟩ E (specializeEnum E ⟨[(t, .goto 0)], .goto 0⟩) t =
          .ub := by
        unfold runSwitch exec specializeEnum specializeSwitch lastVariantTakesWildcard Switch.target
          pruneArms
        simp only [readUB, ht, ↓reduceIte, Bool.false_eq_true, List.map_cons, List.map_nil, hall]
        cases remainingAllowed E.length E.inhabitedTag _ with
        | nil => simp [runArm]
        | cons j rs => cases rs <;> simp [runArm]
      rw [hsrc, htgt] at href
      simp [Refines] at href
  · intro hall sw t ht
    have ha : allowedTag E.length E.inhabitedTag t = true := by
      simp [allowedTag, ht, hall t ht]
    exact Or.inr (by
      unfold runSwitch exec specializeEnum specializeSwitch
      rw [target_lastVariant_of_allowed _ _ _ _ ha, target_pruneArms_of_allowed _ _ _ _ ha])

/-- R5-counterexample. A dead niche value reaches the switch: in the toy niche encoding
`exampleNiche`, stored value `2` decodes to variant `1` of `deadNicheEnum`, which is uninhabited.
Under `permissiveRejectInvalid` the original switch continues normally on it, and the specialized
switch is undefined behaviour. -/
theorem deadNiche_permissive_specializeEnum_introduces_ub :
    exampleNiche.decode 2 = 1 ∧ deadNicheEnum.inhabitedTag 1 = false ∧
    runSwitch permissiveRejectInvalid deadNicheEnum deadNicheSwitch (exampleNiche.decode 2) = .ret 1 ∧
    runSwitch permissiveRejectInvalid deadNicheEnum (specializeEnum deadNicheEnum deadNicheSwitch)
      (exampleNiche.decode 2) = .ub := by decide

/-- R5-counterexample (shape 2). The documented "last remaining variant takes the wildcard"
transformation on an enum `[true, false, true, true]` whose variant `1` is uninhabited: the
uninhabited tag reaches the old wildcard target in the original and `unreachable` after the
rewrite, under `permissiveRejectInvalid`. -/
theorem lastVariant_permissive_introduces_ub :
    runSwitch permissiveRejectInvalid [true, false, true, true] ⟨[(0, .goto 1), (2, .goto 2)], .goto 3⟩ 1
      = .ret 3 ∧
    runSwitch permissiveRejectInvalid [true, false, true, true]
      (specializeEnum [true, false, true, true] ⟨[(0, .goto 1), (2, .goto 2)], .goto 3⟩) 1 = .ub := by
  decide

/-- R5 positive control: under `permissiveRejectInvalid`, on the all-inhabited three-variant enum,
the specialization of `orderingSwitch` has the same outcome as the original on every valid tag. -/
theorem permissive_allInhabited_orderingSwitch_same :
    ∀ t, t < 3 → runSwitch permissiveRejectInvalid [true, true, true]
        (specializeEnum [true, true, true] orderingSwitch) t =
      runSwitch permissiveRejectInvalid [true, true, true] orderingSwitch t := by decide

/-- Fixed-switch escape hatch: `usePayloadSwitch` sends the uninhabited tag `1` of `deadNicheEnum`
to an arm that uses the payload. Under `permissiveRejectInvalid` the read of tag `1` is defined,
the specialization changes the switch, and it refines the original on every tag. -/
theorem usePayloadSwitch_permissive_specializeEnum_refines :
    specializeEnum deadNicheEnum usePayloadSwitch ≠ usePayloadSwitch ∧
    readUB permissiveRejectInvalid deadNicheEnum 1 = false ∧
    ∀ t, Refines
      (runSwitch permissiveRejectInvalid deadNicheEnum (specializeEnum deadNicheEnum usePayloadSwitch) t)
      (runSwitch permissiveRejectInvalid deadNicheEnum usePayloadSwitch t) := by
  refine ⟨by decide, by decide, ?_⟩
  intro t
  match t with
  | 0 => exact Or.inr (by decide)
  | 1 => exact Or.inl (by decide)
  | 2 => exact Or.inr (by decide)
  | k + 3 =>
    have hk : ¬ (k + 3 < 3) := by omega
    exact Or.inl (by simp [runSwitch, exec, readUB, permissiveRejectInvalid, deadNicheEnum, hk])

/-! ## R6: invalid tags -/

/-- R6-all. For every discriminant semantics `D`: the enum-derived specialization refines the
original on every enum, switch and tag (valid or invalid) iff `D` rejects both uninhabited-variant
tags and invalid tags. -/
theorem specializeEnum_refines_allTags_iff_rejectUninhabited_and_rejectInvalid (D : DiscrSem) :
    (∀ (E : Enum) (sw : Switch) (t : Nat),
        Refines (runSwitch D E (specializeEnum E sw) t) (runSwitch D E sw t)) ↔
      D.uninh = .rejectUninhabited ∧ D.invalid = .rejectInvalid := by
  constructor
  · intro h
    refine ⟨(specializeEnum_refines_validTags_iff_rejectUninhabited D).mp
      (fun E sw t _ => h E sw t), ?_⟩
    cases hi : D.invalid with
    | rejectInvalid => rfl
    | passThrough =>
      have href := h [true] ⟨[], .goto 0⟩ 1
      cases hu : D.uninh <;>
        simp [runSwitch, exec, readUB, hi, specializeEnum, specializeSwitch,
              pruneArms, lastVariantTakesWildcard, remainingAllowed, Switch.target,
              runArm, Refines, Enum.inhabitedTag] at href
  · rintro ⟨hu, hi⟩ E sw t
    have hD : D = rejectBoth := by cases D; simp_all [rejectBoth]
    rw [hD]
    exact Or.inr (runSwitch_specializeEnum_eq_of_rejectBoth E sw t)

/-- R6-counterexample. Under a semantics that rejects uninhabited-variant tags but passes invalid
tags through to the switch (where they take the wildcard), the specialization of a switch with no
explicit arm and wildcard `goto 0`, on the one-variant enum `[true]`, turns the invalid tag `1` from
normal continuation into undefined behaviour. -/
theorem invalidTag_passThrough_specializeEnum_introduces_ub :
    runSwitch ⟨.rejectUninhabited, .passThrough⟩ [true] ⟨[], .goto 0⟩ 1 = .ret 0 ∧
    runSwitch ⟨.rejectUninhabited, .passThrough⟩ [true] (specializeEnum [true] ⟨[], .goto 0⟩) 1
      = .ub := by decide

/-- R6 non-vacuity: under `rejectBoth`, the specialization of `deadNicheSwitch` on
`deadNicheEnum` changes the switch and has the same outcome as the original on tags `0..4`. -/
theorem rejectBoth_deadNicheSwitch_same :
    specializeEnum deadNicheEnum deadNicheSwitch ≠ deadNicheSwitch ∧
    ∀ t, t < 5 → runSwitch rejectBoth deadNicheEnum (specializeEnum deadNicheEnum deadNicheSwitch) t =
      runSwitch rejectBoth deadNicheEnum deadNicheSwitch t := by decide

end Toy.DropScope
