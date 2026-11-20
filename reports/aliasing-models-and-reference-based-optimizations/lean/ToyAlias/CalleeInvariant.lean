import ToyAlias.Callee

/-!
# An invariant of unknown code around a freshly reborrowed reference

Proof infrastructure for the refinement theorems of `ToyAlias.Optimizations`.

After the function-entry reborrow `x := retag a p prot` with `p = unique` or
`p = sharedRO`, the new item `⟨p, x, prot⟩` is on top of the stack. `Inv` describes
what unknown code can do to it: either the item is still present, the stored value is
unchanged, and only `sharedRO` items with other tags lie above it; or (only without a
protector, and only when no older item carries the tag `x`) no item with tag `x` is left
at all. `inv_runCallee` shows that every returning callee execution preserves `Inv`,
and `read_at_inv_good` shows what a later read through `x` returns in each case.
`runCallee_val_indep_under_protected_unique` shows that, below a protected `unique` item
whose tag the callee does not hold, a callee execution does not depend on the stored
value.

These declarations are used only inside proofs; none of them is a published result.
-/

namespace Toy.Alias.CalleeInv

open Toy.Alias

/-! ## Helper lemmas on `findGranting` and `accessStack` -/

theorem findGranting_none_skip {k : AccessKind} {t : Tag} {s : List Item}
    (h : findGranting k t s = none) :
    ∀ i ∈ s, ¬ (i.tag = t ∧ i.perm.grants k = true) := by
  induction s with
  | nil => intro _ hm; cases hm
  | cons j rest ih =>
    unfold findGranting at h
    split at h
    · cases h
    · rename_i hc
      cases hfg : findGranting k t rest with
      | some res => rcases res with ⟨a', g', b'⟩; simp [hfg] at h
      | none =>
        intro i hi
        cases hi with
        | head => exact hc
        | tail _ hm => exact ih hfg i hm

theorem findGranting_append_skip {k : AccessKind} {t : Tag} (pre suf : List Item)
    (hskip : ∀ i ∈ pre, ¬ (i.tag = t ∧ i.perm.grants k = true)) :
    findGranting k t (pre ++ suf) =
      (findGranting k t suf).map fun (a, g, b) => (pre ++ a, g, b) := by
  induction pre with
  | nil =>
    simp only [List.nil_append]
    cases findGranting k t suf <;> rfl
  | cons i pre ih =>
    have hi : ¬ (i.tag = t ∧ i.perm.grants k = true) := hskip i (List.mem_cons_self ..)
    have hrest : ∀ j ∈ pre, ¬ (j.tag = t ∧ j.perm.grants k = true) :=
      fun j hj => hskip j (List.mem_cons_of_mem i hj)
    rw [List.cons_append, findGranting_cons_skip hi, ih hrest]
    cases findGranting k t suf <;> rfl

theorem findGranting_append_hit {k : AccessKind} {t : Tag} (pre suf : List Item) (g : Item)
    (hskip : ∀ i ∈ pre, ¬ (i.tag = t ∧ i.perm.grants k = true))
    (hhit : g.tag = t ∧ g.perm.grants k = true) :
    findGranting k t (pre ++ g :: suf) = some (pre, g, suf) := by
  rw [findGranting_append_skip pre (g :: suf) hskip]
  simp [findGranting, hhit]

theorem findGranting_append_in_pre {k : AccessKind} {t : Tag} (pre suf : List Item)
    {a b : List Item} {g : Item}
    (h : findGranting k t pre = some (a, g, b)) :
    findGranting k t (pre ++ suf) = some (a, g, b ++ suf) := by
  induction pre generalizing a with
  | nil => simp [findGranting] at h
  | cons i rest ih =>
    unfold findGranting at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp [findGranting, hc]
    · rename_i hc
      cases hfg : findGranting k t rest with
      | none => simp [hfg] at h
      | some res =>
        rcases res with ⟨a', g', b'⟩
        simp only [hfg, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp [findGranting, hc, ih hfg]

theorem all_sharedRO_read_no_invalid (l : List Item) (h : ∀ i ∈ l, i.perm = .sharedRO) :
    l.any (fun i => invalidatedBy .read i && i.prot) = false ∧
    l.filter (fun i => !invalidatedBy .read i) = l := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons i rest ih =>
    have hi : i.perm = .sharedRO := h i (List.mem_cons_self ..)
    have hr := ih (fun j hj => h j (List.mem_cons_of_mem i hj))
    have hinv : invalidatedBy .read i = false := by simp [invalidatedBy, hi]
    constructor
    · rw [List.any_cons, hinv, hr.1]; rfl
    · rw [List.filter_cons, hinv, hr.2]; rfl

theorem filter_not_invalidatedBy_write (l : List Item) :
    l.filter (fun i => !invalidatedBy .write i) = [] := by
  induction l with
  | nil => rfl
  | cons i rest ih => rw [List.filter_cons]; exact ih


theorem accessStack_protUniqueHead_none {k : AccessKind} {t x : Tag} {rest : List Item}
    (hne : t ≠ x) :
    accessStack k t (⟨.unique, x, true⟩ :: rest) = none := by
  unfold accessStack
  have h1 : ¬ (({ perm := .unique, tag := x, prot := true } : Item).tag = t ∧
      Perm.unique.grants k = true) := fun h => hne h.1.symm
  rw [findGranting_cons_skip h1]
  cases findGranting k t rest with
  | none => rfl
  | some res =>
    rcases res with ⟨ab, g, bl⟩
    cases k <;> simp [invalidatedBy]

theorem insertAboveGranting_protUniqueHead {t x : Tag} {new : Item} {rest : List Item}
    (hne : t ≠ x) :
    insertAboveGranting .write t new (⟨.unique, x, true⟩ :: rest) =
      (insertAboveGranting .write t new rest).map (⟨.unique, x, true⟩ :: ·) := by
  unfold insertAboveGranting
  have h1 : ¬ (({ perm := .unique, tag := x, prot := true } : Item).tag = t ∧
      Perm.unique.grants .write = true) := fun h => hne h.1.symm
  rw [findGranting_cons_skip h1]
  cases findGranting .write t rest <;> rfl

/-! ## The invariant and its preservation by unknown code -/

/-- The invariant for the read-elimination and read-deferral proofs. `x` is the tag of
the entry reborrow, `p` and `prot` its permission and protector flag, `v₀` the stored
value at the reborrow, `env` the callee's current tag environment. The flag `unpassed`
records that the callee does not hold `x`; the flag `fresh` records that no older item
carries the tag `x`. Either the item `⟨p, x, prot⟩` is still in the stack with only
`sharedRO` items carrying other tags above it and the value is still `v₀`, or (without a
protector, with `fresh`) no item with tag `x` remains. -/
def Inv (p : Perm) (prot : Bool) (x : Tag) (v₀ : Nat) (unpassed fresh : Bool)
    (env : List Tag) (m : Mem) : Prop :=
  (m.val = v₀ ∧ x < m.next ∧ (unpassed = true → x ∉ env) ∧
    ∃ ab bl, m.stack = ab ++ ⟨p, x, prot⟩ :: bl ∧
      (∀ i ∈ ab, i.perm = .sharedRO ∧ i.tag ≠ x) ∧
      (fresh = true → ∀ i ∈ bl, i.tag ≠ x))
  ∨
  (prot = false ∧ fresh = true ∧ x < m.next ∧ ∀ i ∈ m.stack, i.tag ≠ x)

theorem inv_step_read {p : Perm} {prot unpassed fresh : Bool} {x v₀ t : Tag} {env : List Tag}
    {m m' : Mem} {v : Nat}
    (hp : p ≠ .sharedRW) (hneed : p = .unique → unpassed = true)
    (hf : fresh = true ∨ prot = true)
    (hinv : Inv p prot x v₀ unpassed fresh env m)
    (hread : Toy.Alias.read t m = some (v, m')) :
    Inv p prot x v₀ unpassed fresh env m' := by
  unfold Toy.Alias.read at hread
  cases ha : accessStack .read t m.stack with
  | none => simp [ha] at hread
  | some s' =>
    simp only [ha, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hread
    obtain ⟨rfl, rfl⟩ := hread
    rcases hinv with ⟨hval, hnxt, hup, ab, bl, hst, hab, hbl⟩ | ⟨hpf, hfr, hnxt, hno⟩
    · rw [hst] at ha
      cases hfg_ab : findGranting .read t ab with
      | some res =>
        rcases res with ⟨ab1, g, ab2⟩
        have hfg := findGranting_append_in_pre ab (⟨p, x, prot⟩ :: bl) hfg_ab
        obtain ⟨hab_eq, _, _, _⟩ := findGranting_spec hfg_ab
        have hnoinv := all_sharedRO_read_no_invalid ab1
          (fun i hi => (hab i (hab_eq ▸ List.mem_append_left _ hi)).1)
        unfold accessStack at ha
        simp only [hfg, hnoinv.1, Bool.false_eq_true, ite_false, hnoinv.2, Option.some.injEq] at ha
        have hs'_eq : s' = ab ++ ⟨p, x, prot⟩ :: bl := by
          rw [← ha, hab_eq]; simp [List.append_assoc]
        exact Or.inl ⟨hval, hnxt, hup, ab, bl, hs'_eq, hab, hbl⟩
      | none =>
        have hskip_ab := findGranting_none_skip hfg_ab
        by_cases htx : x = t
        · have hhit : (⟨p, x, prot⟩ : Item).tag = t ∧ p.grants .read = true :=
            ⟨htx, by cases p <;> rfl⟩
          have hfg' := findGranting_append_hit ab bl ⟨p, x, prot⟩ hskip_ab hhit
          have hnoinv := all_sharedRO_read_no_invalid ab (fun i hi => (hab i hi).1)
          unfold accessStack at ha
          simp only [hfg', hnoinv.1, Bool.false_eq_true, ite_false, hnoinv.2, Option.some.injEq] at ha
          exact Or.inl ⟨hval, hnxt, hup, ab, bl, ha.symm, hab, hbl⟩
        · have hskip_x : ¬ ((⟨p, x, prot⟩ : Item).tag = t ∧ p.grants .read = true) :=
            fun h => htx h.1
          have hfg := findGranting_append_skip (ab ++ [⟨p, x, prot⟩]) bl (by
            intro i hi; simp only [List.mem_append, List.mem_singleton] at hi
            rcases hi with h1 | rfl; exact hskip_ab i h1; exact hskip_x)
          have happ : ab ++ ⟨p, x, prot⟩ :: bl = (ab ++ [⟨p, x, prot⟩]) ++ bl := by simp
          rw [happ] at ha
          unfold accessStack at ha
          rw [hfg] at ha
          cases hfg_bl : findGranting .read t bl with
          | none => simp [hfg_bl] at ha
          | some res =>
            rcases res with ⟨bl1, g, bl2⟩
            obtain ⟨hbl_eq, _, _, _⟩ := findGranting_spec hfg_bl
            simp only [hfg_bl, Option.map_some] at ha
            cases p with
            | sharedRW => exact absurd rfl hp
            | sharedRO =>
              split at ha
              · cases ha
              · simp only [Option.some.injEq] at ha
                subst ha
                have hnoinv := all_sharedRO_read_no_invalid ab (fun i hi => (hab i hi).1)
                have hf_eq : ((ab ++ [({ perm := .sharedRO, tag := x, prot := prot } : Item)]) ++ bl1).filter
                      (fun i => !invalidatedBy .read i) =
                    ab ++ ⟨.sharedRO, x, prot⟩ :: bl1.filter (fun i => !invalidatedBy .read i) := by
                  rw [List.filter_append, List.filter_append, hnoinv.2]
                  simp [invalidatedBy]
                refine Or.inl ⟨hval, hnxt, hup, ab,
                  bl1.filter (fun i => !invalidatedBy .read i) ++ g :: bl2,
                  by rw [hf_eq]; simp [List.append_assoc], hab, ?_⟩
                intro hfr i hi
                apply hbl hfr i
                rw [hbl_eq]
                simp only [List.mem_append, List.mem_filter, List.mem_cons] at hi ⊢
                rcases hi with ⟨h1, _⟩ | h1 | h2
                · exact Or.inl h1
                · exact Or.inr (Or.inl h1)
                · exact Or.inr (Or.inr h2)
            | unique =>
              cases prot with
              | true =>
                simp [List.any_append, invalidatedBy] at ha
              | false =>
                have hfr : fresh = true := by rcases hf with h | h; exact h; cases h
                split at ha
                · cases ha
                · simp only [Option.some.injEq] at ha
                  subst ha
                  refine Or.inr ⟨rfl, hfr, hnxt, ?_⟩
                  intro i hi
                  simp only [List.mem_append, List.mem_filter, List.mem_cons] at hi
                  rcases hi with ⟨h1, hnotu⟩ | rfl | h2
                  · rcases h1 with (hab_m | rfl | hnil) | hbl1
                    · exact (hab i hab_m).2
                    · simp [invalidatedBy] at hnotu
                    · cases hnil
                    · exact hbl hfr i (by rw [hbl_eq]; exact List.mem_append_left _ hbl1)
                  · exact hbl hfr i (by rw [hbl_eq]; exact List.mem_append_right _ (List.mem_cons_self ..))
                  · exact hbl hfr i (by rw [hbl_eq]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h2))
    · exact Or.inr ⟨hpf, hfr, hnxt, accessStack_sublist_prop hno ha⟩

theorem inv_step_write {p : Perm} {prot unpassed fresh : Bool} {x v₀ t v : Tag} {env : List Tag}
    {m m' : Mem}
    (hp : p ≠ .sharedRW) (hneed : p = .unique → unpassed = true)
    (hf : fresh = true ∨ prot = true)
    (hinv : Inv p prot x v₀ unpassed fresh env m) (ht : t ∈ env)
    (hwrite : Toy.Alias.write t v m = some m') :
    Inv p prot x v₀ unpassed fresh env m' := by
  unfold Toy.Alias.write at hwrite
  cases ha : accessStack .write t m.stack with
  | none => simp [ha] at hwrite
  | some s' =>
    simp only [ha, Option.map_some, Option.some.injEq] at hwrite
    subst hwrite
    rcases hinv with ⟨hval, hnxt, hup, ab, bl, hst, hab, hbl⟩ | ⟨hpf, hfr, hnxt, hno⟩
    · rw [hst] at ha
      have hskip_ab : ∀ i ∈ ab, ¬ (i.tag = t ∧ i.perm.grants .write = true) := fun i hi hc => by
        rw [(hab i hi).1] at hc; simp [Perm.grants] at hc
      have hskip_x : ¬ ((⟨p, x, prot⟩ : Item).tag = t ∧ p.grants .write = true) := by
        intro ⟨htx, hgw⟩
        cases p with
        | sharedRW => exact absurd rfl hp
        | sharedRO => simp [Perm.grants] at hgw
        | unique => dsimp at htx; subst htx; exact hup (hneed rfl) ht
      have hfg := findGranting_append_skip (ab ++ [⟨p, x, prot⟩]) bl (by
        intro i hi; simp only [List.mem_append, List.mem_singleton] at hi
        rcases hi with h1 | rfl; exact hskip_ab i h1; exact hskip_x)
      have happ : ab ++ ⟨p, x, prot⟩ :: bl = (ab ++ [⟨p, x, prot⟩]) ++ bl := by simp
      rw [happ] at ha
      unfold accessStack at ha
      rw [hfg] at ha
      cases hfg_bl : findGranting .write t bl with
      | none => simp [hfg_bl] at ha
      | some res =>
        rcases res with ⟨bl1, g, bl2⟩
        obtain ⟨hbl_eq, _, _, _⟩ := findGranting_spec hfg_bl
        simp only [hfg_bl, Option.map_some] at ha
        cases prot with
        | true =>
          simp [List.any_append, invalidatedBy] at ha
        | false =>
          have hfr : fresh = true := by rcases hf with h | h; exact h; cases h
          split at ha
          · cases ha
          · simp only [Option.some.injEq] at ha
            subst ha
            rw [filter_not_invalidatedBy_write, List.nil_append]
            refine Or.inr ⟨rfl, hfr, hnxt, ?_⟩
            intro i hi
            exact hbl hfr i (by rw [hbl_eq]; exact List.mem_append_right _ hi)
    · exact Or.inr ⟨hpf, hfr, hnxt, accessStack_sublist_prop hno ha⟩

theorem inv_step_retag {p pc : Perm} {prot unpassed fresh : Bool} {x v₀ t t' : Tag} {env : List Tag}
    {m m' : Mem}
    (hp : p ≠ .sharedRW) (hneed : p = .unique → unpassed = true)
    (hf : fresh = true ∨ prot = true)
    (hinv : Inv p prot x v₀ unpassed fresh env m) (ht : t ∈ env)
    (hrt : retag t pc false m = some (t', m')) :
    Inv p prot x v₀ unpassed fresh (env ++ [t']) m' := by
  have ht'_eq : t' = m.next := retag_tag hrt
  subst ht'_eq
  cases pc with
  | sharedRW =>
    unfold retag at hrt
    simp only at hrt
    cases hins : insertAboveGranting .write t ⟨.sharedRW, m.next, false⟩ m.stack with
    | none => simp [hins] at hrt
    | some s' =>
      simp only [hins, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrt
      obtain ⟨_, rfl⟩ := hrt
      rcases hinv with ⟨hval, hnxt, hup, ab, bl, hst, hab, hbl⟩ | ⟨hpf, hfr, hnxt, hno⟩
      · rw [hst] at hins
        have hskip_ab : ∀ i ∈ ab, ¬ (i.tag = t ∧ i.perm.grants .write = true) := fun i hi hc => by
          rw [(hab i hi).1] at hc; simp [Perm.grants] at hc
        have hskip_x : ¬ ((⟨p, x, prot⟩ : Item).tag = t ∧ p.grants .write = true) := by
          intro ⟨htx, hgw⟩
          cases p with
          | sharedRW => exact absurd rfl hp
          | sharedRO => simp [Perm.grants] at hgw
          | unique => dsimp at htx; subst htx; exact hup (hneed rfl) ht
        have hfg := findGranting_append_skip (ab ++ [⟨p, x, prot⟩]) bl (by
          intro i hi; simp only [List.mem_append, List.mem_singleton] at hi
          rcases hi with h1 | rfl; exact hskip_ab i h1; exact hskip_x)
        have happ : ab ++ ⟨p, x, prot⟩ :: bl = (ab ++ [⟨p, x, prot⟩]) ++ bl := by simp
        rw [happ] at hins
        unfold insertAboveGranting at hins
        rw [hfg] at hins
        cases hfg_bl : findGranting .write t bl with
        | none => simp [hfg_bl] at hins
        | some res =>
          rcases res with ⟨bl1, g, bl2⟩
          obtain ⟨hbl_eq, _, _, _⟩ := findGranting_spec hfg_bl
          simp only [hfg_bl, Option.map_some, Option.some.injEq] at hins
          subst hins
          refine Or.inl ⟨hval, Nat.lt_succ_of_lt hnxt, ?_, ab,
            bl1 ++ ⟨.sharedRW, m.next, false⟩ :: g :: bl2,
            by simp [List.append_assoc], hab, ?_⟩
          · intro hu hmem
            simp only [List.mem_append, List.mem_singleton] at hmem
            rcases hmem with h1 | h2
            · exact hup hu h1
            · exact Nat.ne_of_lt hnxt h2
          · intro hfr i hi
            simp only [List.mem_append, List.mem_cons] at hi
            rcases hi with h1 | rfl | rfl | h2
            · exact hbl hfr i (by rw [hbl_eq]; exact List.mem_append_left _ h1)
            · exact Nat.ne_of_gt hnxt
            · exact hbl hfr i (by rw [hbl_eq]; exact List.mem_append_right _ (List.mem_cons_self ..))
            · exact hbl hfr i (by rw [hbl_eq]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h2))
      · unfold insertAboveGranting at hins
        cases hfg : findGranting .write t m.stack with
        | none => simp [hfg] at hins
        | some res =>
          rcases res with ⟨ab, g, bl⟩
          obtain ⟨hs, _, _, _⟩ := findGranting_spec hfg
          simp only [hfg, Option.map_some, Option.some.injEq] at hins
          subst hins
          refine Or.inr ⟨hpf, hfr, Nat.lt_succ_of_lt hnxt, ?_⟩
          intro i hi
          simp only [List.mem_append, List.mem_cons] at hi
          rcases hi with h1 | rfl | rfl | h2
          · exact hno i (by rw [hs]; exact List.mem_append_left _ h1)
          · exact Nat.ne_of_gt hnxt
          · exact hno i (by rw [hs]; exact List.mem_append_right _ (List.mem_cons_self ..))
          · exact hno i (by rw [hs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h2))
  | unique =>
    unfold retag at hrt
    simp only at hrt
    cases ha : accessStack .write t m.stack with
    | none => simp [ha] at hrt
    | some s' =>
      simp only [ha, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrt
      obtain ⟨_, rfl⟩ := hrt
      rcases hinv with ⟨hval, hnxt, hup, ab, bl, hst, hab, hbl⟩ | ⟨hpf, hfr, hnxt, hno⟩
      · rw [hst] at ha
        have hskip_ab : ∀ i ∈ ab, ¬ (i.tag = t ∧ i.perm.grants .write = true) := fun i hi hc => by
          rw [(hab i hi).1] at hc; simp [Perm.grants] at hc
        have hskip_x : ¬ ((⟨p, x, prot⟩ : Item).tag = t ∧ p.grants .write = true) := by
          intro ⟨htx, hgw⟩
          cases p with
          | sharedRW => exact absurd rfl hp
          | sharedRO => simp [Perm.grants] at hgw
          | unique => dsimp at htx; subst htx; exact hup (hneed rfl) ht
        have hfg := findGranting_append_skip (ab ++ [⟨p, x, prot⟩]) bl (by
          intro i hi; simp only [List.mem_append, List.mem_singleton] at hi
          rcases hi with h1 | rfl; exact hskip_ab i h1; exact hskip_x)
        have happ : ab ++ ⟨p, x, prot⟩ :: bl = (ab ++ [⟨p, x, prot⟩]) ++ bl := by simp
        rw [happ] at ha
        unfold accessStack at ha
        rw [hfg] at ha
        cases hfg_bl : findGranting .write t bl with
        | none => simp [hfg_bl] at ha
        | some res =>
          rcases res with ⟨bl1, g, bl2⟩
          obtain ⟨hbl_eq, _, _, _⟩ := findGranting_spec hfg_bl
          simp only [hfg_bl, Option.map_some] at ha
          cases prot with
          | true =>
            simp [List.any_append, invalidatedBy] at ha
          | false =>
            have hfr : fresh = true := by rcases hf with h | h; exact h; cases h
            split at ha
            · cases ha
            · simp only [Option.some.injEq] at ha
              subst ha
              rw [filter_not_invalidatedBy_write, List.nil_append]
              refine Or.inr ⟨rfl, hfr, Nat.lt_succ_of_lt hnxt, ?_⟩
              intro i hi
              cases hi with
              | head => exact Nat.ne_of_gt hnxt
              | tail _ hm => exact hbl hfr i (by rw [hbl_eq]; exact List.mem_append_right _ hm)
      · refine Or.inr ⟨hpf, hfr, Nat.lt_succ_of_lt hnxt, ?_⟩
        intro i hi
        cases hi with
        | head => exact Nat.ne_of_gt hnxt
        | tail _ hm => exact accessStack_sublist_prop hno ha i hm
  | sharedRO =>
    unfold retag at hrt
    simp only at hrt
    cases ha : accessStack .read t m.stack with
    | none => simp [ha] at hrt
    | some s' =>
      simp only [ha, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrt
      obtain ⟨_, rfl⟩ := hrt
      have hrd : Toy.Alias.read t m = some (m.val, { m with stack := s' }) := by
        simp [Toy.Alias.read, ha]
      have hinv' := inv_step_read hp hneed hf hinv hrd
      rcases hinv' with ⟨hval, hnxt, hup, ab, bl, hst, hab, hbl⟩ | ⟨hpf, hfr, hnxt, hno⟩
      · refine Or.inl ⟨hval, Nat.lt_succ_of_lt hnxt, ?_, ⟨.sharedRO, m.next, false⟩ :: ab, bl,
          by simpa using congrArg (({ perm := .sharedRO, tag := m.next, prot := false } : Item) :: ·) hst, ?_, hbl⟩
        · intro hu hmem
          simp only [List.mem_append, List.mem_singleton] at hmem
          rcases hmem with h1 | h2
          · exact hup hu h1
          · exact Nat.ne_of_lt hnxt h2
        · intro i hi
          cases hi with
          | head => exact ⟨rfl, Nat.ne_of_gt hnxt⟩
          | tail _ hm => exact hab i hm
      · refine Or.inr ⟨hpf, hfr, Nat.lt_succ_of_lt hnxt, ?_⟩
        intro i hi
        cases hi with
        | head => exact Nat.ne_of_gt hnxt
        | tail _ hm => exact hno i hm

theorem inv_runCallee {p : Perm} {prot unpassed fresh : Bool} {x v₀ : Tag}
    (hp : p ≠ .sharedRW) (hneed : p = .unique → unpassed = true)
    (hf : fresh = true ∨ prot = true) :
    ∀ c env m obs m', Inv p prot x v₀ unpassed fresh env m →
      runCallee env c m = .done obs m' → ∃ env', Inv p prot x v₀ unpassed fresh env' m' := by
  intro c
  induction c with
  | nil =>
    intro env m obs m' hinv hrc
    simp [runCallee] at hrc; obtain ⟨_, rfl⟩ := hrc
    exact ⟨env, hinv⟩
  | cons op c ih =>
    intro env m obs m' hinv hrc
    cases op with
    | halt => simp [runCallee] at hrc
    | emit v =>
      simp only [runCallee] at hrc
      cases hrec : runCallee env c m with
      | ub => simp [hrec, Outcome.consObs] at hrc
      | halted _ => simp [hrec, Outcome.consObs] at hrc
      | done obs' m₂ =>
        simp only [hrec, Outcome.consObs, Outcome.done.injEq] at hrc
        obtain ⟨_, rfl⟩ := hrc
        exact ih env m obs' m₂ hinv hrec
    | read i =>
      unfold runCallee at hrc
      cases hi : env[i]? with
      | none => simp [hi, liftO] at hrc
      | some t =>
        simp only [hi, liftO] at hrc
        cases hr : Toy.Alias.read t m with
        | none => simp [hr] at hrc
        | some vm =>
          rcases vm with ⟨v, m₁⟩
          simp only [hr] at hrc
          cases hrec : runCallee env c m₁ with
          | ub => simp [hrec, Outcome.consObs] at hrc
          | halted _ => simp [hrec, Outcome.consObs] at hrc
          | done obs' m₂ =>
            simp only [hrec, Outcome.consObs, Outcome.done.injEq] at hrc
            obtain ⟨_, rfl⟩ := hrc
            exact ih env m₁ obs' m₂ (inv_step_read hp hneed hf hinv hr) hrec
    | write i v =>
      unfold runCallee at hrc
      cases hi : env[i]? with
      | none => simp [hi, liftO] at hrc
      | some t =>
        simp only [hi, liftO] at hrc
        cases hw : Toy.Alias.write t v m with
        | none => simp [hw] at hrc
        | some m₁ =>
          simp only [hw] at hrc
          exact ih env m₁ obs m'
            (inv_step_write hp hneed hf hinv (List.mem_of_getElem? hi) hw) hrc
    | retag i pc =>
      unfold runCallee at hrc
      cases hi : env[i]? with
      | none => simp [hi, liftO] at hrc
      | some t =>
        simp only [hi, liftO] at hrc
        cases hrt : retag t pc false m with
        | none => simp [hrt] at hrc
        | some tm =>
          rcases tm with ⟨t', m₁⟩
          simp only [hrt] at hrc
          exact ih (env ++ [t']) m₁ obs m'
            (inv_step_retag hp hneed hf hinv (List.mem_of_getElem? hi) hrt) hrc

theorem read_at_inv_good {p : Perm} {prot unpassed fresh : Bool} {x v₀ : Tag} {env : List Tag}
    {m : Mem} (hinv : Inv p prot x v₀ unpassed fresh env m) :
    (Toy.Alias.read x m = some (v₀, m)) ∨ (prot = false ∧ Toy.Alias.read x m = none) := by
  rcases hinv with ⟨hval, _, _, ab, bl, hst, hab, _⟩ | ⟨hpf, _, _, hno⟩
  · left
    have hskip : ∀ i ∈ ab, ¬ (i.tag = x ∧ i.perm.grants .read = true) :=
      fun i hi hc => (hab i hi).2 hc.1
    have hhit : (⟨p, x, prot⟩ : Item).tag = x ∧ p.grants .read = true :=
      ⟨rfl, by cases p <;> rfl⟩
    have hfg := findGranting_append_hit ab bl ⟨p, x, prot⟩ hskip hhit
    have hnoinv := all_sharedRO_read_no_invalid ab (fun i hi => (hab i hi).1)
    unfold Toy.Alias.read accessStack
    rw [hst, hfg]
    simp only [hnoinv.1, Bool.false_eq_true, ite_false, hnoinv.2, Option.map_some,
      Option.some.injEq, Prod.mk.injEq]
    cases m; simp_all
  · right
    refine ⟨hpf, ?_⟩
    unfold Toy.Alias.read accessStack
    have hnone : ∀ l : List Item, (∀ i ∈ l, i.tag ≠ x) → findGranting .read x l = none := by
      intro l hl
      induction l with
      | nil => rfl
      | cons i rest ih =>
        have h1 : ¬ (i.tag = x ∧ i.perm.grants .read = true) :=
          fun h => hl i (List.mem_cons_self ..) h.1
        rw [findGranting_cons_skip h1, ih (fun j hj => hl j (List.mem_cons_of_mem i hj))]
        rfl
    simp [hnone m.stack hno]

/-! ## Value-independence below a protected `unique` item -/

/-- Value-independence of `runCallee` below a protected `unique` item whose tag `x` the
callee does not hold: runs from two states that differ only in the stored value have the
same kind of outcome, the same observations, and (when they return) the same borrow stack
and tag counter, with the protected item still on top. -/
theorem runCallee_val_indep_under_protected_unique
    (c : List COp) (env : List Tag) (x : Tag) (v₁ v₂ : Nat) (rest : List Item) (nxt : Tag)
    (henv : x ∉ env) (hnext : x < nxt) :
    match runCallee env c ⟨v₁, ⟨.unique, x, true⟩ :: rest, nxt⟩,
          runCallee env c ⟨v₂, ⟨.unique, x, true⟩ :: rest, nxt⟩ with
    | .ub, .ub => True
    | .halted o1, .halted o2 => o1 = o2
    | .done o1 m1, .done o2 m2 => o1 = o2 ∧ m1.stack = m2.stack ∧ m1.next = m2.next ∧
        ∃ r, m1.stack = ⟨.unique, x, true⟩ :: r
    | _, _ => False := by
  induction c generalizing env rest nxt with
  | nil => exact ⟨rfl, rfl, rfl, rest, rfl⟩
  | cons op c ih =>
    cases op with
    | halt => exact rfl
    | emit v =>
      have hih := ih env rest nxt henv hnext
      simp only [runCallee]
      revert hih
      cases runCallee env c ⟨v₁, ⟨.unique, x, true⟩ :: rest, nxt⟩ <;>
        cases runCallee env c ⟨v₂, ⟨.unique, x, true⟩ :: rest, nxt⟩ <;>
        simp [Outcome.consObs]
    | read i =>
      unfold runCallee
      cases hi : env[i]? with
      | none => trivial
      | some t =>
        have hne : t ≠ x := fun heq => henv (heq ▸ List.mem_of_getElem? hi)
        have h1 : Toy.Alias.read t ⟨v₁, ⟨.unique, x, true⟩ :: rest, nxt⟩ = none := by
          unfold Toy.Alias.read; rw [accessStack_protUniqueHead_none hne]; rfl
        have h2 : Toy.Alias.read t ⟨v₂, ⟨.unique, x, true⟩ :: rest, nxt⟩ = none := by
          unfold Toy.Alias.read; rw [accessStack_protUniqueHead_none hne]; rfl
        simp [liftO, h1, h2]
    | write i v =>
      unfold runCallee
      cases hi : env[i]? with
      | none => trivial
      | some t =>
        have hne : t ≠ x := fun heq => henv (heq ▸ List.mem_of_getElem? hi)
        have h1 : Toy.Alias.write t v ⟨v₁, ⟨.unique, x, true⟩ :: rest, nxt⟩ = none := by
          unfold Toy.Alias.write; rw [accessStack_protUniqueHead_none hne]; rfl
        have h2 : Toy.Alias.write t v ⟨v₂, ⟨.unique, x, true⟩ :: rest, nxt⟩ = none := by
          unfold Toy.Alias.write; rw [accessStack_protUniqueHead_none hne]; rfl
        simp [liftO, h1, h2]
    | retag i p' =>
      cases p' with
      | unique =>
        unfold runCallee
        cases hi : env[i]? with
        | none => trivial
        | some t =>
          have hne : t ≠ x := fun heq => henv (heq ▸ List.mem_of_getElem? hi)
          have h1 : retag t .unique false ⟨v₁, ⟨.unique, x, true⟩ :: rest, nxt⟩ = none := by
            unfold retag; rw [accessStack_protUniqueHead_none hne]; rfl
          have h2 : retag t .unique false ⟨v₂, ⟨.unique, x, true⟩ :: rest, nxt⟩ = none := by
            unfold retag; rw [accessStack_protUniqueHead_none hne]; rfl
          simp [liftO, h1, h2]
      | sharedRO =>
        unfold runCallee
        cases hi : env[i]? with
        | none => trivial
        | some t =>
          have hne : t ≠ x := fun heq => henv (heq ▸ List.mem_of_getElem? hi)
          have h1 : retag t .sharedRO false ⟨v₁, ⟨.unique, x, true⟩ :: rest, nxt⟩ = none := by
            dsimp only [retag]; rw [accessStack_protUniqueHead_none hne]; rfl
          have h2 : retag t .sharedRO false ⟨v₂, ⟨.unique, x, true⟩ :: rest, nxt⟩ = none := by
            dsimp only [retag]; rw [accessStack_protUniqueHead_none hne]; rfl
          simp [liftO, h1, h2]
      | sharedRW =>
        unfold runCallee
        cases hi : env[i]? with
        | none => trivial
        | some t =>
          have hne : t ≠ x := fun heq => henv (heq ▸ List.mem_of_getElem? hi)
          have hrt : ∀ v, retag t .sharedRW false ⟨v, ⟨.unique, x, true⟩ :: rest, nxt⟩ =
              (insertAboveGranting .write t ⟨.sharedRW, nxt, false⟩ rest).map fun rest' =>
                (nxt, ⟨v, ⟨.unique, x, true⟩ :: rest', nxt + 1⟩) := by
            intro v; unfold retag
            simp only [insertAboveGranting_protUniqueHead hne]
            cases insertAboveGranting .write t ⟨.sharedRW, nxt, false⟩ rest <;> simp
          simp only [liftO, hrt]
          cases hins : insertAboveGranting .write t ⟨.sharedRW, nxt, false⟩ rest with
          | none => simp
          | some rest' =>
            simp only [Option.map_some]
            have henv' : x ∉ env ++ [nxt] := by
              simp only [List.mem_append, List.mem_singleton, not_or]
              exact ⟨henv, Nat.ne_of_lt hnext⟩
            exact ih (env ++ [nxt]) rest' (nxt + 1) henv' (Nat.lt_succ_of_lt hnext)

end Toy.Alias.CalleeInv
