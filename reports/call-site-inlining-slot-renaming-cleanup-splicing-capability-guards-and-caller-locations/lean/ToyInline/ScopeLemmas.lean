import ToyInline.Props

/-!
# Auxiliary list and scope-walk lemmas (fully proved)

Facts about `nth?`, `mapIdxFrom` and the scope walk on an appended table, used by the
caller-location and scope well-formedness results.
-/

namespace Toy.Inline

theorem nth?_append_left {α : Type} :
    ∀ (l₁ l₂ : List α) (i : Nat), i < l₁.length → nth? (l₁ ++ l₂) i = nth? l₁ i
  | [], _, _, h => by cases h
  | _ :: _, _, 0, _ => rfl
  | _ :: as, l₂, i + 1, h => nth?_append_left as l₂ i (Nat.lt_of_succ_lt_succ h)

theorem nth?_append_right {α : Type} :
    ∀ (l₁ l₂ : List α) (i : Nat), nth? (l₁ ++ l₂) (l₁.length + i) = nth? l₂ i
  | [], _, _ => by simp
  | _ :: as, l₂, i => by
    have h : (as.length + 1) + i = (as.length + i) + 1 := by omega
    simp only [List.length_cons, List.cons_append]
    rw [h]; exact nth?_append_right as l₂ i

theorem nth?_lt_length {α : Type} :
    ∀ (l : List α) (i : Nat) (a : α), nth? l i = some a → i < l.length
  | [], _, _, h => by cases h
  | _ :: _, 0, _, _ => Nat.zero_lt_succ _
  | _ :: as, i + 1, a, h => Nat.succ_lt_succ (nth?_lt_length as i a h)

theorem nth?_ne_none_of_lt {α : Type} :
    ∀ (l : List α) (i : Nat), i < l.length → nth? l i ≠ none
  | [], _, h => by cases h
  | _ :: _, 0, _ => by simp [nth?]
  | _ :: as, i + 1, h => nth?_ne_none_of_lt as i (Nat.lt_of_succ_lt_succ h)

theorem nth?_mem {α : Type} :
    ∀ (l : List α) (i : Nat) (a : α), nth? l i = some a → a ∈ l
  | [], _, _, h => by cases h
  | _ :: _, 0, _, h => by cases h; exact .head _
  | _ :: as, i + 1, a, h => .tail _ (nth?_mem as i a h)

theorem mem_of_mem_set {α : Type} :
    ∀ (l : List α) (i : Nat) (v x : α), x ∈ l.set i v → x ∈ l ∨ x = v
  | [], _, _, _, h => by cases h
  | _ :: _, 0, _, _, h => by
    simp only [List.set, List.mem_cons] at h
    rcases h with rfl | h2
    · exact Or.inr rfl
    · exact Or.inl (.tail _ h2)
  | _ :: as, i + 1, v, x, h => by
    simp only [List.set, List.mem_cons] at h
    rcases h with rfl | h2
    · exact Or.inl (.head _)
    · rcases mem_of_mem_set as i v x h2 with h3 | rfl
      · exact Or.inl (.tail _ h3)
      · exact Or.inr rfl

theorem mapIdxFrom_length {α β : Type} (f : Nat → α → β) :
    ∀ k l, (mapIdxFrom f k l).length = l.length
  | _, [] => rfl
  | k, _ :: as => congrArg Nat.succ (mapIdxFrom_length f (k + 1) as)

theorem nth?_mapIdxFrom {α β : Type} (f : Nat → α → β) :
    ∀ k l i, nth? (mapIdxFrom f k l) i = (nth? l i).map (f (k + i))
  | _, [], _ => rfl
  | k, a :: _, 0 => by simp [mapIdxFrom, nth?]
  | k, _ :: as, i + 1 => by
    simp only [mapIdxFrom, nth?]
    rw [nth?_mapIdxFrom f (k + 1) as i]
    have h : k + 1 + i = k + (i + 1) := by omega
    rw [h]

theorem walk_prefix_eq (tr : FnId → Bool) (l₁ l₂ : List Scope)
    (hpbAll : ScopeParentsBelow l₁) :
    ∀ (s : Nat) (sp : Span) (f1 f2 : Nat),
      s < l₁.length → s < f1 → s < f2 →
      walk tr (l₁ ++ l₂) f1 s sp = walk tr l₁ f2 s sp := by
  intro s
  induction s using Nat.strongRecOn with
  | ind s ih =>
    intro sp f1 f2 hs hf1 hf2
    obtain ⟨f1', rfl⟩ : ∃ f1', f1 = f1' + 1 := ⟨f1 - 1, by omega⟩
    obtain ⟨f2', rfl⟩ : ∃ f2', f2 = f2' + 1 := ⟨f2 - 1, by omega⟩
    simp only [walk, nth?_append_left l₁ l₂ s hs]
    have hpb := hpbAll s hs
    cases hsc : nth? l₁ s with
    | none => rfl
    | some sc =>
      rw [hsc] at hpb
      simp only [Option.all_some, Scope.parentBelow] at hpb
      cases hinl : sc.inlined with
      | none =>
        simp only [hinl]
        cases hpar : sc.inlinedParent with
        | none => rfl
        | some t =>
          rw [hpar] at hpb
          have ht : t < s := of_decide_eq_true hpb
          exact ih t ht sp f1' f2' (Nat.lt_trans ht hs)
            (by dsimp [ScopeId] at *; omega) (by dsimp [ScopeId] at *; omega)
      | some gx =>
        simp only [hinl]
        cases htr : tr gx.1 with
        | false => simp
        | true =>
          simp only [↓reduceIte]
          cases hpar : sc.inlinedParent with
          | none => rfl
          | some t =>
            rw [hpar] at hpb
            have ht : t < s := of_decide_eq_true hpb
            exact ih t ht gx.2 f1' f2' (Nat.lt_trans ht hs)
              (by dsimp [ScopeId] at *; omega) (by dsimp [ScopeId] at *; omega)


theorem walk_callee_aux (tr : FnId → Bool) (F : Fn) (ci : CallInfo) (G : Fn)
    (hFpb : ScopeParentsBelow F.scopes)
    (hG : ScopeTreeWF G.scopes) :
    let merged := F.scopes ++ linkScopes .rustc F ci G
    ∀ (s : Nat) (sp : Span) (fM fG : Nat),
      s < G.scopes.length →
      F.scopes.length + s < fM →
      s < fG →
      walk tr merged fM (F.scopes.length + s) sp =
        match walk tr G.scopes fG s sp with
        | .stop sp' => .stop sp'
        | .top sp' =>
          if tr ci.callee then walk tr F.scopes F.scopes.length ci.scope ci.span
          else .stop sp' := by
  intro merged s
  have hF0_helper : ∀ (sp' : Span) (fM' : Nat), F.scopes.length ≤ fM' →
      walk tr merged (fM' + 1) (F.scopes.length + 0) sp' =
        if tr ci.callee then walk tr F.scopes F.scopes.length ci.scope ci.span else .stop sp' := by
    intro sp' fM' hfM'
    change walk tr (F.scopes ++ linkScopes .rustc F ci G) (fM' + 1) (F.scopes.length + 0) sp' = _
    conv => lhs; unfold walk
    rw [nth?_append_right]
    have hlink0 : nth? (linkScopes .rustc F ci G) 0 =
        some (linkScope .rustc ci.scope (nth? F.scopes ci.scope) ci.callee ci.span F.scopes.length 0 ⟨none, none⟩) := by
      simp [linkScopes, nth?_mapIdxFrom, hG.1]
    rw [hlink0]
    simp only [linkScope, ↓reduceIte]
    cases htr : tr ci.callee with
    | false => simp
    | true =>
      simp only [↓reduceIte]
      cases hcs : nth? F.scopes ci.scope with
      | none =>
        cases hlenF : F.scopes.length with
        | zero => simp [walk]
        | succ k => simp [walk, hcs]
      | some c =>
        have hci : ci.scope < F.scopes.length := nth?_lt_length F.scopes ci.scope c hcs
        have hci_fM : ci.scope < fM' := Nat.lt_of_lt_of_le hci hfM'
        by_cases hcinl : c.inlined.isSome = true
        · simp only [hcinl, ↓reduceIte]
          exact walk_prefix_eq tr F.scopes (linkScopes .rustc F ci G) hFpb ci.scope ci.span fM'
            F.scopes.length hci hci_fM hci
        · simp only [hcinl, Bool.false_eq_true, ↓reduceIte]
          have hcinl' : c.inlined = none := by
            cases h : c.inlined with
            | none => rfl
            | some _ => rw [h] at hcinl; simp at hcinl
          have hFpos : 0 < F.scopes.length := Nat.lt_of_le_of_lt (Nat.zero_le _) hci
          obtain ⟨k, hk⟩ : ∃ k, F.scopes.length = k + 1 := ⟨F.scopes.length - 1, by omega⟩
          have hwalkF : walk tr F.scopes F.scopes.length ci.scope ci.span =
              match c.inlinedParent with
              | none => .top ci.span
              | some t => walk tr F.scopes k t ci.span := by
            rw [hk]; simp only [walk, hcs, hcinl']; rfl
          rw [hwalkF]
          cases hpar : c.inlinedParent with
          | none => rfl
          | some t =>
            have hpb := hFpb ci.scope hci
            rw [hcs] at hpb
            simp only [Option.all_some, Scope.parentBelow, hpar] at hpb
            have ht : t < ci.scope := of_decide_eq_true hpb
            have htF : t < F.scopes.length := Nat.lt_trans ht hci
            exact walk_prefix_eq tr F.scopes (linkScopes .rustc F ci G) hFpb t ci.span fM' k htF
              (Nat.lt_of_lt_of_le htF hfM') (by dsimp [ScopeId] at *; omega)
  induction s using Nat.strongRecOn with
  | ind s ih =>
    intro sp fM fG hs hfM hfG
    by_cases hs0 : s = 0
    · subst hs0
      obtain ⟨fM', rfl⟩ : ∃ fM', fM = fM' + 1 := ⟨fM - 1, by omega⟩
      obtain ⟨fG', rfl⟩ : ∃ fG', fG = fG' + 1 := ⟨fG - 1, by omega⟩
      have hG0 : walk tr G.scopes (fG' + 1) 0 sp = .top sp := by simp [walk, hG.1]
      rw [hG0]
      exact hF0_helper sp fM' (by omega)
    · obtain ⟨fM', rfl⟩ : ∃ fM', fM = fM' + 1 := ⟨fM - 1, by omega⟩
      obtain ⟨fG', rfl⟩ : ∃ fG', fG = fG' + 1 := ⟨fG - 1, by omega⟩
      have hGpb := hG.2 s hs
      simp only [merged, walk, nth?_append_right]
      have hlinks : nth? (linkScopes .rustc F ci G) s =
          (nth? G.scopes s).map (linkScope .rustc ci.scope (nth? F.scopes ci.scope) ci.callee ci.span F.scopes.length s) := by
        simp [linkScopes, nth?_mapIdxFrom]
      rw [hlinks]
      cases hsc : nth? G.scopes s with
      | none => exact absurd hsc (nth?_ne_none_of_lt G.scopes s hs)
      | some sc =>
        rw [hsc] at hGpb
        simp only [Option.map_some, Option.all_some, linkScope, hs0, ↓reduceIte, Scope.parentBelow] at hGpb ⊢
        cases hinl : sc.inlined with
        | none =>
          cases hpar : sc.inlinedParent with
          | none =>
            simp only
            have h0eq : F.scopes.length = F.scopes.length + 0 := (Nat.add_zero _).symm
            obtain ⟨fM'', rfl⟩ : ∃ fM'', fM' = fM'' + 1 := ⟨fM' - 1, by omega⟩
            rw [h0eq]
            exact hF0_helper sp fM'' (by omega)
          | some t =>
            rw [hpar] at hGpb
            simp only
            have ht : t < s := of_decide_eq_true hGpb
            have hcomm : t + F.scopes.length = F.scopes.length + t := Nat.add_comm _ _
            rw [hcomm]
            exact ih t ht sp fM' fG' (Nat.lt_trans ht hs)
              (by dsimp [ScopeId] at *; omega) (by dsimp [ScopeId] at *; omega)
        | some gx =>
          cases htr : tr gx.1 with
          | false => simp [htr]
          | true =>
            simp only [htr, ↓reduceIte]
            cases hpar : sc.inlinedParent with
            | none =>
              simp only
              have h0eq : F.scopes.length = F.scopes.length + 0 := (Nat.add_zero _).symm
              obtain ⟨fM'', rfl⟩ : ∃ fM'', fM' = fM'' + 1 := ⟨fM' - 1, by omega⟩
              conv => lhs; rw [h0eq]
              exact hF0_helper gx.2 fM'' (by omega)
            | some t =>
              rw [hpar] at hGpb
              simp only
              have ht : t < s := of_decide_eq_true hGpb
              have hcomm : t + F.scopes.length = F.scopes.length + t := Nat.add_comm _ _
              rw [hcomm]
              exact ih t ht gx.2 fM' fG' (Nat.lt_trans ht hs)
                (by dsimp [ScopeId] at *; omega) (by dsimp [ScopeId] at *; omega)

end Toy.Inline
