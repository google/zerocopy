import PanicSafety.RetainResults

/-!
# Call-site characterization of panic safety under unwinding

For every program `p`: `p` is panic-safe under `unwind` (from every entry state satisfying
`Inv`, under every callback and destructor table) if and only if `p` is panic-safe under
`abort` and, at every user-code site that `exec` reaches from an entry state satisfying `Inv`
(under any callback and destructor table), `DropSafe` holds: after the frame's guard fix-ups,
`len ≤ buf.length`, and the values of the live locals together with the container's first
`len` cells are uniquely owned. User-code sites are callback invocations *and* element
destructor invocations.

Formal scope: `run` and `sites` start `exec` with frame `[]`, and `ResOk` checks `Inv` on
the state handed back at a return or an unwind. Guard fix-ups (`Guard.fix`) are pure
functions of `(buf, len)`: a guard cannot run element destructors, panic, read or change
the drop log, or reach UB, so guards that drop elements are not programs of `Prog`.
-/

namespace Toy.PanicSafety

/-- Every user-code site (callback or destructor) reached by a run of `p` from an entry
state satisfying `Inv`, under any callback and destructor table, satisfies `DropSafe`. The
sites are those produced by the interpreter `exec` (`sites`). -/
def CallSitesDropSafe (p : Prog) : Prop :=
  ∀ (cb : Callback) (dt : DtorTable) (m : Mem), Inv m →
    ∀ s ∈ sites cb dt p m, DropSafe s.entries s.mem

/-- The weaker condition that considers callback sites only. -/
def CallbackSitesDropSafe (p : Prog) : Prop :=
  ∀ (cb : Callback) (dt : DtorTable) (m : Mem), Inv m →
    ∀ s ∈ sites cb dt p m, s.kind = .callback → DropSafe s.entries s.mem

/-- If unwinding a frame with non-panicking destructors ends in `.ok m'`, then with any destructor table it ends in `.ok m'` or `.abort`. -/
theorem unwindEntries_ok_noPanic_imp_ok_or_abort (dt : DtorTable) :
    ∀ (es : List Entry) (m m' : Mem),
      unwindEntries noPanicDtors es m = .ok m' →
      unwindEntries dt es m = .ok m' ∨ unwindEntries dt es m = .abort
  | [], m, m', h => Or.inl h
  | .value t :: es, m, m', h => by
      simp only [unwindEntries, noPanicDtors, Bool.false_eq_true, ite_false] at h ⊢
      by_cases ht : t ∈ m.dropped
      · simp [ht] at h
      · simp only [ht, ite_false] at h ⊢
        cases hdt : dt t
        · simp only [Bool.false_eq_true, ite_false]
          exact unwindEntries_ok_noPanic_imp_ok_or_abort dt es _ m' h
        · exact Or.inr rfl
  | .guard g :: es, m, m', h => by
      simp only [unwindEntries] at h ⊢
      exact unwindEntries_ok_noPanic_imp_ok_or_abort dt es _ m' h

/-- Unwinding is unaffected by destructors that panic only on values already in the drop log. -/
theorem unwindEntries_eq_noPanic_of_panickers_dropped (dt : DtorTable) :
    ∀ (es : List Entry) (m : Mem),
      (∀ u, dt u = true → u ∈ m.dropped) →
      unwindEntries dt es m = unwindEntries noPanicDtors es m
  | [], _, _ => rfl
  | .value t :: es, m, hdrop => by
      simp only [unwindEntries, noPanicDtors, Bool.false_eq_true, ite_false]
      by_cases ht : t ∈ m.dropped
      · simp [ht]
      · have hdt : dt t = false := by
          cases h : dt t
          · rfl
          · exact absurd (hdrop t h) ht
        simp only [ht, hdt, Bool.false_eq_true, ite_false]
        exact unwindEntries_eq_noPanic_of_panickers_dropped dt es _ fun u hu =>
          List.mem_cons_of_mem t (hdrop u hu)
  | .guard g :: es, m, hdrop => by
      simp only [unwindEntries]
      exact unwindEntries_eq_noPanic_of_panickers_dropped dt es _ hdrop

/-- A panic at a `DropSafe` site gives an acceptable outcome under `unwind`, for every destructor table. -/
theorem resOk_panicFrom_of_dropSafe (dt : DtorTable) (es : List Entry) (m : Mem)
    (hds : DropSafe es m) : ResOk (panicFrom .unwind dt es m) := by
  obtain ⟨m', hok, hinv⟩ := (unwindEntries_noPanic_ok_inv_iff_dropSafe es m).mpr hds
  rcases unwindEntries_ok_noPanic_imp_ok_or_abort dt es m m' hok with h | h <;>
    simp [panicFrom, h, ResOk, hinv]

/-- Right-to-left direction of the call-site characterization, generalized over the frame and the callback counter. -/
theorem exec_unwind_resOk_of_abort_resOk_of_sitesDropSafe (cb : Callback) (dt : DtorTable) :
    ∀ (p : Prog) (j : Nat) (es : List Entry) (m : Mem),
      ResOk (exec .abort cb dt p j es m).1 →
      (∀ s ∈ (exec .unwind cb dt p j es m).2, DropSafe s.entries s.mem) →
      ResOk (exec .unwind cb dt p j es m).1
  | .done, _, _, _, hab, _ => hab
  | .getLen k, j, es, m, hab, hsites => exec_unwind_resOk_of_abort_resOk_of_sitesDropSafe cb dt (k m.len) j es m hab hsites
  | .call k, j, es, m, hab, hsites => by
      simp only [exec] at hab hsites ⊢
      cases hcb : cb j with
      | ret b =>
        simp only [hcb] at hab hsites ⊢
        exact exec_unwind_resOk_of_abort_resOk_of_sitesDropSafe cb dt (k b) (j + 1) es m hab fun s hs =>
          hsites s (List.mem_cons_of_mem _ hs)
      | panic =>
        simp only [hcb] at hsites ⊢
        exact resOk_panicFrom_of_dropSafe dt es m (hsites _ List.mem_cons_self)
  | .copy s d k, j, es, m, hab, hsites => by
      simp only [exec] at hab hsites ⊢
      split at hab
      · rename_i hlt
        simp only [hlt] at hsites ⊢
        exact exec_unwind_resOk_of_abort_resOk_of_sitesDropSafe cb dt k j es _ hab hsites
      · simp [ResOk] at hab
  | .dropCell i k, j, es, m, hab, hsites => by
      simp only [exec] at hab hsites ⊢
      cases hb : m.buf[i]? with
      | none => simp [hb, ResOk] at hab
      | some c =>
        cases c with
        | none => simp [hb, ResOk] at hab
        | some t =>
          simp only [hb] at hab hsites ⊢
          by_cases ht : t ∈ m.dropped
          · simp [ht, ResOk] at hab
          · simp only [ht, ite_false] at hab hsites ⊢
            cases hdt : dt t with
            | true =>
              simp only [hdt, ite_true] at hsites ⊢
              exact resOk_panicFrom_of_dropSafe dt es _ (hsites _ List.mem_cons_self)
            | false =>
              simp only [hdt, Bool.false_eq_true, ite_false] at hab hsites ⊢
              exact exec_unwind_resOk_of_abort_resOk_of_sitesDropSafe cb dt k j es _ hab fun s hs =>
                hsites s (List.mem_cons_of_mem _ hs)
  | .setLen n k, j, es, m, hab, hsites => exec_unwind_resOk_of_abort_resOk_of_sitesDropSafe cb dt k j es _ hab hsites
  | .readOut i k, j, es, m, hab, hsites => by
      simp only [exec] at hab hsites ⊢
      cases hb : m.buf[i]? with
      | none => simp [hb, ResOk] at hab
      | some c =>
        cases c with
        | none => simp [hb, ResOk] at hab
        | some t =>
          simp only [hb] at hab hsites ⊢
          exact exec_unwind_resOk_of_abort_resOk_of_sitesDropSafe cb dt k j _ m hab hsites
  | .writeBack i k, j, es, m, hab, hsites => by
      simp only [exec] at hab hsites ⊢
      cases es with
      | nil => exact hab
      | cons e es' =>
        cases e with
        | guard _ => exact hab
        | value t =>
          simp only at hab hsites ⊢
          split at hab
          · rename_i hlt
            simp only [hlt, ite_true] at hsites ⊢
            exact exec_unwind_resOk_of_abort_resOk_of_sitesDropSafe cb dt k j es' _ hab hsites
          · simp [ResOk] at hab
  | .dropVal k, j, es, m, hab, hsites => by
      simp only [exec] at hab hsites ⊢
      cases es with
      | nil => exact hab
      | cons e es' =>
        cases e with
        | guard _ => exact hab
        | value t =>
          simp only at hab hsites ⊢
          by_cases ht : t ∈ m.dropped
          · simp [ht, ResOk] at hab
          · simp only [ht, ite_false] at hab hsites ⊢
            cases hdt : dt t with
            | true =>
              simp only [hdt, ite_true] at hsites ⊢
              exact resOk_panicFrom_of_dropSafe dt es' _ (hsites _ List.mem_cons_self)
            | false =>
              simp only [hdt, Bool.false_eq_true, ite_false] at hab hsites ⊢
              exact exec_unwind_resOk_of_abort_resOk_of_sitesDropSafe cb dt k j es' _ hab fun s hs =>
                hsites s (List.mem_cons_of_mem _ hs)
  | .forgetVal k, j, es, m, hab, hsites => by
      simp only [exec] at hab hsites ⊢
      cases es with
      | nil => exact hab
      | cons e es' =>
        cases e with
        | guard _ => exact hab
        | value _ => exact exec_unwind_resOk_of_abort_resOk_of_sitesDropSafe cb dt k j es' m hab hsites
  | .pushGuard g k, j, es, m, hab, hsites => exec_unwind_resOk_of_abort_resOk_of_sitesDropSafe cb dt k j _ m hab hsites
  | .setGuard g k, j, es, m, hab, hsites => by
      simp only [exec] at hab hsites ⊢
      cases es with
      | nil => exact hab
      | cons e es' =>
        cases e with
        | value _ => exact hab
        | guard _ => exact exec_unwind_resOk_of_abort_resOk_of_sitesDropSafe cb dt k j _ m hab hsites
  | .popGuard k, j, es, m, hab, hsites => by
      simp only [exec] at hab hsites ⊢
      cases es with
      | nil => exact hab
      | cons e es' =>
        cases e with
        | value _ => exact hab
        | guard g => exact exec_unwind_resOk_of_abort_resOk_of_sitesDropSafe cb dt k j es' _ hab hsites
  | .forgetGuard k, j, es, m, hab, hsites => by
      simp only [exec] at hab hsites ⊢
      cases es with
      | nil => exact hab
      | cons e es' =>
        cases e with
        | value _ => exact hab
        | guard _ => exact exec_unwind_resOk_of_abort_resOk_of_sitesDropSafe cb dt k j es' m hab hsites
  | .bumpA k, j, es, m, hab, hsites => exec_unwind_resOk_of_abort_resOk_of_sitesDropSafe cb dt k j es _ hab hsites
  | .bumpB k, j, es, m, hab, hsites => exec_unwind_resOk_of_abort_resOk_of_sitesDropSafe cb dt k j es _ hab hsites

/-- An acceptable outcome under `unwind` implies an acceptable outcome under `abort` for the same run. -/
theorem exec_abort_resOk_of_unwind_resOk (cb : Callback) (dt : DtorTable) :
    ∀ (p : Prog) (j : Nat) (es : List Entry) (m : Mem),
      ResOk (exec .unwind cb dt p j es m).1 →
      ResOk (exec .abort cb dt p j es m).1
  | .done, _, _, _, h => h
  | .getLen k, j, es, m, h => exec_abort_resOk_of_unwind_resOk cb dt (k m.len) j es m h
  | .call k, j, es, m, h => by
      simp only [exec] at h ⊢
      cases hcb : cb j with
      | ret b => simp only [hcb] at h ⊢; exact exec_abort_resOk_of_unwind_resOk cb dt (k b) (j + 1) es m h
      | panic => simp [panicFrom, ResOk]
  | .copy s d k, j, es, m, h => by
      simp only [exec] at h ⊢
      split at h
      · rename_i hlt
        simp only [hlt]
        exact exec_abort_resOk_of_unwind_resOk cb dt k j es _ h
      · simp [ResOk] at h
  | .dropCell i k, j, es, m, h => by
      simp only [exec] at h ⊢
      cases hb : m.buf[i]? with
      | none => simp [hb, ResOk] at h
      | some c =>
        cases c with
        | none => simp [hb, ResOk] at h
        | some t =>
          simp only [hb] at h ⊢
          by_cases ht : t ∈ m.dropped
          · simp [ht, ResOk] at h
          · simp only [ht, ite_false] at h ⊢
            cases hdt : dt t with
            | true => simp [panicFrom, ResOk]
            | false =>
              simp only [hdt, Bool.false_eq_true, ite_false] at h ⊢
              exact exec_abort_resOk_of_unwind_resOk cb dt k j es _ h
  | .setLen n k, j, es, m, h => exec_abort_resOk_of_unwind_resOk cb dt k j es _ h
  | .readOut i k, j, es, m, h => by
      simp only [exec] at h ⊢
      cases hb : m.buf[i]? with
      | none => simp [hb, ResOk] at h
      | some c =>
        cases c with
        | none => simp [hb, ResOk] at h
        | some t => simp only [hb] at h ⊢; exact exec_abort_resOk_of_unwind_resOk cb dt k j _ m h
  | .writeBack i k, j, es, m, h => by
      simp only [exec] at h ⊢
      cases es with
      | nil => exact h
      | cons e es' =>
        cases e with
        | guard _ => exact h
        | value t =>
          simp only at h ⊢
          split at h
          · rename_i hlt
            simp only [hlt, ite_true]
            exact exec_abort_resOk_of_unwind_resOk cb dt k j es' _ h
          · simp [ResOk] at h
  | .dropVal k, j, es, m, h => by
      simp only [exec] at h ⊢
      cases es with
      | nil => exact h
      | cons e es' =>
        cases e with
        | guard _ => exact h
        | value t =>
          simp only at h ⊢
          by_cases ht : t ∈ m.dropped
          · simp [ht, ResOk] at h
          · simp only [ht, ite_false] at h ⊢
            cases hdt : dt t with
            | true => simp [panicFrom, ResOk]
            | false =>
              simp only [hdt, Bool.false_eq_true, ite_false] at h ⊢
              exact exec_abort_resOk_of_unwind_resOk cb dt k j es' _ h
  | .forgetVal k, j, es, m, h => by
      simp only [exec] at h ⊢
      cases es with
      | nil => exact h
      | cons e es' =>
        cases e with
        | guard _ => exact h
        | value _ => exact exec_abort_resOk_of_unwind_resOk cb dt k j es' m h
  | .pushGuard g k, j, es, m, h => exec_abort_resOk_of_unwind_resOk cb dt k j _ m h
  | .setGuard g k, j, es, m, h => by
      simp only [exec] at h ⊢
      cases es with
      | nil => exact h
      | cons e es' =>
        cases e with
        | value _ => exact h
        | guard _ => exact exec_abort_resOk_of_unwind_resOk cb dt k j _ m h
  | .popGuard k, j, es, m, h => by
      simp only [exec] at h ⊢
      cases es with
      | nil => exact h
      | cons e es' =>
        cases e with
        | value _ => exact h
        | guard _ => exact exec_abort_resOk_of_unwind_resOk cb dt k j es' _ h
  | .forgetGuard k, j, es, m, h => by
      simp only [exec] at h ⊢
      cases es with
      | nil => exact h
      | cons e es' =>
        cases e with
        | value _ => exact h
        | guard _ => exact exec_abort_resOk_of_unwind_resOk cb dt k j es' m h
  | .bumpA k, j, es, m, h => exec_abort_resOk_of_unwind_resOk cb dt k j es _ h
  | .bumpB k, j, es, m, h => exec_abort_resOk_of_unwind_resOk cb dt k j es _ h

/-- Table surgery at a callback site: making that invocation panic (with non-panicking destructors) ends the run in `panicFrom` at that site. -/
theorem exec_callback_site_surgery (cb : Callback) (dt : DtorTable) :
    ∀ (p : Prog) (j : Nat) (es : List Entry) (m : Mem) (s : Site),
      s ∈ (exec .unwind cb dt p j es m).2 →
      s.kind = .callback →
      ∃ k ≥ j,
        (exec .unwind (fun i => if i = k then .panic else cb i) noPanicDtors p j es m).1 =
          panicFrom .unwind noPanicDtors s.entries s.mem
  | .done, _, _, _, _, hs, _ => by simp [exec] at hs
  | .getLen k, j, es, m, s, hs, hk => exec_callback_site_surgery cb dt (k m.len) j es m s hs hk
  | .call k, j, es, m, s, hs, hk => by
      simp only [exec] at hs
      cases hcb : cb j with
      | panic =>
        simp only [hcb, List.mem_singleton] at hs
        subst hs
        exact ⟨j, Nat.le_refl _, by simp [exec]⟩
      | ret b =>
        simp only [hcb, List.mem_cons] at hs
        rcases hs with rfl | hs
        · exact ⟨j, Nat.le_refl _, by simp [exec]⟩
        · obtain ⟨k', hk', heq⟩ := exec_callback_site_surgery cb dt (k b) (j + 1) es m s hs hk
          have hne : j ≠ k' := by omega
          refine ⟨k', by omega, ?_⟩
          simp only [exec, hne, ite_false, hcb]
          exact heq
  | .copy src dst k, j, es, m, s, hs, hk => by
      simp only [exec] at hs
      split at hs
      · rename_i hlt
        obtain ⟨k', hk', heq⟩ := exec_callback_site_surgery cb dt k j es _ s hs hk
        exact ⟨k', hk', by simp only [exec, hlt]; exact heq⟩
      · simp at hs
  | .dropCell i k, j, es, m, s, hs, hk => by
      simp only [exec] at hs
      cases hb : m.buf[i]? with
      | none => simp [hb] at hs
      | some c =>
        cases c with
        | none => simp [hb] at hs
        | some t =>
          simp only [hb] at hs
          by_cases ht : t ∈ m.dropped
          · simp [ht] at hs
          · simp only [ht, ite_false] at hs
            cases hdt : dt t with
            | true =>
              simp only [hdt, ite_true, List.mem_singleton] at hs
              subst hs; simp at hk
            | false =>
              simp only [hdt, Bool.false_eq_true, ite_false, List.mem_cons] at hs
              rcases hs with rfl | hs
              · simp at hk
              · obtain ⟨k', hk', heq⟩ := exec_callback_site_surgery cb dt k j es _ s hs hk
                exact ⟨k', hk', by
                  simp only [exec, hb, ht, ite_false, noPanicDtors, Bool.false_eq_true]
                  exact heq⟩
  | .setLen n k, j, es, m, s, hs, hk => exec_callback_site_surgery cb dt k j es _ s hs hk
  | .readOut i k, j, es, m, s, hs, hk => by
      simp only [exec] at hs
      cases hb : m.buf[i]? with
      | none => simp [hb] at hs
      | some c =>
        cases c with
        | none => simp [hb] at hs
        | some t =>
          simp only [hb] at hs
          obtain ⟨k', hk', heq⟩ := exec_callback_site_surgery cb dt k j _ m s hs hk
          exact ⟨k', hk', by simp only [exec, hb]; exact heq⟩
  | .writeBack i k, j, es, m, s, hs, hk => by
      simp only [exec] at hs
      cases es with
      | nil => simp at hs
      | cons e es' =>
        cases e with
        | guard _ => simp at hs
        | value t =>
          simp only at hs
          split at hs
          · rename_i hlt
            obtain ⟨k', hk', heq⟩ := exec_callback_site_surgery cb dt k j es' _ s hs hk
            exact ⟨k', hk', by simp only [exec, hlt]; exact heq⟩
          · simp at hs
  | .dropVal k, j, es, m, s, hs, hk => by
      simp only [exec] at hs
      cases es with
      | nil => simp at hs
      | cons e es' =>
        cases e with
        | guard _ => simp at hs
        | value t =>
          simp only at hs
          by_cases ht : t ∈ m.dropped
          · simp [ht] at hs
          · simp only [ht, ite_false] at hs
            cases hdt : dt t with
            | true =>
              simp only [hdt, ite_true, List.mem_singleton] at hs
              subst hs; simp at hk
            | false =>
              simp only [hdt, Bool.false_eq_true, ite_false, List.mem_cons] at hs
              rcases hs with rfl | hs
              · simp at hk
              · obtain ⟨k', hk', heq⟩ := exec_callback_site_surgery cb dt k j es' _ s hs hk
                exact ⟨k', hk', by
                  simp only [exec, ht, ite_false, noPanicDtors, Bool.false_eq_true]
                  exact heq⟩
  | .forgetVal k, j, es, m, s, hs, hk => by
      simp only [exec] at hs
      cases es with
      | nil => simp at hs
      | cons e es' =>
        cases e with
        | guard _ => simp at hs
        | value _ => exact exec_callback_site_surgery cb dt k j es' m s hs hk
  | .pushGuard g k, j, es, m, s, hs, hk => exec_callback_site_surgery cb dt k j _ m s hs hk
  | .setGuard g k, j, es, m, s, hs, hk => by
      simp only [exec] at hs
      cases es with
      | nil => simp at hs
      | cons e es' =>
        cases e with
        | value _ => simp at hs
        | guard _ => exact exec_callback_site_surgery cb dt k j _ m s hs hk
  | .popGuard k, j, es, m, s, hs, hk => by
      simp only [exec] at hs
      cases es with
      | nil => simp at hs
      | cons e es' =>
        cases e with
        | value _ => simp at hs
        | guard _ => exact exec_callback_site_surgery cb dt k j es' _ s hs hk
  | .forgetGuard k, j, es, m, s, hs, hk => by
      simp only [exec] at hs
      cases es with
      | nil => simp at hs
      | cons e es' =>
        cases e with
        | value _ => simp at hs
        | guard _ => exact exec_callback_site_surgery cb dt k j es' m s hs hk
  | .bumpA k, j, es, m, s, hs, hk => exec_callback_site_surgery cb dt k j es _ s hs hk
  | .bumpB k, j, es, m, s, hs, hk => exec_callback_site_surgery cb dt k j es _ s hs hk

/-- Table surgery at a destructor site: making exactly that value's destructor panic ends the run in `panicFrom` at that site. -/
theorem exec_destructor_site_surgery (cb : Callback) (dt : DtorTable) :
    ∀ (p : Prog) (j : Nat) (es : List Entry) (m : Mem) (s : Site),
      s ∈ (exec .unwind cb dt p j es m).2 →
      s.kind = .destructor →
      ∃ t, t ∉ m.dropped ∧ t ∈ s.mem.dropped ∧
        (exec .unwind cb (fun u => decide (u = t)) p j es m).1 =
          panicFrom .unwind (fun u => decide (u = t)) s.entries s.mem
  | .done, _, _, _, _, hs, _ => by simp [exec] at hs
  | .getLen k, j, es, m, s, hs, hk => exec_destructor_site_surgery cb dt (k m.len) j es m s hs hk
  | .call k, j, es, m, s, hs, hk => by
      simp only [exec] at hs
      cases hcb : cb j with
      | panic =>
        simp only [hcb, List.mem_singleton] at hs
        subst hs; simp at hk
      | ret b =>
        simp only [hcb, List.mem_cons] at hs
        rcases hs with rfl | hs
        · simp at hk
        · obtain ⟨t, hnot, hin, heq⟩ := exec_destructor_site_surgery cb dt (k b) (j + 1) es m s hs hk
          exact ⟨t, hnot, hin, by simp only [exec, hcb]; exact heq⟩
  | .copy src dst k, j, es, m, s, hs, hk => by
      simp only [exec] at hs
      split at hs
      · rename_i hlt
        obtain ⟨t, hnot, hin, heq⟩ := exec_destructor_site_surgery cb dt k j es _ s hs hk
        exact ⟨t, hnot, hin, by simp only [exec, hlt]; exact heq⟩
      · simp at hs
  | .dropCell i k, j, es, m, s, hs, hk => by
      simp only [exec] at hs
      cases hb : m.buf[i]? with
      | none => simp [hb] at hs
      | some c =>
        cases c with
        | none => simp [hb] at hs
        | some u =>
          simp only [hb] at hs
          by_cases hu : u ∈ m.dropped
          · simp [hu] at hs
          · simp only [hu, ite_false] at hs
            cases hdt : dt u with
            | true =>
              simp only [hdt, ite_true, List.mem_singleton] at hs
              subst hs
              exact ⟨u, hu, List.mem_cons_self, by simp [exec, hb, hu]⟩
            | false =>
              simp only [hdt, Bool.false_eq_true, ite_false, List.mem_cons] at hs
              rcases hs with rfl | hs
              · exact ⟨u, hu, List.mem_cons_self, by simp [exec, hb, hu]⟩
              · obtain ⟨t, hnot, hin, heq⟩ := exec_destructor_site_surgery cb dt k j es _ s hs hk
                have hne : u ≠ t := fun h => hnot (h ▸ List.mem_cons_self)
                have hnot' : t ∉ m.dropped := fun h => hnot (List.mem_cons_of_mem u h)
                refine ⟨t, hnot', hin, ?_⟩
                simp only [exec, hb, hu, ite_false, decide_eq_true_eq, hne]
                exact heq
  | .setLen n k, j, es, m, s, hs, hk => exec_destructor_site_surgery cb dt k j es _ s hs hk
  | .readOut i k, j, es, m, s, hs, hk => by
      simp only [exec] at hs
      cases hb : m.buf[i]? with
      | none => simp [hb] at hs
      | some c =>
        cases c with
        | none => simp [hb] at hs
        | some t =>
          simp only [hb] at hs
          obtain ⟨u, hnot, hin, heq⟩ := exec_destructor_site_surgery cb dt k j _ m s hs hk
          exact ⟨u, hnot, hin, by simp only [exec, hb]; exact heq⟩
  | .writeBack i k, j, es, m, s, hs, hk => by
      simp only [exec] at hs
      cases es with
      | nil => simp at hs
      | cons e es' =>
        cases e with
        | guard _ => simp at hs
        | value t =>
          simp only at hs
          split at hs
          · rename_i hlt
            obtain ⟨u, hnot, hin, heq⟩ := exec_destructor_site_surgery cb dt k j es' _ s hs hk
            exact ⟨u, hnot, hin, by simp only [exec, hlt, ite_true]; exact heq⟩
          · simp at hs
  | .dropVal k, j, es, m, s, hs, hk => by
      simp only [exec] at hs
      cases es with
      | nil => simp at hs
      | cons e es' =>
        cases e with
        | guard _ => simp at hs
        | value u =>
          simp only at hs
          by_cases hu : u ∈ m.dropped
          · simp [hu] at hs
          · simp only [hu, ite_false] at hs
            cases hdt : dt u with
            | true =>
              simp only [hdt, ite_true, List.mem_singleton] at hs
              subst hs
              exact ⟨u, hu, List.mem_cons_self, by simp [exec, hu]⟩
            | false =>
              simp only [hdt, Bool.false_eq_true, ite_false, List.mem_cons] at hs
              rcases hs with rfl | hs
              · exact ⟨u, hu, List.mem_cons_self, by simp [exec, hu]⟩
              · obtain ⟨t, hnot, hin, heq⟩ := exec_destructor_site_surgery cb dt k j es' _ s hs hk
                have hne : u ≠ t := fun h => hnot (h ▸ List.mem_cons_self)
                have hnot' : t ∉ m.dropped := fun h => hnot (List.mem_cons_of_mem u h)
                refine ⟨t, hnot', hin, ?_⟩
                simp only [exec, hu, ite_false, decide_eq_true_eq, hne]
                exact heq
  | .forgetVal k, j, es, m, s, hs, hk => by
      simp only [exec] at hs
      cases es with
      | nil => simp at hs
      | cons e es' =>
        cases e with
        | guard _ => simp at hs
        | value _ => exact exec_destructor_site_surgery cb dt k j es' m s hs hk
  | .pushGuard g k, j, es, m, s, hs, hk => exec_destructor_site_surgery cb dt k j _ m s hs hk
  | .setGuard g k, j, es, m, s, hs, hk => by
      simp only [exec] at hs
      cases es with
      | nil => simp at hs
      | cons e es' =>
        cases e with
        | value _ => simp at hs
        | guard _ => exact exec_destructor_site_surgery cb dt k j _ m s hs hk
  | .popGuard k, j, es, m, s, hs, hk => by
      simp only [exec] at hs
      cases es with
      | nil => simp at hs
      | cons e es' =>
        cases e with
        | value _ => simp at hs
        | guard _ => exact exec_destructor_site_surgery cb dt k j es' _ s hs hk
  | .forgetGuard k, j, es, m, s, hs, hk => by
      simp only [exec] at hs
      cases es with
      | nil => simp at hs
      | cons e es' =>
        cases e with
        | value _ => simp at hs
        | guard _ => exact exec_destructor_site_surgery cb dt k j es' m s hs hk
  | .bumpA k, j, es, m, s, hs, hk => exec_destructor_site_surgery cb dt k j es _ s hs hk
  | .bumpB k, j, es, m, s, hs, hk => exec_destructor_site_surgery cb dt k j es _ s hs hk

/-- An acceptable outcome of a panic with non-panicking destructors implies `DropSafe` at the site. -/
theorem dropSafe_of_resOk_panicFrom_noPanic (es : List Entry) (m : Mem)
    (h : ResOk (panicFrom .unwind noPanicDtors es m)) : DropSafe es m := by
  have hneAbort : unwindEntries noPanicDtors es m ≠ .abort := by
    have aux : ∀ es m, unwindEntries noPanicDtors es m ≠ .abort := by
      intro es
      induction es with
      | nil => intro m; simp [unwindEntries]
      | cons e es ih =>
        intro m
        cases e with
        | value t =>
          simp only [unwindEntries, noPanicDtors, Bool.false_eq_true, ite_false]
          split
          · simp
          · exact ih _
        | guard g => exact ih _
    exact aux es m
  rw [← unwindEntries_noPanic_ok_inv_iff_dropSafe]
  cases hu : unwindEntries noPanicDtors es m with
  | ok m' =>
    simp [panicFrom, hu, ResOk] at h
    exact ⟨m', rfl, h⟩
  | abort => exact absurd hu hneAbort
  | ub => simp [panicFrom, hu, ResOk] at h

/-- Call-site characterization: an operation is panic-safe under `unwind` if and only if it
is panic-safe under `abort` and every user-code site it reaches from an entry state
satisfying `Inv` (callback and destructor invocations, as produced by `sites`) is
`DropSafe`. -/
theorem panicSafe_unwind_iff_abort_and_callSitesDropSafe (p : Prog) :
    PanicSafe .unwind p ↔ PanicSafe .abort p ∧ CallSitesDropSafe p := by
  constructor
  · intro hu
    refine ⟨fun cb dt m hm => exec_abort_resOk_of_unwind_resOk cb dt p 0 [] m (hu cb dt m hm), ?_⟩
    intro cb dt m hm s hs
    cases hk : s.kind with
    | callback =>
      obtain ⟨k, _, heq⟩ := exec_callback_site_surgery cb dt p 0 [] m s hs hk
      have hok := hu (fun i => if i = k then .panic else cb i) noPanicDtors m hm
      unfold run at hok
      rw [heq] at hok
      exact dropSafe_of_resOk_panicFrom_noPanic s.entries s.mem hok
    | destructor =>
      obtain ⟨t, _, hin, heq⟩ := exec_destructor_site_surgery cb dt p 0 [] m s hs hk
      have hok := hu cb (fun u => decide (u = t)) m hm
      unfold run at hok
      rw [heq] at hok
      have heqU : unwindEntries (fun u => decide (u = t)) s.entries s.mem =
          unwindEntries noPanicDtors s.entries s.mem :=
        unwindEntries_eq_noPanic_of_panickers_dropped _ s.entries s.mem fun u hu' => by
          have : u = t := of_decide_eq_true hu'
          exact this ▸ hin
      simp only [panicFrom, heqU] at hok
      exact dropSafe_of_resOk_panicFrom_noPanic s.entries s.mem hok
  · rintro ⟨hab, hsites⟩ cb dt m hm
    exact exec_unwind_resOk_of_abort_resOk_of_sitesDropSafe cb dt p 0 [] m (hab cb dt m hm)
      (hsites cb dt m hm)

/-- Every site reached under some destructor table is also reached with non-panicking destructors. -/
theorem exec_sites_subset_noPanicDtors (cb : Callback) (dt : DtorTable) :
    ∀ (p : Prog) (j : Nat) (es : List Entry) (m : Mem) (s : Site),
      s ∈ (exec .unwind cb dt p j es m).2 →
      s ∈ (exec .unwind cb noPanicDtors p j es m).2
  | .done, _, _, _, _, hs => hs
  | .getLen k, j, es, m, s, hs => exec_sites_subset_noPanicDtors cb dt (k m.len) j es m s hs
  | .call k, j, es, m, s, hs => by
      simp only [exec] at hs ⊢
      cases hcb : cb j with
      | panic => simp [hcb] at hs ⊢; exact hs
      | ret b =>
        simp only [hcb, List.mem_cons] at hs ⊢
        rcases hs with rfl | hs
        · exact Or.inl rfl
        · exact Or.inr (exec_sites_subset_noPanicDtors cb dt (k b) (j + 1) es m s hs)
  | .copy src dst k, j, es, m, s, hs => by
      simp only [exec] at hs ⊢
      split at hs <;> simp_all
      exact exec_sites_subset_noPanicDtors cb dt k j es _ s hs
  | .dropCell i k, j, es, m, s, hs => by
      simp only [exec] at hs ⊢
      cases hb : m.buf[i]? with
      | none => simp [hb] at hs
      | some c =>
        cases c with
        | none => simp [hb] at hs
        | some t =>
          simp only [hb] at hs ⊢
          by_cases ht : t ∈ m.dropped
          · simp [ht] at hs
          · simp only [ht, ite_false, noPanicDtors, Bool.false_eq_true] at hs ⊢
            cases hdt : dt t with
            | true =>
              simp only [hdt, ite_true, List.mem_singleton] at hs
              exact List.mem_cons.mpr (Or.inl hs)
            | false =>
              simp only [hdt, Bool.false_eq_true, ite_false, List.mem_cons] at hs
              rcases hs with rfl | hs
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (exec_sites_subset_noPanicDtors cb dt k j es _ s hs)
  | .setLen n k, j, es, m, s, hs => exec_sites_subset_noPanicDtors cb dt k j es _ s hs
  | .readOut i k, j, es, m, s, hs => by
      simp only [exec] at hs ⊢
      cases hb : m.buf[i]? with
      | none => simp [hb] at hs
      | some c =>
        cases c with
        | none => simp [hb] at hs
        | some t => simp only [hb] at hs ⊢; exact exec_sites_subset_noPanicDtors cb dt k j _ m s hs
  | .writeBack i k, j, es, m, s, hs => by
      simp only [exec] at hs ⊢
      cases es with
      | nil => simp at hs
      | cons e es' =>
        cases e with
        | guard _ => simp at hs
        | value t =>
          simp only at hs ⊢
          split at hs <;> simp_all
          exact exec_sites_subset_noPanicDtors cb dt k j es' _ s hs
  | .dropVal k, j, es, m, s, hs => by
      simp only [exec] at hs ⊢
      cases es with
      | nil => simp at hs
      | cons e es' =>
        cases e with
        | guard _ => simp at hs
        | value t =>
          simp only at hs ⊢
          by_cases ht : t ∈ m.dropped
          · simp [ht] at hs
          · simp only [ht, ite_false, noPanicDtors, Bool.false_eq_true] at hs ⊢
            cases hdt : dt t with
            | true =>
              simp only [hdt, ite_true, List.mem_singleton] at hs
              exact List.mem_cons.mpr (Or.inl hs)
            | false =>
              simp only [hdt, Bool.false_eq_true, ite_false, List.mem_cons] at hs
              rcases hs with rfl | hs
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (exec_sites_subset_noPanicDtors cb dt k j es' _ s hs)
  | .forgetVal k, j, es, m, s, hs => by
      simp only [exec] at hs ⊢
      cases es with
      | nil => simp at hs
      | cons e es' =>
        cases e with
        | guard _ => simp at hs
        | value _ => exact exec_sites_subset_noPanicDtors cb dt k j es' m s hs
  | .pushGuard g k, j, es, m, s, hs => exec_sites_subset_noPanicDtors cb dt k j _ m s hs
  | .setGuard g k, j, es, m, s, hs => by
      simp only [exec] at hs ⊢
      cases es with
      | nil => simp at hs
      | cons e es' =>
        cases e with
        | value _ => simp at hs
        | guard _ => exact exec_sites_subset_noPanicDtors cb dt k j _ m s hs
  | .popGuard k, j, es, m, s, hs => by
      simp only [exec] at hs ⊢
      cases es with
      | nil => simp at hs
      | cons e es' =>
        cases e with
        | value _ => simp at hs
        | guard _ => exact exec_sites_subset_noPanicDtors cb dt k j es' _ s hs
  | .forgetGuard k, j, es, m, s, hs => by
      simp only [exec] at hs ⊢
      cases es with
      | nil => simp at hs
      | cons e es' =>
        cases e with
        | value _ => simp at hs
        | guard _ => exact exec_sites_subset_noPanicDtors cb dt k j es' m s hs
  | .bumpA k, j, es, m, s, hs => exec_sites_subset_noPanicDtors cb dt k j es _ s hs
  | .bumpB k, j, es, m, s, hs => exec_sites_subset_noPanicDtors cb dt k j es _ s hs

/-- Quantifying over all destructor tables in `CallSitesDropSafe` is equivalent to fixing the
non-panicking table. -/
theorem callSitesDropSafe_iff_noPanicDtors (p : Prog) :
    CallSitesDropSafe p ↔
      ∀ (cb : Callback) (m : Mem), Inv m →
        ∀ s ∈ sites cb noPanicDtors p m, DropSafe s.entries s.mem := by
  constructor
  · intro h cb m hm s hs
    exact h cb noPanicDtors m hm s hs
  · intro h cb dt m hm s hs
    exact h cb m hm s (exec_sites_subset_noPanicDtors cb dt p 0 [] m s hs)

/-! ## Tightness of the right-hand side -/

/-- An operation that sets `len` past the buffer and reaches no user code. -/
def badSetLen : Prog := .getLen fun n => .setLen (n + 1) .done

/-- Counterexample (tightness of the `abort` conjunct): `badSetLen` reaches no user-code
site, so `CallSitesDropSafe` holds vacuously; it is not panic-safe under `abort` and not
panic-safe under `unwind` (its normal return violates `Inv`). -/
theorem badSetLen_callSitesDropSafe_not_panicSafe :
    CallSitesDropSafe badSetLen ∧ ¬ PanicSafe .abort badSetLen ∧
    ¬ PanicSafe .unwind badSetLen := by
  refine ⟨?_, ?_, ?_⟩
  · intro cb dt m _ s hs
    simp [sites, exec, badSetLen] at hs
  · intro h
    have := h (tableOf []) noPanicDtors ceMem1 (by decide)
    revert this
    decide
  · intro h
    have := h (tableOf []) noPanicDtors ceMem1 (by decide)
    revert this
    decide

/-- Truncate by one element, dropping it *before* decrementing `len`. -/
def truncateLate : Prog := .getLen fun n =>
  match n with
  | 0 => .done
  | k + 1 => .dropCell k (.setLen k .done)

/-- `truncateLate` is panic-safe under `abort`. -/
theorem truncateLate_panicSafe_abort : PanicSafe .abort truncateLate := by
  intro cb dt m hm
  unfold run
  rcases hlen : m.len with _ | k
  · simp [exec, truncateLate, hlen, ResOk]
    exact hm
  · obtain ⟨t, hbuf, hnd, hinv⟩ := inv_pop m k hm hlen
    simp only [exec, truncateLate, hlen, hbuf, hnd, ite_false]
    cases hdt : dt t
    · simp [ResOk]
      exact hinv
    · simp [panicFrom, ResOk]

/-- `truncateLate` is panic-safe under `unwind` when no destructor panics. -/
theorem truncateLate_panicSafeAssumingNoDtorPanic :
    PanicSafeAssumingNoDtorPanic .unwind truncateLate := by
  intro cb dt m hdt hm
  unfold run
  rcases hlen : m.len with _ | k
  · simp [exec, truncateLate, hlen, ResOk]
    exact hm
  · obtain ⟨t, hbuf, hnd, hinv⟩ := inv_pop m k hm hlen
    simp only [exec, truncateLate, hlen, hbuf, hnd, ite_false, hdt t]
    simp [ResOk]
    exact hinv

/-- `truncateLate` reaches only destructor sites. -/
theorem truncateLate_callbackSitesDropSafe : CallbackSitesDropSafe truncateLate := by
  intro cb dt m hm s hs hk
  unfold sites at hs
  rcases hlen : m.len with _ | k
  · simp [exec, truncateLate, hlen] at hs
  · obtain ⟨t, hbuf, hnd, -⟩ := inv_pop m k hm hlen
    simp only [exec, truncateLate, hlen, hbuf, hnd, ite_false] at hs
    cases hdt : dt t <;> simp [hdt] at hs <;> (subst hs; simp at hk)

/-- Counterexample (destructor sites cannot be dropped from the condition, and the
call-site conjunct cannot be dropped): `truncateLate` is panic-safe under `abort` and all of
its callback sites (there are none) are `DropSafe`, but its destructor site is not, and it
is not panic-safe under `unwind`: if the destructor panics, `len` still covers the dropped
value. -/
theorem truncateLate_counterexample :
    PanicSafe .abort truncateLate ∧ CallbackSitesDropSafe truncateLate ∧
    ¬ CallSitesDropSafe truncateLate ∧ ¬ PanicSafe .unwind truncateLate := by
  refine ⟨truncateLate_panicSafe_abort, truncateLate_callbackSitesDropSafe, ?_, ?_⟩
  · intro h
    have := h (tableOf []) noPanicDtors ceMem1 (by decide)
    revert this
    decide
  · intro h
    have := h (tableOf []) dtPanicsOn0 ceMem1 (by decide)
    revert this
    decide

/-! ## Non-vacuity -/

/-- Truncate by one element with `len` decremented *before* the destructor runs, then call
user code; on an empty container just call user code. -/
def truncateThenCall : Prog := .getLen fun n =>
  match n with
  | 0 => .call fun _ => .done
  | k + 1 => .setLen k (.dropCell k (.call fun _ => .done))

theorem truncateThenCall_panicSafe (mode : Mode) : PanicSafe mode truncateThenCall := by
  intro cb dt m hm
  unfold run
  rcases hlen : m.len with _ | k
  · simp only [exec, truncateThenCall, hlen]
    cases hcb : cb 0 <;> cases mode <;> simp [panicFrom, unwindEntries, ResOk] <;> exact hm
  · obtain ⟨t, hbuf, hnd, hinv⟩ := inv_pop m k hm hlen
    simp only [exec, truncateThenCall, hlen, hbuf, hnd, ite_false]
    cases hdt : dt t
    · cases hcb : cb 0 <;> cases mode <;> simp [panicFrom, unwindEntries, ResOk] <;>
        exact hinv
    · cases mode <;> simp [panicFrom, unwindEntries, ResOk]
      exact hinv

theorem truncateThenCall_callSitesDropSafe : CallSitesDropSafe truncateThenCall := by
  intro cb dt m hm s hs
  unfold sites at hs
  rcases hlen : m.len with _ | k
  · simp only [exec, truncateThenCall, hlen] at hs
    have hs' : s = ⟨.callback, [], m⟩ := by
      cases hcb : cb 0 <;> simp [hcb] at hs <;> exact hs
    subst hs'
    exact (dropSafe_nil_iff_inv m).mpr hm
  · obtain ⟨t, hbuf, hnd, hinv⟩ := inv_pop m k hm hlen
    simp only [exec, truncateThenCall, hlen, hbuf, hnd, ite_false] at hs
    have hs' : s.entries = [] ∧ s.mem = { m with len := k, dropped := t :: m.dropped } := by
      cases hdt : dt t <;> simp [hdt] at hs
      · cases hcb : cb 0 <;> simp [hcb] at hs <;> rcases hs with hs | hs <;> subst hs <;>
          exact ⟨rfl, rfl⟩
      · subst hs; exact ⟨rfl, rfl⟩
    rw [hs'.1, hs'.2]
    exact (dropSafe_nil_iff_inv _).mpr hinv

/-- Non-vacuity witness (both sides hold): `truncateThenCall` is panic-safe under `unwind`
and under `abort`, and all of its user-code sites are `DropSafe`. -/
theorem truncateThenCall_satisfies_both_sides :
    PanicSafe .unwind truncateThenCall ∧ PanicSafe .abort truncateThenCall ∧
    CallSitesDropSafe truncateThenCall :=
  ⟨truncateThenCall_panicSafe .unwind, truncateThenCall_panicSafe .abort,
    truncateThenCall_callSitesDropSafe⟩

/-- `truncateThenCall` reaches both a destructor site and a callback site. -/
theorem truncateThenCall_sites_example :
    (sites (tableOf []) noPanicDtors truncateThenCall ceMem1).map (·.kind) =
      [.destructor, .callback] := by
  decide

/-- Non-vacuity witness (both sides fail): `rawRetain` reaches a callback site that is not
`DropSafe` (the site of `rawRetain_unwind_doubleDrop`), hence is not panic-safe under
`unwind` by the characterization; directly, `rawRetain_unwind_doubleDrop` exhibits the
failing run. -/
theorem rawRetain_not_callSitesDropSafe : ¬ CallSitesDropSafe rawRetain := by
  intro h
  have := h ceCbRemoveThenPanic noPanicDtors ceMem2 (by decide)
  revert this
  decide

/-- Counterexample (tightness of the entry precondition `Inv m` inside `CallSitesDropSafe`):
`truncateThenCall` is panic-safe under `unwind`, yet from the entry state `dupMem`, which
violates `Inv`, it reaches a site that is not `DropSafe`. Without the precondition the
characterization would be false. -/
theorem truncateThenCall_sites_need_inv :
    PanicSafe .unwind truncateThenCall ∧ ¬ Inv dupMem ∧
    ∃ s ∈ sites (tableOf []) noPanicDtors truncateThenCall dupMem, ¬ DropSafe s.entries s.mem := by
  refine ⟨truncateThenCall_panicSafe .unwind, by decide, ?_⟩
  decide

end Toy.PanicSafety
