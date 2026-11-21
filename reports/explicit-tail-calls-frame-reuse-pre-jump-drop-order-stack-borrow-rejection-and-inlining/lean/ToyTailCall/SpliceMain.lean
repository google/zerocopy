import ToyTailCall.SpliceSimSite

/-!
# Proof support: the corrected call-site splice preserves `frameReuse` observations

Every step of the original run from a related pair is matched by zero or more steps of the
spliced run (`sim_step`); induction on the length of the original run transfers every halted
result whose outcome is neither `ub` nor `stackOverflow`.
-/

namespace Toy.TailCall.SpliceProof

open Toy.TailCall
open Toy.TailCall.EscapeProof

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section
variable {S : Site} {ρ : Nat → Nat × Nat}

theorem top_cases {u : Bool} {stk stk' : List Frame} (h : Top S ρ u stk stk') :
    (∃ F F' os ss, stk = F :: os ∧ stk' = F' :: ss ∧ PlainRel S ρ F F' ∧
      (u = false → F'.pc = F.pc) ∧ Below S ρ os ss) ∨
    (∃ G C M os ss, stk = G :: C :: os ∧ stk' = M :: ss ∧ InlRel S ρ G C M ∧
      C.cont = .store S.dst S.next ∧ (u = false → M.pc = S.gStart + S.K * G.pc) ∧
      Below S ρ os ss) := by
  cases h with
  | plain hP hpc hB => exact Or.inl ⟨_, _, _, _, rfl, rfl, hP, hpc, hB⟩
  | inl hI hc hpc hB => exact Or.inr ⟨_, _, _, _, _, rfl, rfl, hI, hc, hpc, hB⟩

/-- Every original step from a related pair is matched by spliced steps. -/
theorem sim_step {D : Option Nat} {a b : State} (hr : RelAt S ρ a b) :
    ∃ j m, 0 < j ∧ Match S (run .frameReuse D S.p j (.running a))
      (run .frameReuse D S.p' m (.running b)) := by
  rcases top_cases hr.top with ⟨F, F', os, ss, ha, hb, hP, hpc, hB⟩ |
    ⟨G, C, M, os, ss, ha, hb, hI, hc, hpc, hB⟩
  · have c : PlainCtx S ρ a b F F' os ss := ⟨hr, ha, hb, hP, hB⟩
    by_cases hsite : F.fn = S.ci ∧ F.pc = S.k ∧ a.unwinding = false
    · obtain ⟨m, hm⟩ := sim_site (D := D) c (hpc hsite.2.2) hsite.1 hsite.2.1 hsite.2.2
      exact ⟨1, m, Nat.one_pos, by rw [run_one']; exact hm⟩
    · have := sim_plain (D := D) c hpc (fun h1 h2 h3 => hsite ⟨h1, h3, h2⟩)
      exact ⟨1, 1, Nat.one_pos, by rw [run_one', run_one']; exact this⟩
  · have c : InlCtx S ρ a b G C M os ss := ⟨hr, ha, hb, hI, hc, hpc, hB⟩
    cases hu : a.unwinding with
    | true => exact sim_inl_unw c hu
    | false =>
      cases hq : S.gf.code[G.pc]? with
      | none =>
        refine ⟨1, 0, Nat.one_pos, ?_⟩
        rw [run_one', step_code_none c.ha c.fnG hu c.hI.owfG.ret hq]
        exact match_ub a
      | some i =>
        cases i with
        | ret op =>
          obtain ⟨m, hm⟩ := sim_inl_ret (D := D) c hu hq
          exact ⟨1, m, Nat.one_pos, by rw [run_one']; exact hm⟩
        | tailCall h as =>
          obtain ⟨m, hm⟩ := sim_inl_tail (D := D) c hu hq
          exact ⟨1, m, Nat.one_pos, by rw [run_one']; exact hm⟩
        | _ =>
          exact ⟨1, 1, Nat.one_pos, by
            rw [run_one', run_one']
            exact sim_inl_simple c hu hq (by intro op h; cases h) (by intro h as e; cases e)⟩

theorem run_det' {sem : Sem} {D : Option Nat} {p : Prog} {c : Conf} {m k : Nat} {r r' : Result}
    (h1 : run sem D p m c = .halted r) (h2 : run sem D p k c = .halted r') : r = r' := by
  rcases Nat.lt_or_ge m k with hlt | hge
  · have := run_mono sem D p m (k - m) _ _ h1
    rw [show m + (k - m) = k by omega, h2] at this
    exact (Conf.halted.inj this).symm
  · have := run_mono sem D p k (m - k) _ _ h2
    rw [show k + (m - k) = m by omega, h1] at this
    exact Conf.halted.inj this

theorem fwd {D : Option Nat} (N : Nat) :
    ∀ (n : Nat) (ρ : Nat → Nat × Nat) (a b : State) (ra : Result), n ≤ N → RelAt S ρ a b →
      run .frameReuse D S.p n (.running a) = .halted ra → ra.outcome ≠ .ub →
      ra.outcome ≠ .stackOverflow →
      ∃ m rb, run .frameReuse D S.p' m (.running b) = .halted rb ∧
        rb.outcome = ra.outcome ∧ rb.events = ra.events := by
  induction N with
  | zero =>
    intro n ρ a b ra hn _ h _ _
    have : n = 0 := by omega
    subst this
    simp [run] at h
  | succ N ih =>
    intro n ρ a b ra hnN hr hn hub hso
    obtain ⟨j, m, hj, hk⟩ := sim_step (D := D) hr
    rcases hk with ⟨a', b', ha', hb', ρ', hr'⟩ | ⟨ra', rb, ha', hb', ho, he⟩ | ⟨ra', ha', ho⟩
    · rcases Nat.lt_or_ge n j with hlt | hge
      · exfalso
        have := run_mono .frameReuse D S.p n (j - n) _ _ hn
        rw [show n + (j - n) = j by omega, ha'] at this
        cases this
      · have h2 : run .frameReuse D S.p (n - j) (.running a') = .halted ra := by
          rw [← ha', ← run_add, show j + (n - j) = n by omega]
          exact hn
        obtain ⟨m', rb, hm', ho, he⟩ := ih (n - j) ρ' a' b' ra (by omega) hr' h2 hub hso
        exact ⟨m + m', rb, by rw [run_add, hb']; exact hm', ho, he⟩
    · have := run_det' ha' hn
      subst this
      exact ⟨m, rb, hb', ho.symm, he.symm⟩
    · have := run_det' ha' hn
      subst this
      rcases ho with ho | ho
      · exact absurd ho hub
      · exact absurd ho hso

/-- The corrected splice at a well-formed call site preserves every `frameReuse` outcome other
than `ub` and `stackOverflow`, with its event trace. -/
theorem preserves_site (S : Site) (D : Option Nat) (o : Outcome) (es : List Event)
    (hub : o ≠ .ub) (hso : o ≠ .stackOverflow) :
    Observes .frameReuse D S.p o es → Observes .frameReuse D S.p' o es := by
  rintro ⟨ra, ⟨n, hn⟩, ho, he⟩
  have hst : Match S (start D S.p) (start D S.p') :=
    match_push (ρ := fun _ => (0, 0)) (D := D) (a1 := State.empty) (b1 := State.empty)
      (os := []) (ss := []) (f := 0) (vs := []) .nil (by simp) (by simp) (by simp) (by simp) rfl rfl
      rfl
  rcases hst with ⟨a, b, ha, hb, ρ, hr⟩ | ⟨ra', rb, ha, hb, ho', he'⟩ | ⟨ra', ha, ho'⟩
  · rw [ha] at hn
    obtain ⟨m, rb, hm, ho2, he2⟩ :=
      fwd (S := S) n n ρ a b ra (Nat.le_refl _) hr hn (by rw [ho]; exact hub) (by rw [ho]; exact hso)
    exact ⟨rb, ⟨m, by rw [hb]; exact hm⟩, by rw [ho2, ho], by rw [he2, he]⟩
  · rw [ha, run_halted] at hn
    cases hn
    exact ⟨rb, ⟨0, hb⟩, by rw [← ho', ho], by rw [← he', he]⟩
  · rw [ha, run_halted] at hn
    cases hn
    rcases ho' with ho' | ho'
    · exact absurd (ho'.symm.trans ho) (Ne.symm hub)
    · exact absurd (ho'.symm.trans ho) (Ne.symm hso)

end

theorem inline_cases (p : Prog) (ci k : Nat) :
    inlineCallSite .corrected p ci k = p ∨
      ∃ S : Site, S.p = p ∧ inlineCallSite .corrected p ci k = S.p' := by
  unfold inlineCallSite
  split
  · exact Or.inl rfl
  · next c hc =>
    split
    · next g args dst next hk =>
      split
      · exact Or.inl rfl
      · next hgci =>
        split
        · exact Or.inl rfl
        · next gf hg =>
          split
          · next hcond =>
            exact Or.inr ⟨⟨p, ci, k, c, g, gf, args, dst, next, hc, hk, hgci, hg, hcond.1, hcond.2.1,
              hcond.2.2⟩, rfl, rfl⟩
          · exact Or.inl rfl
    · exact Or.inl rfl

/-- Card R15. -/
theorem preserves (p : Prog) (ci k : Nat) (D : Option Nat) (o : Outcome) (es : List Event)
    (hub : o ≠ .ub) (hso : o ≠ .stackOverflow) :
    Observes .frameReuse D p o es → Observes .frameReuse D (inlineCallSite .corrected p ci k) o es := by
  intro h
  rcases inline_cases p ci k with he | ⟨S, hp, he⟩
  · rw [he]; exact h
  · rw [he]; subst hp; exact preserves_site S D o es hub hso h

end Toy.TailCall.SpliceProof
