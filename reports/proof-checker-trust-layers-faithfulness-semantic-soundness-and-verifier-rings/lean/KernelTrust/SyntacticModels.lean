/-
  Toy.KernelTrust.SyntacticModels

  Countermodels for the propositional closure conditions, built on free
  polymodal syntax or on two truth values:
  * `noMpFamily`: every condition of K4a holds except modus ponens;
  * `noKSFamily`: every condition of K4a holds except the axiom schemes K and S;
  * `noMpEfqFamily`: every hypothesis of K5 / K5-iff holds except modus ponens;
  * `noEfqBoolFamily`: every hypothesis of K5 / K5-iff holds except ex falso.

  These are abstract structures, not arithmetical theories.
-/
import KernelTrust.Kripke

namespace Toy.KernelTrust

/-- Syntactic polymodal sentences over `n` theories. -/
inductive SynSent (n : Nat) : Type where
  | bot : SynSent n
  | imp : SynSent n → SynSent n → SynSent n
  | box : Fin n → SynSent n → SynSent n

/-- Structural size of syntactic sentences. -/
def SynSent.size {n : Nat} : SynSent n → Nat
  | .bot => 1
  | .imp a b => 1 + a.size + b.size
  | .box _ a => 1 + a.size

/-! ## Modus ponens is necessary for K4a -/

/-- The least theorem sets closed under the axiom schemes K, S, ex falso, the
cross-theory conditions and the ring hypothesis, and under cross-necessitation,
but *not* under modus ponens. -/
inductive NoMpThm (n : Nat) : Fin n → SynSent n → Prop where
  | axK : ∀ i A B, NoMpThm n i (.imp A (.imp B A))
  | axS : ∀ i A B C,
      NoMpThm n i (.imp (.imp A (.imp B C)) (.imp (.imp A B) (.imp A C)))
  | efq : ∀ i A, NoMpThm n i (.imp .bot A)
  | distrib : ∀ i j A B,
      NoMpThm n i (.imp (.box j (.imp A B)) (.imp (.box j A) (.box j B)))
  | sigma1 : ∀ i j k A,
      NoMpThm n i (.imp (.box k A) (.box j (.box k A)))
  | ring : ∀ i, NoMpThm n i (.imp (.box (ringNext i) .bot) .bot)
  | nec : ∀ i j A, NoMpThm n j A → NoMpThm n i (.box j A)

/-- The family of `NoMpThm`. -/
def noMpFamily (n : Nat) : ProvFamily (Fin n) where
  Sent := SynSent n
  bot  := .bot
  imp  := .imp
  box  := .box
  Thm  := NoMpThm n

/-- **Modus ponens is necessary for K4a and K4a-local.**  For every `n ≥ 2`,
`noMpFamily n` satisfies the axiom schemes K and S, ex falso, Löb's rule and
Gödel's second incompleteness property for every theory, the full cross-theory
conditions, and the ring hypothesis, and every theory is consistent; modus
ponens (hence `ImpClosed`) fails at every theory. -/
theorem consistencyRing_consistent_without_mp (n : Nat) (hn : 2 ≤ n) :
    (∀ i A B, (noMpFamily n).Thm i ((noMpFamily n).imp A ((noMpFamily n).imp B A))) ∧
    (∀ i A B C, (noMpFamily n).Thm i
      ((noMpFamily n).imp ((noMpFamily n).imp A ((noMpFamily n).imp B C))
        ((noMpFamily n).imp ((noMpFamily n).imp A B) ((noMpFamily n).imp A C)))) ∧
    (∀ i, (noMpFamily n).HasEfq i) ∧
    (∀ i, (noMpFamily n).LobRule i) ∧
    (∀ i, (noMpFamily n).GodelII i) ∧
    (noMpFamily n).CrossHBL ∧
    (∀ i, (noMpFamily n).Thm i ((noMpFamily n).con (ringNext i))) ∧
    (∀ i, (noMpFamily n).Consistent i) ∧
    ¬ (∀ i, (noMpFamily n).Thm i (noMpFamily n).bot) ∧
    (∀ i, ¬ (noMpFamily n).MpClosed i) ∧
    (∀ i, ¬ (noMpFamily n).ImpClosed i) := by
  have hLob : ∀ i, (noMpFamily n).LobRule i := by
    intro i A h
    have hnot : ∀ s, NoMpThm n i s → s ≠ .imp (.box i A) A := by
      intro s hs heq
      cases hs with
      | axK _ X Y =>
        injection heq with h1 h2
        have hY : SynSent.imp Y (.box i A) = A := h1 ▸ h2
        have hsz := congrArg SynSent.size hY
        simp [SynSent.size] at hsz
        omega
      | axS _ _ _ _ => cases heq
      | efq _ _ => cases heq
      | distrib _ j X Y =>
        injection heq with h1 h2
        injection h1 with _ hA1
        have hXY : SynSent.imp X Y = SynSent.imp (.box j X) (.box j Y) := hA1.trans h2.symm
        injection hXY with hx _
        have hsz := congrArg SynSent.size hx
        simp [SynSent.size] at hsz
      | sigma1 _ j k X =>
        injection heq with h1 h2
        injection h1 with _ hA1
        have hX : X = .box j (.box k X) := hA1.trans h2.symm
        have hsz := congrArg SynSent.size hX
        simp [SynSent.size] at hsz
        omega
      | ring _ =>
        injection heq with h1 _
        injection h1 with hne _
        exact ringNext_ne_self hn i hne
      | nec _ _ _ _ => cases heq
    exact absurd rfl (hnot _ h)
  have hNoMp : ∀ i, ¬ (noMpFamily n).MpClosed i := by
    intro i hmp
    let j := ringNext i
    let k := ringNext j
    have hdist : NoMpThm n i (.imp (.box j (.imp (.box k .bot) .bot))
        (.imp (.box j (.box k .bot)) (.box j .bot))) := .distrib i j (.box k .bot) .bot
    have hnec : NoMpThm n i (.box j (.imp (.box k .bot) .bot)) := .nec i j _ (.ring j)
    have hq : NoMpThm n i (.imp (.box j (.box k .bot)) (.box j .bot)) := hmp hdist hnec
    have hnot : ∀ s, NoMpThm n i s → s ≠ .imp (.box j (.box k .bot)) (.box j .bot) := by
      intro s hs heq
      cases hs with
      | axK _ _ _ => cases heq
      | axS _ _ _ _ => cases heq
      | efq _ _ => cases heq
      | distrib _ _ _ _ => cases heq
      | sigma1 _ j' k' X =>
        injection heq with h1 h2
        have hsz1 := congrArg SynSent.size h1
        have hsz2 := congrArg SynSent.size h2
        simp [SynSent.size] at hsz1 hsz2
        omega
      | ring _ => cases heq
      | nec _ _ _ _ => cases heq
    exact absurd rfl (hnot _ hq)
  have hcons : ∀ i, (noMpFamily n).Consistent i := fun i h => by cases h
  exact ⟨fun i A B => .axK i A B, fun i A B C => .axS i A B C, fun i A => .efq i A,
    hLob, fun i => (hLob i).godelII,
    ⟨fun i j A h => .nec i j A h, fun i j A B => .distrib i j A B,
     fun i j k A => .sigma1 i j k A⟩,
    fun i => .ring i, hcons, fun h => hcons ⟨0, by omega⟩ (h _),
    hNoMp, fun i h => hNoMp i h.mp⟩

/-! ## The axiom schemes K and S are necessary for K4a -/

/-- A non-transitive implication: theory `i` proves `A → B` when proving `A`
gives `B`, *unless* `A` is literally `□ᵢB`.  This blocks Löb's premise
`□ᵢB → B` and, with it, the axiom schemes K and S. -/
def NoKSThm (n : Nat) : Fin n → SynSent n → Prop
  | _, .bot     => False
  | _, .box j A => NoKSThm n j A
  | i, .imp A B => (NoKSThm n i A → NoKSThm n i B) ∧ (A ≠ .box i B)

/-- The family of `NoKSThm`. -/
def noKSFamily (n : Nat) : ProvFamily (Fin n) where
  Sent := SynSent n
  bot  := .bot
  imp  := .imp
  box  := .box
  Thm  := NoKSThm n

/-- **The axiom schemes K and S are necessary for K4a and K4a-local.**  For
every `n ≥ 2`, `noKSFamily n` satisfies modus ponens, ex falso, Löb's rule and
Gödel's second incompleteness property for every theory, the full cross-theory
conditions, and the ring hypothesis, and every theory is consistent; the axiom
schemes K and S (hence `ImpClosed`) fail at every theory. -/
theorem consistencyRing_consistent_without_axK_axS (n : Nat) (hn : 2 ≤ n) :
    (∀ i, (noKSFamily n).MpClosed i) ∧
    (∀ i, (noKSFamily n).HasEfq i) ∧
    (∀ i, (noKSFamily n).LobRule i) ∧
    (∀ i, (noKSFamily n).GodelII i) ∧
    (noKSFamily n).CrossHBL ∧
    (∀ i, (noKSFamily n).Thm i ((noKSFamily n).con (ringNext i))) ∧
    (∀ i, (noKSFamily n).Consistent i) ∧
    ¬ (∀ i, (noKSFamily n).Thm i (noKSFamily n).bot) ∧
    (∀ i, ¬ ∀ A B, (noKSFamily n).Thm i ((noKSFamily n).imp A ((noKSFamily n).imp B A))) ∧
    (∀ i, ¬ ∀ A B C, (noKSFamily n).Thm i
      ((noKSFamily n).imp ((noKSFamily n).imp A ((noKSFamily n).imp B C))
        ((noKSFamily n).imp ((noKSFamily n).imp A B) ((noKSFamily n).imp A C)))) ∧
    (∀ i, ¬ (noKSFamily n).ImpClosed i) := by
  have hLob : ∀ i, (noKSFamily n).LobRule i := fun _ _ h => absurd rfl h.2
  have hcons : ∀ i, (noKSFamily n).Consistent i := fun _ h => h
  have hNoK : ∀ i, ¬ ∀ A B, (noKSFamily n).Thm i ((noKSFamily n).imp A ((noKSFamily n).imp B A)) := by
    intro i hK
    have hTop : NoKSThm n i (.imp .bot .bot) := ⟨False.elim, fun h => by cases h⟩
    have h1 := (hK (.imp .bot .bot) (.box i (.imp .bot .bot))).1 hTop
    exact h1.2 rfl
  refine ⟨fun _ _ _ hAB hA => hAB.1 hA,
          fun _ _ => ⟨False.elim, fun h => by cases h⟩,
          hLob, fun i => (hLob i).godelII,
          ⟨fun _ _ _ h => h, ?_, ?_⟩,
          fun i => ⟨False.elim, fun h => by
            injection h with hne _
            exact ringNext_ne_self hn i hne⟩,
          hcons, fun h => hcons ⟨0, by omega⟩ (h _),
          hNoK, ?_, fun i h => hNoK i h.axK⟩
  · intro i j A B
    refine ⟨fun hAB => ⟨fun hA => hAB.1 hA, fun heq => ?_⟩, fun heq => ?_⟩
    · injection heq with hji hAb
      subst hji
      exact hAB.2 hAb
    · have hs := congrArg SynSent.size heq
      simp [noKSFamily, SynSent.size] at hs
      omega
  · intro i j k A
    refine ⟨fun h => h, fun heq => ?_⟩
    have hs := congrArg SynSent.size heq
    simp [noKSFamily, SynSent.size] at hs
    omega
  · intro i hS
    have h1 : NoKSThm n i (.imp (.box i .bot) (.imp (.imp .bot .bot) .bot)) :=
      ⟨False.elim, fun heq => by
        have hs := congrArg SynSent.size heq
        simp [SynSent.size] at hs⟩
    have h2 : NoKSThm n i (.imp (.box i .bot) (.imp .bot .bot)) :=
      ⟨False.elim, fun heq => by
        have hs := congrArg SynSent.size heq
        simp [SynSent.size] at hs⟩
    have h3 := ((hS (.box i .bot) (.imp .bot .bot) .bot).1 h1).1 h2
    exact h3.2 rfl

/-! ## Modus ponens is necessary for K5 and K5-iff -/

/-- A theory that proves exactly `⊥` and the ex falso instances `⊥ → A`. -/
def noMpEfqFamily : ProvFamily (Fin 1) where
  Sent := SynSent 1
  bot  := .bot
  imp  := .imp
  box  := .box
  Thm  := fun _ s => s = .bot ∨ ∃ A, s = .imp .bot A

/-- **K5 and K5-iff without modus ponens.**  The theory of `noMpEfqFamily` has
ex falso, is inconsistent, and has Gödel's second incompleteness property
(trivially, being inconsistent); modus ponens fails; and it proves no instance
of the local reflection schema, so both K5 and K5-iff fail. -/
theorem local_reflection_fails_without_mp :
    noMpEfqFamily.HasEfq 0 ∧
    noMpEfqFamily.Thm 0 noMpEfqFamily.bot ∧
    noMpEfqFamily.GodelII 0 ∧
    ¬ noMpEfqFamily.MpClosed 0 ∧
    ¬ (∀ (j : Fin 1) (A : noMpEfqFamily.Sent),
        noMpEfqFamily.Thm 0 (noMpEfqFamily.imp (noMpEfqFamily.box j A) A)) ∧
    ¬ ((∀ A : noMpEfqFamily.Sent,
          noMpEfqFamily.Thm 0 (noMpEfqFamily.imp (noMpEfqFamily.box 0 A) A)) ↔
        noMpEfqFamily.Thm 0 noMpEfqFamily.bot) := by
  have hnorefl : ¬ noMpEfqFamily.Thm 0
      (noMpEfqFamily.imp (noMpEfqFamily.box 0 noMpEfqFamily.bot) noMpEfqFamily.bot) := by
    rintro (h | ⟨A, h⟩)
    · cases h
    · injection h with h1 _
      cases h1
  refine ⟨fun A => .inr ⟨A, rfl⟩, .inl rfl, fun _ => .inl rfl, ?_, fun h => hnorefl (h 0 _),
    fun h => hnorefl (h.mpr (.inl rfl) _)⟩
  intro hmp
  have h := @hmp SynSent.bot (.imp (.box 0 .bot) .bot) (.inr ⟨_, rfl⟩) (.inl rfl)
  exact hnorefl h

/-! ## Ex falso is necessary for K5 and K5-iff -/

/-- A two-valued "paraconsistent" theory: sentences are Booleans, `⊥` is
`true`, implication is classical, every box is `true`, and the theory proves
exactly `true`.  It proves `⊥` but not every sentence. -/
def noEfqBoolFamily : ProvFamily Unit where
  Sent := Bool
  bot  := true
  imp  := fun a b => (!a) || b
  box  := fun _ _ => true
  Thm  := fun _ s => s = true

/-- **K5 and K5-iff without ex falso.**  The theory of `noEfqBoolFamily` is
closed under modus ponens and the axiom schemes K and S, satisfies Löb's rule
and Gödel's second incompleteness property, and is inconsistent; ex falso
fails, and so do K5 (it does not prove `□A → A` for `A := false`) and the
equivalence of K5-iff. -/
theorem local_reflection_fails_without_efq :
    noEfqBoolFamily.MpClosed () ∧
    (∀ A B, noEfqBoolFamily.Thm () (noEfqBoolFamily.imp A (noEfqBoolFamily.imp B A))) ∧
    (∀ A B C, noEfqBoolFamily.Thm ()
      (noEfqBoolFamily.imp (noEfqBoolFamily.imp A (noEfqBoolFamily.imp B C))
        (noEfqBoolFamily.imp (noEfqBoolFamily.imp A B) (noEfqBoolFamily.imp A C)))) ∧
    noEfqBoolFamily.LobRule () ∧
    noEfqBoolFamily.GodelII () ∧
    noEfqBoolFamily.Thm () noEfqBoolFamily.bot ∧
    ¬ noEfqBoolFamily.HasEfq () ∧
    ¬ (∀ (j : Unit) (A : noEfqBoolFamily.Sent),
        noEfqBoolFamily.Thm () (noEfqBoolFamily.imp (noEfqBoolFamily.box j A) A)) ∧
    ¬ ((∀ A : noEfqBoolFamily.Sent,
          noEfqBoolFamily.Thm () (noEfqBoolFamily.imp (noEfqBoolFamily.box () A) A)) ↔
        noEfqBoolFamily.Thm () noEfqBoolFamily.bot) := by
  have hLob : noEfqBoolFamily.LobRule () := by
    intro A hA; cases A <;> simp_all [noEfqBoolFamily]
  refine ⟨?_, ?_, ?_, hLob, hLob.godelII, rfl, ?_, ?_, ?_⟩
  · intro A B hAB hA; cases A <;> cases B <;> simp_all [noEfqBoolFamily]
  · intro A B; cases A <;> cases B <;> rfl
  · intro A B C; cases A <;> cases B <;> cases C <;> rfl
  · intro hefq; have h := hefq false; cases h
  · intro hrefl; have h := hrefl () false; cases h
  · intro hiff; have h := hiff.mpr rfl false; cases h

/-- Negative example (`MpClosed`): `noMpFamily 2`. -/
theorem ex_mpClosed_neg : ¬ (noMpFamily 2).MpClosed 0 :=
  (consistencyRing_consistent_without_mp 2 (Nat.le_refl 2)).2.2.2.2.2.2.2.2.2.1 0

/-- Positive example (`MpClosed`): every Kripke family. -/
theorem ex_mpClosed_pos : (constFamily Unit).MpClosed () :=
  ((constModel Unit).toFamily_impClosed ()).mp

/-! ## The consistency form of K5 without modus ponens or ex falso -/

/-- **K5, consistency form, without modus ponens.**  The theory of
`noMpEfqFamily` has ex falso and is inconsistent, modus ponens fails, and it
does not prove its own consistency statement `□₀⊥ → ⊥`, so the conclusion of
`inconsistent_proves_every_con_of_mp_efq` fails. -/
theorem con_fails_without_mp :
    noMpEfqFamily.HasEfq 0 ∧
    noMpEfqFamily.Thm 0 noMpEfqFamily.bot ∧
    ¬ noMpEfqFamily.MpClosed 0 ∧
    ¬ (∀ j : Fin 1, noMpEfqFamily.Thm 0 (noMpEfqFamily.con j)) := by
  have h := local_reflection_fails_without_mp
  refine ⟨h.1, h.2.1, h.2.2.2.1, fun hcon => ?_⟩
  rcases hcon 0 with h' | ⟨A, h'⟩
  · cases h'
  · injection h' with h1 _
    cases h1

/-- A one-theory family over free syntax whose theory proves exactly `⊥`. -/
def onlyBotFamily : ProvFamily Unit where
  Sent := SynSent 1
  bot  := .bot
  imp  := .imp
  box  := fun _ => .box 0
  Thm  := fun _ s => s = .bot

/-- **K5, consistency form, without ex falso.**  The theory of `onlyBotFamily`
is closed under modus ponens (vacuously) and inconsistent; ex falso fails, and
so does the axiom scheme K; and it proves no consistency statement, so the
conclusion of `inconsistent_proves_every_con_of_mp_efq` fails.  (With the axiom
scheme K in place of ex falso the consistency form would hold again; compare
`local_reflection_fails_without_efq`, whose theory has K.) -/
theorem con_fails_without_efq :
    onlyBotFamily.MpClosed () ∧
    onlyBotFamily.Thm () onlyBotFamily.bot ∧
    ¬ onlyBotFamily.HasEfq () ∧
    ¬ (∀ A B : onlyBotFamily.Sent,
        onlyBotFamily.Thm () (onlyBotFamily.imp A (onlyBotFamily.imp B A))) ∧
    ¬ (∀ j : Unit, onlyBotFamily.Thm () (onlyBotFamily.con j)) := by
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · intro A B hAB _
    cases hAB
  · intro h
    cases h .bot
  · intro h
    cases h .bot .bot
  · intro h
    cases h ()

end Toy.KernelTrust
