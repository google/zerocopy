import Toy.Capture.Lang

/-!
# Simulation lemmas for the concrete captures and the equivalence pass

* `capFC_faithfulOnOk`: the fail-closed capture is faithful on its ok-image, for
  either meaning of `opaque` (it never produces `opaque`).
* `capStringify_overApproxOnOk_havoc`: the stringifying capture over-approximates
  on its ok-image when `opaque` means `havoc`.
* `clearReplace_denEquiv`: clearing drop replace flags preserves the source
  denotation of every program.
* `failOpenVariants_eq_partialExtend_capFC`: each fail-open variant agrees with
  `capFC` wherever `capFC` succeeds.
-/

namespace Toy.Capture

/-- Lift a source statement result into a verifier statement result. -/
def liftS : Except Beh St → Except VRes St
  | .ok st => .ok st
  | .error b => .error (.det b)

/-- The capture configurations whose only possible deviation from `cfgFC` is the
stringify field. -/
structure CfgFCExceptAsm (c : CapCfg) : Prop where
  noDefault : c.defaultTrap = false
  noSwallow : c.swallowErrConst = false
  keepCl : c.keepCleanup = true
  keepR : c.keepReason = true

theorem capBlocks_length (c : CapCfg) :
    ∀ (bs : List SBlock) (vbs : List VBlock), capBlocks c bs = .ok vbs →
      vbs.length = bs.length
  | [], vbs, h => by
    simp only [capBlocks, Except.ok.injEq] at h
    subst h; rfl
  | b :: bs, vbs, h => by
    simp only [capBlocks] at h
    cases hb : capBlock c b <;> cases hbs : capBlocks c bs <;> simp [hb, hbs] at h
    subst h
    simp [capBlocks_length c bs _ hbs]

theorem capBlocks_getElem? (c : CapCfg) :
    ∀ (bs : List SBlock) (vbs : List VBlock), capBlocks c bs = .ok vbs → ∀ i : Nat,
      (bs[i]? = none ∧ vbs[i]? = none) ∨
        ∃ b vb, bs[i]? = some b ∧ vbs[i]? = some vb ∧ capBlock c b = .ok vb
  | [], vbs, h, i => by
    simp only [capBlocks, Except.ok.injEq] at h
    subst h; simp
  | b :: bs, vbs, h, i => by
    simp only [capBlocks] at h
    cases hb : capBlock c b <;> cases hbs : capBlocks c bs <;> simp [hb, hbs] at h
    subst h
    cases i with
    | zero => exact Or.inr ⟨b, _, rfl, rfl, hb⟩
    | succ i => simpa using capBlocks_getElem? c bs _ hbs i

theorem capOperand_eval {c : CapCfg} (hc : c.swallowErrConst = false) {o : SOperand}
    {vo : VOperand} (h : capOperand c o = .ok vo) (st : St) :
    vo.eval st = o.eval st := by
  cases o with
  | copy l =>
    simp only [capOperand, Except.ok.injEq] at h
    subst h; rfl
  | const k =>
    cases k with
    | val n =>
      simp only [capOperand, Except.ok.injEq] at h
      subst h; rfl
    | err => simp [capOperand, hc] at h

theorem capStmt_exec {c : CapCfg} (hc : c.swallowErrConst = false) (os : OpaqueSem)
    {s : SStmt} {vs : VStmt} (h : capStmt c s = .ok vs) (st : St) :
    execVStmt os st vs = liftS (execSStmt st s) ∨
      (c.stringifyAsm = true ∧ os = .havoc ∧ execVStmt os st vs = .error .top) ∨
      (c.stringifyAsm = true ∧ os = .noop ∧ ∃ t, s = .asm t) := by
  cases s with
  | assign d o =>
    simp only [capStmt] at h
    cases ho : capOperand c o <;> simp [ho] at h
    subst h
    left
    simp only [execVStmt, execSStmt, capOperand_eval hc ho st]
    cases o.eval st <;> rfl
  | placeMention l =>
    simp only [capStmt, Except.ok.injEq] at h
    subst h; left
    simp only [execVStmt, execSStmt]
    split <;> rfl
  | zstRead l =>
    simp only [capStmt, Except.ok.injEq] at h
    subst h; left
    simp only [execVStmt, execSStmt]
    split <;> rfl
  | emit o =>
    simp only [capStmt] at h
    cases ho : capOperand c o <;> simp [ho] at h
    subst h
    left
    simp only [execVStmt, execSStmt, capOperand_eval hc ho st]
    cases o.eval st <;> rfl
  | asm t =>
    simp only [capStmt] at h
    cases hs : c.stringifyAsm <;> simp [hs] at h
    subst h
    cases os with
    | noop => exact Or.inr (Or.inr ⟨rfl, rfl, t, rfl⟩)
    | havoc => exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)

theorem capStmts_exec {c : CapCfg} (hc : c.swallowErrConst = false) (os : OpaqueSem)
    (hstr : c.stringifyAsm = false ∨ os = .havoc) :
    ∀ (ss : List SStmt) (vss : List VStmt), capStmts c ss = .ok vss → ∀ st,
      execVStmts os vss st = liftS (execSStmts ss st) ∨
        (c.stringifyAsm = true ∧ os = .havoc ∧ execVStmts os vss st = .error .top)
  | [], vss, h, st => by
    simp only [capStmts, Except.ok.injEq] at h
    subst h; left; rfl
  | s :: ss, vss, h, st => by
    simp only [capStmts] at h
    cases hs : capStmt c s <;> cases hss : capStmts c ss <;> simp [hs, hss] at h
    subst h
    rcases capStmt_exec hc os hs st with h1 | ⟨h2, h3, h4⟩ | ⟨h2, h3, _⟩
    · cases hx : execSStmt st s with
      | ok st' =>
        rw [hx] at h1
        simp only [liftS] at h1
        have ih := capStmts_exec hc os hstr ss _ hss st'
        simp only [execVStmts, execSStmts, h1, hx]
        exact ih
      | error b =>
        rw [hx] at h1
        simp only [liftS] at h1
        left
        simp [execVStmts, execSStmts, h1, hx, liftS]
    · right
      exact ⟨h2, h3, by simp [execVStmts, h4]⟩
    · exfalso
      rcases hstr with h5 | h5
      · rw [h2] at h5; cases h5
      · rw [h3] at h5; cases h5

/-- Main simulation: for the configurations that deviate from `cfgFC` at most in
the stringify field, and either without stringify or with `havoc`, the verifier
run of the captured program is the source run, or (only with stringify and
`havoc`) `top`. -/
theorem capWith_runV {c : CapCfg} (hc : CfgFCExceptAsm c) (os : OpaqueSem)
    (hstr : c.stringifyAsm = false ∨ os = .havoc) {p : SProg} {q : VProg}
    (h : capWith c p = .ok q) :
    ∀ n pc st, runV os q n pc st = .det (runS p n pc st) ∨
      (c.stringifyAsm = true ∧ os = .havoc ∧ runV os q n pc st = .top) := by
  have hqb : capBlocks c p.blocks = .ok q.blocks := by
    unfold capWith at h
    cases hb : capBlocks c p.blocks <;> simp [hb] at h
    subst h; rfl
  intro n
  induction n with
  | zero => intro pc st; left; rfl
  | succ n ih =>
    intro pc st
    rcases capBlocks_getElem? c p.blocks q.blocks hqb pc with ⟨h1, h2⟩ | ⟨b, vb, h1, h2, h3⟩
    · left; simp [runV, runS, h1, h2]
    · have hst : ∃ ss t, capStmts c b.stmts = .ok ss ∧ capTerm c b.term = .ok t ∧
          vb = ⟨ss, t, b.cleanup⟩ := by
        unfold capBlock at h3
        cases hs : capStmts c b.stmts <;> cases ht : capTerm c b.term <;> simp [hs, ht] at h3
        exact ⟨_, _, rfl, rfl, by rw [← h3, hc.keepCl]; rfl⟩
      obtain ⟨ss, t, hs, ht, hvb⟩ := hst
      subst hvb
      rcases capStmts_exec hc.noSwallow os hstr b.stmts ss hs st with e1 | ⟨e2, e3, e4⟩
      · cases hx : execSStmts b.stmts st with
        | error bh =>
          rw [hx] at e1
          left
          simp only [runV, runS, h1, h2, hx, e1, liftS]
        | ok st' =>
          rw [hx] at e1
          simp only [liftS] at e1
          simp only [runV, runS, h1, h2, hx, e1]
          cases hterm : b.term with
          | goto t' =>
            rw [hterm] at ht
            simp only [capTerm, Except.ok.injEq] at ht
            subst ht
            exact ih t' st'
          | switchInt o ts ow =>
            rw [hterm] at ht
            simp only [capTerm] at ht
            cases ho : capOperand c o <;> simp [ho] at ht
            subst ht
            simp only [capOperand_eval hc.noSwallow ho st']
            cases o.eval st' with
            | ok v => exact ih _ st'
            | error e => left; rfl
          | ret =>
            rw [hterm] at ht
            simp only [capTerm, Except.ok.injEq] at ht
            subst ht; left; rfl
          | resume =>
            rw [hterm] at ht
            simp only [capTerm, Except.ok.injEq] at ht
            subst ht; left; rfl
          | call pa nx uw =>
            rw [hterm] at ht
            simp only [capTerm, Except.ok.injEq] at ht
            subst ht
            cases pa with
            | false => exact ih nx st'
            | true =>
              cases hcl : b.cleanup with
              | true => left; simp
              | false =>
                cases uw with
                | continueUnwind => left; simp
                | cleanup cl => simpa using ih cl st'
          | drop rep l nx =>
            rw [hterm] at ht
            simp only [capTerm, Except.ok.injEq] at ht
            subst ht
            cases hl : st'.loc l with
            | some v => simpa [hl] using ih nx (st'.set l none)
            | none => left; simp [hl]
          | terminate r =>
            rw [hterm] at ht
            simp only [capTerm, hc.keepR, Except.ok.injEq] at ht
            subst ht; left; simp
          | trap nx =>
            rw [hterm] at ht
            simp [capTerm, hc.noDefault] at ht
          | unreachable =>
            rw [hterm] at ht
            simp only [capTerm, Except.ok.injEq] at ht
            subst ht; left; rfl
      · right
        refine ⟨e2, e3, ?_⟩
        simp [runV, h2, e4]

theorem capWith_fuel {c : CapCfg} {p : SProg} {q : VProg} (h : capWith c p = .ok q) :
    q.fuel = p.fuel := by
  unfold capWith at h
  cases hb : capBlocks c p.blocks <;> simp [hb] at h
  subst h
  simp [VProg.fuel, SProg.fuel, capBlocks_length c _ _ hb]

theorem cfgFC_ok : CfgFCExceptAsm cfgFC := ⟨rfl, rfl, rfl, rfl⟩

/-- The fail-closed capture simulates the source run step for step: at every fuel,
block and state, the verifier run of the captured program is the source run. -/
theorem capFC_runV_eq_runS (os : OpaqueSem) {p : SProg} {q : VProg} (h : capFC p = .ok q) :
    ∀ n pc st, runV os q n pc st = .det (runS p n pc st) := by
  intro n pc st
  rcases capWith_runV cfgFC_ok os (Or.inl rfl) h n pc st with e | ⟨e, _, _⟩
  · exact e
  · cases e

/-- **The fail-closed capture is faithful on its ok-image** (for either meaning of
`opaque`, which it never produces). -/
theorem capFC_faithfulOnOk (os : OpaqueSem) : FaithfulOnOk semS (semV os) capFC := by
  intro p q h ⟨x, b⟩
  have hf := capWith_fuel h
  rcases capWith_runV cfgFC_ok os (Or.inl rfl) h q.fuel 0 (St.init x) with e | ⟨e, _, _⟩
  · simp only [semV, semS, e, VRes.admits]
    rw [hf]
  · cases e

/-- **The stringifying capture over-approximates on its ok-image when `opaque`
means `havoc`.** -/
theorem capStringify_overApproxOnOk_havoc :
    OverApproxOnOk semS (semV .havoc) capStringify := by
  intro p q h ⟨x, b⟩ hb
  have hf := capWith_fuel h
  have hc : CfgFCExceptAsm { cfgFC with stringifyAsm := true } := ⟨rfl, rfl, rfl, rfl⟩
  rcases capWith_runV hc .havoc (Or.inr rfl) h q.fuel 0 (St.init x) with e | ⟨_, _, e⟩
  · simp only [semV, e, VRes.admits]
    rw [hf]; exact hb
  · simp [semV, e, VRes.admits]

theorem runS_clearReplace (p : SProg) :
    ∀ n pc st, runS (clearReplace p) n pc st = runS p n pc st
  | 0, _, _ => rfl
  | n + 1, pc, st => by
    have ih := runS_clearReplace p n
    have hget : (clearReplace p).blocks[pc]? = (p.blocks[pc]?).map clearReplaceBlock := by
      simp [clearReplace]
    simp only [runS]
    rw [hget]
    cases hb : p.blocks[pc]? with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      have hs : (clearReplaceBlock b).stmts = b.stmts := rfl
      have hc : (clearReplaceBlock b).cleanup = b.cleanup := rfl
      rw [hs, hc]
      cases hx : execSStmts b.stmts st with
      | error => rfl
      | ok st' =>
        cases ht : b.term <;> simp [clearReplaceBlock, ht, ih]

/-- **Clearing drop replace flags is an equivalence**: it preserves the source
denotation of every program. -/
theorem clearReplace_denEquiv (p : SProg) : DenEquiv (semS (clearReplace p)) (semS p) := by
  intro ⟨x, b⟩
  have hf : (clearReplace p).fuel = p.fuel := by simp [SProg.fuel, clearReplace]
  simp only [semS, hf, runS_clearReplace]

/-! ## The fail-open variants extend the fail-closed capture -/

theorem capOperand_of_cfgFC (c : CapCfg) {o : SOperand} {vo : VOperand}
    (h : capOperand cfgFC o = .ok vo) : capOperand c o = .ok vo := by
  cases o with
  | copy l => simpa [capOperand] using h
  | const k =>
    cases k with
    | val n => simpa [capOperand] using h
    | err => simp [capOperand, cfgFC] at h

theorem capStmt_of_cfgFC (c : CapCfg) {s : SStmt} {vs : VStmt}
    (h : capStmt cfgFC s = .ok vs) : capStmt c s = .ok vs := by
  cases s with
  | assign d o =>
    simp only [capStmt] at h ⊢
    cases ho : capOperand cfgFC o <;> simp [ho] at h
    subst h
    rw [capOperand_of_cfgFC c ho]
  | emit o =>
    simp only [capStmt] at h ⊢
    cases ho : capOperand cfgFC o <;> simp [ho] at h
    subst h
    rw [capOperand_of_cfgFC c ho]
  | placeMention l => simpa [capStmt] using h
  | zstRead l => simpa [capStmt] using h
  | asm t => simp [capStmt, cfgFC] at h

theorem capStmts_of_cfgFC (c : CapCfg) :
    ∀ (ss : List SStmt) (vss : List VStmt), capStmts cfgFC ss = .ok vss →
      capStmts c ss = .ok vss
  | [], vss, h => by simpa [capStmts] using h
  | s :: ss, vss, h => by
    simp only [capStmts] at h
    cases h1 : capStmt cfgFC s <;> cases h2 : capStmts cfgFC ss <;> simp [h1, h2] at h
    subst h
    simp [capStmts, capStmt_of_cfgFC c h1, capStmts_of_cfgFC c ss _ h2]

theorem capTerm_of_cfgFC {c : CapCfg} (hr : c.keepReason = true) {t : STerm} {vt : VTerm}
    (h : capTerm cfgFC t = .ok vt) : capTerm c t = .ok vt := by
  cases t with
  | switchInt o ts ow =>
    simp only [capTerm] at h ⊢
    cases ho : capOperand cfgFC o <;> simp [ho] at h
    subst h
    rw [capOperand_of_cfgFC c ho]
  | terminate r => simpa [capTerm, hr, cfgFC] using h
  | trap nx => simp [capTerm, cfgFC] at h
  | goto t => simpa [capTerm] using h
  | ret => simpa [capTerm] using h
  | resume => simpa [capTerm] using h
  | call pa nx uw => simpa [capTerm] using h
  | drop rep l nx => simpa [capTerm] using h
  | unreachable => simpa [capTerm] using h

theorem capBlock_of_cfgFC {c : CapCfg} (hcl : c.keepCleanup = true) (hr : c.keepReason = true)
    {b : SBlock} {vb : VBlock} (h : capBlock cfgFC b = .ok vb) : capBlock c b = .ok vb := by
  unfold capBlock at h ⊢
  cases h1 : capStmts cfgFC b.stmts <;> cases h2 : capTerm cfgFC b.term <;> simp [h1, h2] at h
  subst h
  rw [capStmts_of_cfgFC c _ _ h1, capTerm_of_cfgFC hr h2]
  simp [hcl, cfgFC]

theorem capBlocks_of_cfgFC {c : CapCfg} (hcl : c.keepCleanup = true)
    (hr : c.keepReason = true) :
    ∀ (bs : List SBlock) (vbs : List VBlock), capBlocks cfgFC bs = .ok vbs →
      capBlocks c bs = .ok vbs
  | [], vbs, h => by simpa [capBlocks] using h
  | b :: bs, vbs, h => by
    simp only [capBlocks] at h
    cases h1 : capBlock cfgFC b <;> cases h2 : capBlocks cfgFC bs <;> simp [h1, h2] at h
    subst h
    simp [capBlocks, capBlock_of_cfgFC hcl hr h1, capBlocks_of_cfgFC hcl hr bs _ h2]

/-- Every capture configuration that keeps cleanup marks and terminate reasons
agrees with `capFC` wherever `capFC` succeeds. -/
theorem capWith_of_capFC {c : CapCfg} (hcl : c.keepCleanup = true) (hr : c.keepReason = true)
    {p : SProg} {q : VProg} (h : capFC p = .ok q) : capWith c p = .ok q := by
  unfold capFC capWith at h
  unfold capWith
  cases hb : capBlocks cfgFC p.blocks <;> simp [hb] at h
  subst h
  rw [capBlocks_of_cfgFC hcl hr p.blocks _ hb]

/-- The programs on which `capFC` succeeds (the modeled fragment). -/
def capFCAccepts (p : SProg) : Prop := ∃ q, capFC p = .ok q

instance : DecidablePred capFCAccepts := fun p =>
  match h : capFC p with
  | .ok q => isTrue ⟨q, h⟩
  | .error _ => isFalse (by rintro ⟨q, hq⟩; rw [h] at hq; cases hq)

/-- The output of `capFC` on the modeled fragment (an arbitrary program elsewhere). -/
def capFCOut (p : SProg) : VProg :=
  match capFC p with
  | .ok q => q
  | .error _ => ⟨[]⟩

/-- **Each fail-open variant is a partial extension of `capFC`.** `capDefault`,
`capStringify` and `capSwallow` each equal `partialExtend capFCAccepts capFCOut`
applied to themselves: on the programs where `capFC` succeeds they return `capFC`'s
result, and elsewhere they are themselves. -/
theorem failOpenVariants_eq_partialExtend_capFC :
    capDefault = partialExtend capFCAccepts capFCOut capDefault ∧
    capStringify = partialExtend capFCAccepts capFCOut capStringify ∧
    capSwallow = partialExtend capFCAccepts capFCOut capSwallow := by
  have key : ∀ c : CapCfg, c.keepCleanup = true → c.keepReason = true →
      capWith c = partialExtend capFCAccepts capFCOut (capWith c) := by
    intro c hcl hr
    funext p
    unfold partialExtend
    by_cases hp : capFCAccepts p
    · simp only [hp, ↓reduceIte]
      obtain ⟨q, hq⟩ := hp
      have hout : capFCOut p = q := by simp [capFCOut, hq]
      rw [hout]
      exact capWith_of_capFC hcl hr hq
    · simp [hp]
  exact ⟨key _ rfl rfl, key _ rfl rfl, key _ rfl rfl⟩

end Toy.Capture
