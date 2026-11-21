import ToyInline.ScopeLemmas

/-!
# Simulation proof for call-site inlining (fully proved)

Auxiliary definitions and lemmas used by the proofs of the four whole-program inlining
theorems in `ToyInline/Results.lean`. The proof is a stuttering forward simulation: every step
of the original program is matched by one or more steps of the inlined program with the same
events, and the two machines are deterministic, so the simulation yields behavioural
equivalence in both directions.

The stack relation pairs each frame of the original program with one frame of the inlined
program, except that a callee frame of the inlined call together with the suspended caller
frame below it (a *merged segment*) is paired with the single merged frame of the inlined
program.
-/

namespace Toy.Inline
namespace InlineSim

/-! ## `nth?` as `getElem?` -/

theorem nth?_eq_getElem? {α : Type} : ∀ (l : List α) (i : Nat), nth? l i = l[i]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: as, i + 1 => by simp only [nth?, List.getElem?_cons_succ]; exact nth?_eq_getElem? as i

theorem nth?_map {α β : Type} (g : α → β) (l : List α) (i : Nat) :
    nth? (l.map g) i = (nth? l i).map g := by
  simp only [nth?_eq_getElem?, List.getElem?_map]

/-! ## The data of one inlining step -/

/-- The objects of one inlining step. `loose` is the host local that may differ between the two
machines after an unwind out of the inlined body (`some ci.dest` in destination mode, `none` in
temporary mode). -/
structure Site where
  p : Program
  f : Nat
  b : Nat
  F : Fn
  B : Block
  ci : CallInfo
  G : Fn
  cfg : InlineCfg
  loose : Option Local

namespace Site

variable (S : Site)

def ρ : Nat → Local := S.cfg.rename S.ci.dest

def nb : Nat := S.F.blocks.length

def base : Nat := S.F.blocks.length + (match S.ci.target with | some _ => 1 | none => 0)

def retBlock (t : BlockId) : Block :=
  { stmts := retStmts S.cfg S.ci, term := .goto t,
    isCleanup := ((nth? S.F.blocks t).map Block.isCleanup).getD false }

def rb : List Block := (S.ci.target.map (fun t => [S.retBlock t])).getD []

def ctx : SpliceCtx :=
  { ρ := S.ρ, base := S.base, ns := S.F.scopes.length, retBlk := S.ci.target.map (fun _ => S.nb),
    callUnwind := S.ci.unwind, redirectContinue := S.cfg.redirectContinue,
    resumeMap := S.cfg.resumeMap }

def prol : List Stmt := prologue S.ρ S.ci.args S.G.nlocals

def callBlk : Block :=
  { stmts := S.B.stmts ++ S.prol, term := .goto S.base, isCleanup := S.B.isCleanup }

def F' : Fn := inlineFn S.F S.b S.B S.ci S.G S.cfg

def q : Program := { S.p with fns := S.p.fns.set S.f S.F' }


theorem F'_caps : S.F'.caps = S.F.caps := rfl
theorem F'_trackCaller : S.F'.trackCaller = S.F.trackCaller := rfl
theorem F'_scopes : S.F'.scopes = S.F.scopes ++ linkScopes S.cfg.link S.F S.ci S.G := rfl

theorem rb_length : S.rb.length = (match S.ci.target with | some _ => 1 | none => 0) := by
  unfold rb; cases S.ci.target <;> rfl

theorem F'_blocks_prefix_len : ((S.F.blocks.set S.b S.callBlk) ++ S.rb).length = S.base := by
  simp [rb_length, base]

theorem F'_blocks : S.F'.blocks = (S.F.blocks.set S.b S.callBlk) ++ S.rb ++ S.G.blocks.map S.ctx.block := by
  unfold F' inlineFn rb retBlock callBlk prol ctx ρ base nb
  cases S.ci.target <;> rfl

theorem nth?_F'_lt (blk : Nat) (hlt : blk < S.nb) (hne : blk ≠ S.b) :
    nth? S.F'.blocks blk = nth? S.F.blocks blk := by
  rw [F'_blocks, nth?_eq_getElem?, nth?_eq_getElem?, List.append_assoc,
    List.getElem?_append_left (by simpa [nb] using hlt), List.getElem?_set_ne (Ne.symm hne)]

theorem nth?_F'_b (hb : S.b < S.nb) : nth? S.F'.blocks S.b = some S.callBlk := by
  rw [F'_blocks, nth?_eq_getElem?, List.append_assoc,
    List.getElem?_append_left (by simpa [nb] using hb), List.getElem?_set_self (by simpa [nb] using hb)]

theorem nth?_F'_nb (t : BlockId) (ht : S.ci.target = some t) :
    nth? S.F'.blocks S.nb = some (S.retBlock t) := by
  rw [F'_blocks, nth?_eq_getElem?, List.append_assoc]
  rw [List.getElem?_append_right (by simp [nb])]
  simp [ht, nb, rb]

theorem nth?_F'_base (j : Nat) :
    nth? S.F'.blocks (j + S.base) = (nth? S.G.blocks j).map S.ctx.block := by
  rw [F'_blocks, nth?_eq_getElem?, nth?_eq_getElem?]
  rw [List.getElem?_append_right (by rw [F'_blocks_prefix_len]; omega), F'_blocks_prefix_len]
  simp

theorem b_lt_nb (hB : nth? S.F.blocks S.b = some S.B) : S.b < S.nb :=
  nth?_lt_length _ _ _ hB

theorem nth?_q_fns (hf : S.f < S.p.fns.length) (g : Nat) :
    nth? S.q.fns g = if g = S.f then some S.F' else nth? S.p.fns g := by
  simp only [q, nth?_eq_getElem?]
  by_cases hg : g = S.f
  · subst hg; simp [List.getElem?_set_self hf]
  · simp [hg, List.getElem?_set_ne (Ne.symm hg)]

theorem q_tracked (hF : nth? S.p.fns S.f = some S.F) : S.q.tracked = S.p.tracked := by
  have hf : S.f < S.p.fns.length := nth?_lt_length _ _ _ hF
  funext g
  simp only [Program.tracked, S.nth?_q_fns hf g]
  by_cases hg : g = S.f
  · subst hg; simp [hF, F'_trackCaller]
  · simp [hg]

theorem q_abi : S.q.abi = S.p.abi := rfl

end Site

/-! ## Running a fixed number of steps -/

/-- `stepN q k c`: the configuration after `k` steps of `q` from `c` (stopping early at a halted
configuration) and the events emitted on the way. -/
def stepN (q : Program) : Nat → Config → Config × List Event
  | 0, c => (c, [])
  | _ + 1, .halted o => (.halted o, [])
  | k + 1, .running s =>
    ((stepN q k (step .walk q s).1).1, (step .walk q s).2 ++ (stepN q k (step .walk q s).1).2)

theorem stepN_zero (q : Program) (c : Config) : stepN q 0 c = (c, []) := by
  cases c <;> rfl

theorem stepN_succ_running (q : Program) (k : Nat) (s : List Frame) :
    stepN q (k + 1) (.running s) =
      ((stepN q k (step .walk q s).1).1, (step .walk q s).2 ++ (stepN q k (step .walk q s).1).2) :=
  rfl

theorem stepN_one (q : Program) (s : List Frame) :
    stepN q 1 (.running s) = step .walk q s := by
  rw [stepN_succ_running, stepN_zero]; simp

theorem stepN_add (q : Program) : ∀ (k₁ k₂ : Nat) (c : Config),
    stepN q (k₁ + k₂) c =
      ((stepN q k₂ (stepN q k₁ c).1).1, (stepN q k₁ c).2 ++ (stepN q k₂ (stepN q k₁ c).1).2)
  | 0, k₂, c => by simp [stepN_zero]
  | k₁ + 1, k₂, .halted o => by
    rw [show k₁ + 1 + k₂ = (k₁ + k₂) + 1 by omega]
    cases k₂ <;> rfl
  | k₁ + 1, k₂, .running s => by
    rw [show k₁ + 1 + k₂ = (k₁ + k₂) + 1 by omega, stepN_succ_running, stepN_succ_running,
      stepN_add q k₁ k₂]
    simp

theorem run_stepN (q : Program) : ∀ (k m : Nat) (c : Config),
    run q (k + m) c =
      ⟨(stepN q k c).2 ++ (run q m (stepN q k c).1).events, (run q m (stepN q k c).1).outcome⟩
  | 0, m, c => by simp [stepN_zero]
  | k + 1, m, .halted o => by
    simp only [stepN, run, runWith_halted, List.append_nil]
  | k + 1, m, .running s => by
    rw [show k + 1 + m = (k + m) + 1 by omega, stepN_succ_running]
    simp only [run, runWith]
    have ih := run_stepN q k m (step .walk q s).1
    simp only [run] at ih
    rw [ih]
    simp

/-! ## Stuttering forward simulation gives behavioural equivalence -/

theorem run_eq_of_sim (p q : Program) (R : Config → Config → Prop)
    (hhalt : ∀ o c', R (.halted o) c' → c' = .halted o)
    (hrun : ∀ s c', R (.running s) c' → ∃ s', c' = .running s')
    (hstep : ∀ s s', R (.running s) (.running s') → ∃ k, 0 < k ∧
      R (step .walk p s).1 (stepN q k (.running s')).1 ∧
      (stepN q k (.running s')).2 = (step .walk p s).2) :
    ∀ (n : Nat) (c c' : Config), R c c' → ∃ m, n ≤ m ∧ run p n c = run q m c' := by
  intro n
  induction n with
  | zero =>
    intro c c' h
    cases c with
    | halted o => rw [hhalt o c' h]; exact ⟨0, Nat.le_refl _, by simp [run, runWith_halted]⟩
    | running s =>
      obtain ⟨s', rfl⟩ := hrun s c' h
      exact ⟨0, Nat.le_refl _, rfl⟩
  | succ n ih =>
    intro c c' h
    cases c with
    | halted o => rw [hhalt o c' h]; exact ⟨n + 1, Nat.le_refl _, by simp [run, runWith_halted]⟩
    | running s =>
      obtain ⟨s', rfl⟩ := hrun s c' h
      obtain ⟨k, hk, hR, hev⟩ := hstep s s' h
      obtain ⟨m, hm, heq⟩ := ih _ _ hR
      refine ⟨k + m, by omega, ?_⟩
      rw [run_stepN q k m (.running s'), hev, ← heq]
      rfl

theorem behEquivAt_of_sim (p q : Program) (R : Config → Config → Prop)
    (hhalt : ∀ o c', R (.halted o) c' → c' = .halted o)
    (hrun : ∀ s c', R (.running s) c' → ∃ s', c' = .running s')
    (hstep : ∀ s s', R (.running s) (.running s') → ∃ k, 0 < k ∧
      R (step .walk p s).1 (stepN q k (.running s')).1 ∧
      (stepN q k (.running s')).2 = (step .walk p s).2)
    (e : Entry) (hinit : R (init p e) (init q e)) : BehEquivAt p q e := by
  have key := run_eq_of_sim p q R hhalt hrun hstep
  refine ⟨fun n => ?_, fun m => ?_⟩
  · obtain ⟨m, -, heq⟩ := key n _ _ hinit
    refine ⟨m, ?_⟩
    have heq' : runWith .walk p n (init p e) = runWith .walk q m (init q e) := heq
    rw [heq']
    exact Obs.Prefix.refl _
  · obtain ⟨m', hm', heq⟩ := key m _ _ hinit
    refine ⟨m, ?_⟩
    have heq' : runWith .walk p m (init p e) = runWith .walk q m' (init q e) := heq
    rw [heq']
    exact runWith_mono .walk q m m' _ hm'

/-! ## One-step equations for `step` -/

section StepEqs

variable {P : Program} {fr : Frame} {rest : List Frame} {Fn0 : Fn} {Bk : Block}

theorem step_noFn (hF : nth? P.fns fr.fn = none) : step .walk P (fr :: rest) = (.halted .ub, []) := by
  simp [step, hF]

theorem step_noBlk (hF : nth? P.fns fr.fn = some Fn0) (hB : nth? Fn0.blocks fr.block = none) :
    step .walk P (fr :: rest) = (.halted .ub, []) := by
  simp [step, hF, hB]

theorem step_assign (hF : nth? P.fns fr.fn = some Fn0) (hB : nth? Fn0.blocks fr.block = some Bk)
    {x : Local} {rv : Rvalue} (hs : nth? Bk.stmts fr.pc = some (.assign x rv)) :
    step .walk P (fr :: rest) =
      (.running ({ fr with pc := fr.pc + 1, store := upd fr.store x (evalRv fr.store rv) } :: rest), []) := by
  simp [step, hF, hB, hs]

theorem step_emit (hF : nth? P.fns fr.fn = some Fn0) (hB : nth? Fn0.blocks fr.block = some Bk)
    {o : Operand} (hs : nth? Bk.stmts fr.pc = some (.emit o)) :
    step .walk P (fr :: rest) = (.running ({ fr with pc := fr.pc + 1 } :: rest), [.out (evalOp fr.store o)]) := by
  simp [step, hF, hB, hs]

theorem step_needCap (hF : nth? P.fns fr.fn = some Fn0) (hB : nth? Fn0.blocks fr.block = some Bk)
    {c : Cap} (hs : nth? Bk.stmts fr.pc = some (.needCap c)) :
    step .walk P (fr :: rest) =
      if Fn0.caps.contains c then (.running ({ fr with pc := fr.pc + 1 } :: rest), [])
      else (.halted .capFault, []) := by
  simp [step, hF, hB, hs]

theorem step_loc (hF : nth? P.fns fr.fn = some Fn0) (hB : nth? Fn0.blocks fr.block = some Bk)
    {sp : Span} {sc : ScopeId} (hs : nth? Bk.stmts fr.pc = some (.loc sp sc)) :
    step .walk P (fr :: rest) =
      (.running ({ fr with pc := fr.pc + 1 } :: rest), [.loc (locValue P.tracked Fn0.scopes sc sp fr.il)]) := by
  simp [step, hF, hB, hs, locValueWith]

theorem step_term (hF : nth? P.fns fr.fn = some Fn0) (hB : nth? Fn0.blocks fr.block = some Bk)
    (hs : nth? Bk.stmts fr.pc = none) :
    step .walk P (fr :: rest) =
      match Bk.term with
      | .goto b => (.running ({ fr with block := b, pc := 0 } :: rest), [])
      | .branch o z nz =>
        (.running ({ fr with block := if evalOp fr.store o = 0 then z else nz, pc := 0 } :: rest), [])
      | .call ci =>
        match nth? P.fns ci.callee with
        | none => (.halted .ub, [])
        | some G =>
          (.running ({
              fn := ci.callee, block := 0, pc := 0,
              store := bindArgs (if ci.abiSensitive && (P.abi Fn0.caps != P.abi G.caps)
                then (ci.args.map (evalOp fr.store)).map (· + 1) else ci.args.map (evalOp fr.store)),
              il := if G.trackCaller
                then some (locValue P.tracked Fn0.scopes ci.scope ci.span fr.il) else none }
            :: { fr with pc := Bk.stmts.length } :: rest), [])
      | .ret => (returnInto P (fr.store 0) rest, [])
      | .resume => (unwindInto P rest, [])
      | .panic u => (startUnwind P fr rest u, [])
      | .unreachable => (.halted .ub, [])
      | .abort => (.halted .aborted, []) := by
  simp only [step, hF, hB, hs, locValueWith]
  rfl

end StepEqs

/-! ## Hypotheses and the simulation relation -/

namespace Site

variable (S : Site)

/-- The facts about one inlining step that the simulation uses. The four whole-program theorems
establish them from their own hypotheses. -/
structure Hyps : Prop where
  hF : nth? S.p.fns S.f = some S.F
  hB : nth? S.F.blocks S.b = some S.B
  hBt : S.B.term = .call S.ci
  hG : nth? S.p.fns S.ci.callee = some S.G
  locF : LocalsBounded S.F
  locG : LocalsBounded S.G
  blkF : BlocksBounded S.F
  scF : ScopesWF S.F
  scG : ScopesWF S.G
  inj : ∀ i, i < S.G.nlocals → ∀ j, j < S.G.nlocals → S.ρ i = S.ρ j → i = j
  fresh : ∀ i, i < S.G.nlocals → S.F.nlocals ≤ S.ρ i ∨ S.loose = some (S.ρ i)
  slotGe : ∀ i, 1 ≤ i → i < S.G.nlocals → S.F.nlocals ≤ S.ρ i
  looseCl : ∀ d, S.loose = some d → CleanupClosed S.F ∧ DestNotReadInCleanup S.F d
  mode : (∃ t, S.cfg.ret = .temp t ∧ S.loose = none) ∨ (S.cfg.ret = .dest ∧ S.loose = some S.ci.dest)
  cont : S.cfg.redirectContinue = true
  res : S.cfg.resumeMap = .unwind
  link : S.cfg.link = .rustc
  caps : ∀ BG ∈ S.G.blocks, ∀ c, Stmt.needCap c ∈ BG.stmts → S.F.caps.contains c = S.G.caps.contains c
  abiCall : (S.ci.abiSensitive && (S.p.abi S.F.caps != S.p.abi S.G.caps)) = false
  abiG : ∀ BG ∈ S.G.blocks, ∀ ci2, BG.term = .call ci2 → ci2.abiSensitive = true →
    S.p.abi S.F.caps = S.p.abi S.G.caps

/-- Host stores agree on the declared host locals, except that the `loose` local may differ while
control is in a cleanup block. -/
def StoreRelF (blk : BlockId) (C M : Local → Nat) : Prop :=
  ∀ x, x < S.F.nlocals → M x = C x ∨ (S.loose = some x ∧ cleanupAt S.F blk = true)

/-- Store relation of a plain frame of function `g` at block `blk`. -/
def PStore (g blk : Nat) (C M : Local → Nat) : Prop :=
  (g ≠ S.f → M = C) ∧ (g = S.f → S.StoreRelF blk C M)

/-- A frame of the original program paired with the same frame of the inlined program. -/
structure PlainRel (fp fq : Frame) : Prop where
  fn : fq.fn = fp.fn
  block : fq.block = fp.block
  pc : fq.pc = fp.pc
  il : fq.il = fp.il
  blk : fp.fn = S.f → fp.block < S.nb
  pcb : fp.fn = S.f → fp.block = S.b → fp.pc ≤ S.B.stmts.length
  st : S.PStore fp.fn fp.block fp.store fq.store

/-- The frame is not suspended at the inlined call. -/
def NotCallSite (fp : Frame) : Prop := ¬ (fp.fn = S.f ∧ fp.block = S.b ∧ fp.pc = S.B.stmts.length)

/-- A callee frame `gp` of the inlined call and the suspended caller frame `cp` below it, paired
with the merged frame `mq` of the inlined program. -/
structure MergedRel (gp cp mq : Frame) : Prop where
  gfn : gp.fn = S.ci.callee
  cfn : cp.fn = S.f
  cblk : cp.block = S.b
  cpc : cp.pc = S.B.stmts.length
  mfn : mq.fn = S.f
  mblk : mq.block = gp.block + S.base
  mpc : mq.pc = gp.pc
  mil : mq.il = cp.il
  gil : gp.il = if S.G.trackCaller
    then some (locValue S.p.tracked S.F.scopes S.ci.scope S.ci.span cp.il) else none
  host : ∀ x, x < S.F.nlocals → mq.store x = cp.store x ∨ S.loose = some x
  slots : ∀ i, i < S.G.nlocals → mq.store (S.ρ i) = gp.store i

end Site

/-- Relation between the suspended parts of the two stacks. -/
inductive RestRel (S : Site) : List Frame → List Frame → Prop
  | nil : RestRel S [] []
  | plain {fp fq sp sq} : S.PlainRel fp fq → S.NotCallSite fp → RestRel S sp sq →
      RestRel S (fp :: sp) (fq :: sq)
  | merged {gp cp mq sp sq} : S.MergedRel gp cp mq → RestRel S sp sq →
      RestRel S (gp :: cp :: sp) (mq :: sq)

/-- Relation between two stacks. -/
inductive StackRel (S : Site) : List Frame → List Frame → Prop
  | plain {fp fq sp sq} : S.PlainRel fp fq → RestRel S sp sq → StackRel S (fp :: sp) (fq :: sq)
  | merged {gp cp mq sp sq} : S.MergedRel gp cp mq → RestRel S sp sq →
      StackRel S (gp :: cp :: sp) (mq :: sq)

/-- Relation between two configurations. -/
inductive ConfigRel (S : Site) : Config → Config → Prop
  | halted (o : Outcome) : ConfigRel S (.halted o) (.halted o)
  | running {s s' : List Frame} : StackRel S s s' → ConfigRel S (.running s) (.running s')

/-! ## Basic consequences of the hypotheses -/

theorem Stmt.reads_sub (s : Stmt) : ∀ y ∈ s.reads, y ∈ s.locals := by
  intro y hy
  cases s <;> simp_all [Stmt.reads, Stmt.locals]

theorem Term.reads_sub (t : Term) : ∀ y ∈ t.reads, y ∈ t.locals := by
  intro y hy
  cases t <;> simp_all [Term.reads, Term.locals]

theorem Block.reads_sub (B : Block) : ∀ y ∈ B.reads, y ∈ B.locals := by
  intro y hy
  simp only [Block.reads, Block.locals, List.mem_append, List.mem_flatMap] at hy ⊢
  rcases hy with ⟨s, hs, hy⟩ | hy
  · exact Or.inl ⟨s, hs, Stmt.reads_sub s y hy⟩
  · exact Or.inr (Term.reads_sub _ y hy)

theorem stmt_reads_sub_block {B : Block} {s : Stmt} (hs : s ∈ B.stmts) : ∀ y ∈ s.reads, y ∈ B.reads := by
  intro y hy
  simp only [Block.reads, List.mem_append, List.mem_flatMap]
  exact Or.inl ⟨s, hs, hy⟩

theorem term_reads_sub_block (B : Block) : ∀ y ∈ B.term.reads, y ∈ B.reads := by
  intro y hy
  simp only [Block.reads, List.mem_append]
  exact Or.inr hy

theorem stmt_locals_sub_block {B : Block} {s : Stmt} (hs : s ∈ B.stmts) : ∀ y ∈ s.locals, y ∈ B.locals := by
  intro y hy
  simp only [Block.locals, List.mem_append, List.mem_flatMap]
  exact Or.inl ⟨s, hs, hy⟩

theorem term_locals_sub_block (B : Block) : ∀ y ∈ B.term.locals, y ∈ B.locals := by
  intro y hy
  simp only [Block.locals, List.mem_append]
  exact Or.inr hy

theorem stmt_scopes_sub_block {B : Block} {s : Stmt} (hs : s ∈ B.stmts) :
    ∀ y ∈ s.scopes, y ∈ B.scopeRefs := by
  intro y hy
  simp only [Block.scopeRefs, List.mem_append, List.mem_flatMap]
  exact Or.inl ⟨s, hs, hy⟩

theorem term_scopes_sub_block (B : Block) : ∀ y ∈ B.term.scopes, y ∈ B.scopeRefs := by
  intro y hy
  simp only [Block.scopeRefs, List.mem_append]
  exact Or.inr hy

theorem unwindTargets_sub_succs (t : Term) : ∀ c ∈ t.unwindTargets, c ∈ t.succs := by
  intro c hc
  cases t <;> simp_all [Term.unwindTargets, Term.succs]

namespace Site

variable {S : Site}

theorem Hyps.hf (H : S.Hyps) : S.f < S.p.fns.length := nth?_lt_length _ _ _ H.hF

theorem Hyps.hBmem (H : S.Hyps) : S.B ∈ S.F.blocks := nth?_mem _ _ _ H.hB

theorem Hyps.hb (H : S.Hyps) : S.b < S.nb := S.b_lt_nb H.hB

theorem Hyps.q_f (H : S.Hyps) : nth? S.q.fns S.f = some S.F' := by
  rw [S.nth?_q_fns H.hf]; simp

theorem Hyps.q_ne (H : S.Hyps) {g : Nat} (hg : g ≠ S.f) : nth? S.q.fns g = nth? S.p.fns g := by
  rw [S.nth?_q_fns H.hf]; simp [hg]

theorem Hyps.q_callee (H : S.Hyps) (h : Nat) :
    (nth? S.q.fns h).map (fun Fh => (Fh.caps, Fh.trackCaller)) =
      (nth? S.p.fns h).map (fun Fh => (Fh.caps, Fh.trackCaller)) := by
  by_cases hh : h = S.f
  · subst hh; rw [H.q_f, H.hF]; rfl
  · rw [H.q_ne hh]

theorem Hyps.q_callee_none (H : S.Hyps) (h : Nat) :
    nth? S.q.fns h = none ↔ nth? S.p.fns h = none := by
  by_cases hh : h = S.f
  · subst hh; rw [H.q_f, H.hF]; simp
  · rw [H.q_ne hh]

theorem Hyps.tracked_callee (H : S.Hyps) : S.p.tracked S.ci.callee = S.G.trackCaller := by
  simp [Program.tracked, H.hG]

theorem Hyps.succ_lt (H : S.Hyps) {Bk : Block} (hBk : Bk ∈ S.F.blocks) {t : BlockId}
    (ht : t ∈ Bk.term.succs) : t < S.nb := H.blkF Bk hBk t ht

theorem Hyps.target_lt (H : S.Hyps) {t : BlockId} (ht : S.ci.target = some t) : t < S.nb :=
  H.succ_lt H.hBmem (by rw [H.hBt]; simp [Term.succs, ht])

theorem Hyps.unwind_lt (H : S.Hyps) {c : BlockId} (hc : S.ci.unwind = .cleanup c) : c < S.nb :=
  H.succ_lt H.hBmem (by rw [H.hBt]; simp [Term.succs, hc, Unwind.blocks])

theorem Hyps.unwind_cleanup (H : S.Hyps) {c : BlockId} (hc : S.ci.unwind = .cleanup c) {d : Local}
    (hd : S.loose = some d) : cleanupAt S.F c = true :=
  ((H.looseCl d hd).1 S.B H.hBmem).1 c (by rw [H.hBt]; simp [Term.unwindTargets, hc, Unwind.blocks])

theorem Hyps.args_lt (H : S.Hyps) : ∀ a ∈ S.ci.args, ∀ y ∈ a.locals, y < S.F.nlocals := by
  intro a ha y hy
  apply H.locF S.B H.hBmem y
  apply term_locals_sub_block
  rw [H.hBt]
  simp only [Term.locals, List.mem_cons, List.mem_flatMap]
  exact Or.inr ⟨a, ha, hy⟩

theorem Hyps.dest_lt (H : S.Hyps) : S.ci.dest < S.F.nlocals := by
  apply H.locF S.B H.hBmem
  apply term_locals_sub_block
  rw [H.hBt]
  simp [Term.locals]

/-! ### Store relations -/

theorem storeRelF_reads (H : S.Hyps) {blk : BlockId} {Bk : Block} (hBk : nth? S.F.blocks blk = some Bk)
    {C M : Local → Nat} (hst : S.StoreRelF blk C M) : ∀ y ∈ Bk.reads, M y = C y := by
  intro y hy
  have hmem : Bk ∈ S.F.blocks := nth?_mem _ _ _ hBk
  have hlt : y < S.F.nlocals := H.locF Bk hmem y (Block.reads_sub Bk y hy)
  rcases hst y hlt with h | ⟨hl, hc⟩
  · exact h
  · exfalso
    have hcl : Bk.isCleanup = true := by
      simpa [cleanupAt, hBk] using hc
    exact (H.looseCl y hl).2 Bk hmem hcl hy

theorem storeRelF_upd {blk : BlockId} {C M : Local → Nat} (hst : S.StoreRelF blk C M) (x : Local) (v : Nat) :
    S.StoreRelF blk (upd C x v) (upd M x v) := by
  intro y hy
  by_cases hyx : y = x
  · left; simp [upd, hyx]
  · rcases hst y hy with h | h
    · left; simp [upd, hyx, h]
    · right; exact h

theorem storeRelF_succ (H : S.Hyps) {blk : BlockId} {Bk : Block} (hBk : nth? S.F.blocks blk = some Bk)
    {C M : Local → Nat} (hst : S.StoreRelF blk C M) {t : BlockId} (ht : t ∈ Bk.term.succs) :
    S.StoreRelF t C M := by
  intro y hy
  rcases hst y hy with h | ⟨hl, hc⟩
  · exact Or.inl h
  · right
    refine ⟨hl, ?_⟩
    have hmem : Bk ∈ S.F.blocks := nth?_mem _ _ _ hBk
    have hcl : Bk.isCleanup = true := by
      simpa [cleanupAt, hBk] using hc
    exact ((H.looseCl y hl).1 Bk hmem).2 hcl t ht

theorem pstore_reads (H : S.Hyps) {g blk : Nat} {Fp : Fn} {Bk : Block} (hFp : nth? S.p.fns g = some Fp)
    (hBk : nth? Fp.blocks blk = some Bk) {C M : Local → Nat} (hst : S.PStore g blk C M) :
    ∀ y ∈ Bk.reads, M y = C y := by
  by_cases hg : g = S.f
  · subst hg
    rw [H.hF] at hFp
    cases hFp
    exact storeRelF_reads H hBk (hst.2 rfl)
  · intro y _; rw [hst.1 hg]

theorem pstore_upd {g blk : Nat} {C M : Local → Nat} (hst : S.PStore g blk C M) (x : Local) (v : Nat) :
    S.PStore g blk (upd C x v) (upd M x v) :=
  ⟨fun hg => by rw [hst.1 hg], fun hg => storeRelF_upd (hst.2 hg) x v⟩

theorem pstore_succ (H : S.Hyps) {g blk : Nat} {Fp : Fn} {Bk : Block} (hFp : nth? S.p.fns g = some Fp)
    (hBk : nth? Fp.blocks blk = some Bk) {C M : Local → Nat} (hst : S.PStore g blk C M)
    {t : BlockId} (ht : t ∈ Bk.term.succs) : S.PStore g t C M := by
  refine ⟨hst.1, fun hg => ?_⟩
  subst hg
  rw [H.hF] at hFp
  cases hFp
  exact storeRelF_succ H hBk (hst.2 rfl) ht

theorem plainRel_succ (H : S.Hyps) {g blk : Nat} {Fp : Fn} {Bk : Block} (hFp : nth? S.p.fns g = some Fp)
    (hBk : nth? Fp.blocks blk = some Bk) {C M : Local → Nat} (hst : S.PStore g blk C M)
    {t : BlockId} (ht : t ∈ Bk.term.succs) (il : Option Span) :
    S.PlainRel ⟨g, t, 0, C, il⟩ ⟨g, t, 0, M, il⟩ where
  fn := rfl
  block := rfl
  pc := rfl
  il := rfl
  blk := by
    intro hg
    subst hg
    rw [H.hF] at hFp
    cases hFp
    exact H.succ_lt (nth?_mem _ _ _ hBk) ht
  pcb := fun _ _ => Nat.zero_le _
  st := pstore_succ H hFp hBk hst ht

end Site

/-! ### Generic facts about `curTerm`, `unwindInto`, `returnInto` -/

theorem curTerm_some {P : Program} {fr : Frame} {T : Term} (h : curTerm P fr = some T) :
    ∃ Fn0 Bk, nth? P.fns fr.fn = some Fn0 ∧ nth? Fn0.blocks fr.block = some Bk ∧ Bk.term = T ∧
      fr.pc = Bk.stmts.length := by
  unfold curTerm at h
  cases hF : nth? P.fns fr.fn with
  | none => rw [hF] at h; cases h
  | some Fn0 =>
    rw [hF] at h
    cases hB : nth? Fn0.blocks fr.block with
    | none => simp only [hB] at h; cases h
    | some Bk =>
      simp only [hB] at h
      by_cases hpc : fr.pc = Bk.stmts.length
      · simp only [hpc, ↓reduceIte, Option.some.injEq] at h
        exact ⟨Fn0, Bk, rfl, hB, h, hpc⟩
      · simp [hpc] at h

theorem unwindInto_cons_call {P : Program} {c : Frame} {rest : List Frame} {ci : CallInfo}
    (h : curTerm P c = some (.call ci)) :
    unwindInto P (c :: rest) =
      match ci.unwind with
      | .cleanup b => .running ({ c with block := b, pc := 0 } :: rest)
      | .continue => unwindInto P rest
      | .terminate => .halted .aborted := by
  simp only [unwindInto, h]
  cases ci.unwind <;> rfl

theorem unwindInto_cons_ub {P : Program} {c : Frame} {rest : List Frame}
    (h : ∀ ci, curTerm P c ≠ some (.call ci)) : unwindInto P (c :: rest) = .halted .ub := by
  unfold unwindInto
  split
  · rename_i ci hc; exact absurd hc (h ci)
  all_goals rfl

theorem returnInto_cons_call {P : Program} {c : Frame} {rest : List Frame} {ci : CallInfo} {v : Nat}
    (h : curTerm P c = some (.call ci)) :
    returnInto P v (c :: rest) =
      match ci.target with
      | some t => .running ({ c with block := t, pc := 0, store := upd c.store ci.dest v } :: rest)
      | none => .halted .ub := by
  simp only [returnInto, h]
  cases ci.target <;> rfl

theorem returnInto_cons_ub {P : Program} {c : Frame} {rest : List Frame} {v : Nat}
    (h : ∀ ci, curTerm P c ≠ some (.call ci)) : returnInto P v (c :: rest) = .halted .ub := by
  simp only [returnInto]
  all_goals (split <;> first | rfl | (rename_i ci hc; exact absurd hc (h ci)))

theorem spliceTerm_call {c : SpliceCtx} {T : Term} {ci' : CallInfo} (h : c.term T = .call ci') :
    ∃ ci2, T = .call ci2 := by
  cases T with
  | call ci2 => exact ⟨ci2, rfl⟩
  | ret =>
    simp only [SpliceCtx.term] at h
    split at h <;> cases h
  | resume =>
    simp only [SpliceCtx.term] at h
    split at h
    · split at h <;> cases h
    · split at h <;> cases h
  | goto _ => cases h
  | branch _ _ _ => cases h
  | panic _ => cases h
  | unreachable => cases h
  | abort => cases h

namespace Site

variable {S : Site}

/-! ### The suspended frames -/

theorem curTerm_plain (H : S.Hyps) {fp fq : Frame} (hP : S.PlainRel fp fq) (hn : S.NotCallSite fp) :
    curTerm S.q fq = curTerm S.p fp := by
  obtain ⟨g, blk, pc, C, il⟩ := fp
  obtain ⟨g', blk', pc', M, il'⟩ := fq
  obtain ⟨hfn, hblk, hpc, hil, hb, hpcb, -⟩ := hP
  simp only at hfn hblk hpc hil hb hpcb
  subst g' blk' pc' il'
  unfold curTerm
  simp only
  by_cases hg : g = S.f
  · subst hg
    rw [H.q_f, H.hF]
    simp only
    by_cases hbb : blk = S.b
    · subst hbb
      rw [S.nth?_F'_b H.hb, H.hB]
      have hpc' : pc < S.B.stmts.length := by
        have := hpcb rfl rfl
        have hne : pc ≠ S.B.stmts.length := fun h => hn ⟨rfl, rfl, h⟩
        omega
      simp only [callBlk, List.length_append]
      have h1 : pc ≠ S.B.stmts.length + S.prol.length := by omega
      have h2 : pc ≠ S.B.stmts.length := by omega
      simp [h1, h2]
    · rw [S.nth?_F'_lt blk (hb rfl) hbb]
  · rw [H.q_ne hg]

theorem curTerm_merged (H : S.Hyps) {gp cp mq : Frame} (hM : S.MergedRel gp cp mq) :
    curTerm S.q mq = (curTerm S.p gp).map S.ctx.term := by
  unfold curTerm
  rw [hM.mfn, H.q_f, hM.gfn, H.hG]
  simp only
  rw [hM.mblk, S.nth?_F'_base, hM.mpc]
  cases nth? S.G.blocks gp.block with
  | none => rfl
  | some BG =>
    simp only [Option.map_some, SpliceCtx.block, List.length_map]
    by_cases h : gp.pc = BG.stmts.length <;> simp [h]

theorem curTerm_cp (H : S.Hyps) {gp cp mq : Frame} (hM : S.MergedRel gp cp mq) :
    curTerm S.p cp = some (.call S.ci) := by
  unfold curTerm
  rw [hM.cfn, H.hF]
  simp only
  rw [hM.cblk, H.hB]
  simp [hM.cpc, H.hBt]

theorem merged_store_upd (H : S.Hyps) {Gs M C : Local → Nat}
    (hhost : ∀ x, x < S.F.nlocals → M x = C x ∨ S.loose = some x)
    (hslots : ∀ i, i < S.G.nlocals → M (S.ρ i) = Gs i) {x : Local} (hx : x < S.G.nlocals) (v : Nat) :
    (∀ y, y < S.F.nlocals → upd M (S.ρ x) v y = C y ∨ S.loose = some y) ∧
      (∀ i, i < S.G.nlocals → upd M (S.ρ x) v (S.ρ i) = upd Gs x v i) := by
  constructor
  · intro y hy
    by_cases hyx : y = S.ρ x
    · right
      rcases H.fresh x hx with h | h
      · omega
      · rw [hyx]; exact h
    · simp only [upd, hyx, ↓reduceIte]; exact hhost y hy
  · intro i hi
    by_cases hix : i = x
    · subst hix; simp [upd]
    · have hne : S.ρ i ≠ S.ρ x := fun h => hix (H.inj i hi x hx h)
      simp only [upd, hne, hix, ↓reduceIte]
      exact hslots i hi

/-- Unwinding out of a merged segment into the caller's unwind action. -/
theorem unwind_from_cp (H : S.Hyps) {gp cp mq : Frame} {sp sq : List Frame} (hM : S.MergedRel gp cp mq)
    (hR : RestRel S sp sq) (hU : ConfigRel S (unwindInto S.p sp) (unwindInto S.q sq)) :
    ConfigRel S (unwindInto S.p (cp :: sp)) (startUnwind S.q mq sq S.ci.unwind) := by
  rw [unwindInto_cons_call (curTerm_cp H hM)]
  cases hu : S.ci.unwind with
  | cleanup c =>
    simp only [startUnwind]
    refine ConfigRel.running (StackRel.plain ⟨?_, rfl, rfl, ?_, ?_, ?_, ?_⟩ hR)
    · simp [hM.mfn, hM.cfn]
    · simp [hM.mil]
    · intro _; exact H.unwind_lt hu
    · intro _ _; exact Nat.zero_le _
    · refine ⟨fun h => absurd hM.cfn h, fun _ => ?_⟩
      intro x hx
      rcases hM.host x hx with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, H.unwind_cleanup hu h⟩
  | «continue» => exact hU
  | terminate => exact ConfigRel.halted _

theorem startUnwind_mapUnwind_continue (H : S.Hyps) :
    S.ctx.mapUnwind .continue = S.ci.unwind := by
  simp [SpliceCtx.mapUnwind, ctx, H.cont]

theorem unwindInto_rel (H : S.Hyps) {sp sq : List Frame} (hR : RestRel S sp sq) :
    ConfigRel S (unwindInto S.p sp) (unwindInto S.q sq) := by
  induction hR with
  | nil => exact ConfigRel.halted _
  | @plain fp fq sp sq hP hn hR ih =>
    have hct := curTerm_plain H hP hn
    cases hc : curTerm S.p fp with
    | none =>
      rw [unwindInto_cons_ub (by intro ci h; rw [hc] at h; cases h),
        unwindInto_cons_ub (by intro ci h; rw [hct, hc] at h; cases h)]
      exact ConfigRel.halted _
    | some T =>
      cases T with
      | call ci2 =>
        rw [unwindInto_cons_call hc, unwindInto_cons_call (hct.trans hc)]
        obtain ⟨Fp, Bk, hFp, hBk, hBt, -⟩ := curTerm_some hc
        obtain ⟨g, blk, pc, C, il⟩ := fp
        obtain ⟨g', blk', pc', M, il'⟩ := fq
        obtain ⟨hfn, hblk, hpc, hil, -, -, hst⟩ := hP
        simp only at hfn hblk hpc hil hst hFp hBk
        subst g' blk' pc' il'
        cases hu : ci2.unwind with
        | cleanup c =>
          refine ConfigRel.running (StackRel.plain ?_ hR)
          exact plainRel_succ H hFp hBk hst (by rw [hBt]; simp [Term.succs, hu, Unwind.blocks]) il
        | «continue» => exact ih
        | terminate => exact ConfigRel.halted _
      | ret | resume | goto _ | branch _ _ _ | panic _ | unreachable | abort =>
        rw [unwindInto_cons_ub (by intro ci h; rw [hc] at h; cases h),
          unwindInto_cons_ub (by intro ci h; rw [hct, hc] at h; cases h)]
        exact ConfigRel.halted _
  | @merged gp cp mq sp sq hM hR ih =>
    have hct := curTerm_merged H hM
    cases hc : curTerm S.p gp with
    | none =>
      rw [unwindInto_cons_ub (by intro ci h; rw [hc] at h; cases h),
        unwindInto_cons_ub (by intro ci h; rw [hct, hc] at h; cases h)]
      exact ConfigRel.halted _
    | some T =>
      rw [hc] at hct
      cases T with
      | call ci2 =>
        rw [unwindInto_cons_call hc, unwindInto_cons_call hct]
        cases hu : ci2.unwind with
        | cleanup c =>
          simp only [SpliceCtx.mapUnwind]
          refine ConfigRel.running (StackRel.merged ⟨hM.gfn, hM.cfn, hM.cblk, hM.cpc, hM.mfn,
            ?_, rfl, hM.mil, hM.gil, hM.host, hM.slots⟩ hR)
          simp [ctx]
        | «continue» =>
          rw [startUnwind_mapUnwind_continue H]
          have := unwind_from_cp H hM hR ih
          cases hu' : S.ci.unwind <;> rw [hu'] at this <;> simpa [startUnwind] using this
        | terminate => exact ConfigRel.halted _
      | ret | resume | goto _ | branch _ _ _ | panic _ | unreachable | abort =>
        rw [unwindInto_cons_ub (by intro ci h; rw [hc] at h; cases h),
          unwindInto_cons_ub (by
            intro ci h; rw [hct] at h
            obtain ⟨ci3, h3⟩ := spliceTerm_call (Option.some.inj h)
            cases h3)]
        exact ConfigRel.halted _

theorem returnInto_rel (H : S.Hyps) {sp sq : List Frame} (hR : RestRel S sp sq) (v : Nat) :
    ConfigRel S (returnInto S.p v sp) (returnInto S.q v sq) := by
  cases hR with
  | nil => exact ConfigRel.halted _
  | @plain fp fq sp sq hP hn hR =>
    have hct := curTerm_plain H hP hn
    cases hc : curTerm S.p fp with
    | none =>
      rw [returnInto_cons_ub (by intro ci h; rw [hc] at h; cases h),
        returnInto_cons_ub (by intro ci h; rw [hct, hc] at h; cases h)]
      exact ConfigRel.halted _
    | some T =>
      cases T with
      | call ci2 =>
        rw [returnInto_cons_call hc, returnInto_cons_call (hct.trans hc)]
        obtain ⟨Fp, Bk, hFp, hBk, hBt, -⟩ := curTerm_some hc
        obtain ⟨g, blk, pc, C, il⟩ := fp
        obtain ⟨g', blk', pc', M, il'⟩ := fq
        obtain ⟨hfn, hblk, hpc, hil, -, -, hst⟩ := hP
        simp only at hfn hblk hpc hil hst hFp hBk
        subst g' blk' pc' il'
        cases ht : ci2.target with
        | none => exact ConfigRel.halted _
        | some t =>
          refine ConfigRel.running (StackRel.plain ?_ hR)
          exact plainRel_succ H hFp hBk (pstore_upd hst ci2.dest v)
            (by rw [hBt]; simp [Term.succs, ht]) il
      | ret | resume | goto _ | branch _ _ _ | panic _ | unreachable | abort =>
        rw [returnInto_cons_ub (by intro ci h; rw [hc] at h; cases h),
          returnInto_cons_ub (by intro ci h; rw [hct, hc] at h; cases h)]
        exact ConfigRel.halted _
  | @merged gp cp mq sp sq hM hR =>
    have hct := curTerm_merged H hM
    cases hc : curTerm S.p gp with
    | none =>
      rw [returnInto_cons_ub (by intro ci h; rw [hc] at h; cases h),
        returnInto_cons_ub (by intro ci h; rw [hct, hc] at h; cases h)]
      exact ConfigRel.halted _
    | some T =>
      rw [hc] at hct
      cases T with
      | call ci2 =>
        rw [returnInto_cons_call hc, returnInto_cons_call hct]
        obtain ⟨Gx, BG, hGx, hBG, hBGt, -⟩ := curTerm_some hc
        rw [hM.gfn, H.hG] at hGx
        cases hGx
        have hdest : ci2.dest < S.G.nlocals :=
          H.locG BG (nth?_mem _ _ _ hBG) _ (term_locals_sub_block BG _ (by rw [hBGt]; simp [Term.locals]))
        cases ht : ci2.target with
        | none => exact ConfigRel.halted _
        | some t =>
          obtain ⟨hh, hs⟩ := merged_store_upd H hM.host hM.slots hdest v
          refine ConfigRel.running (StackRel.merged ⟨hM.gfn, hM.cfn, hM.cblk, hM.cpc, hM.mfn,
            ?_, rfl, hM.mil, hM.gil, hh, hs⟩ hR)
          simp [ctx]
      | ret | resume | goto _ | branch _ _ _ | panic _ | unreachable | abort =>
        rw [returnInto_cons_ub (by intro ci h; rw [hc] at h; cases h),
          returnInto_cons_ub (by
            intro ci h; rw [hct] at h
            obtain ⟨ci3, h3⟩ := spliceTerm_call (Option.some.inj h)
            cases h3)]
        exact ConfigRel.halted _

end Site

/-! ## Straight-line runs of assignments -/

/-- The store after executing a list of statements with `stmtStore` (used for assignments). -/
def execStores (ss : List Stmt) (st : Local → Nat) : Local → Nat :=
  ss.foldl (fun st s => (stmtStore st s).1) st

theorem execStores_nil (st : Local → Nat) : execStores [] st = st := rfl

theorem execStores_cons (s : Stmt) (ss : List Stmt) (st : Local → Nat) :
    execStores (s :: ss) st = execStores ss (stmtStore st s).1 := rfl

theorem execStores_append (ss ts : List Stmt) (st : Local → Nat) :
    execStores (ss ++ ts) st = execStores ts (execStores ss st) := by
  simp [execStores, List.foldl_append]

/-- `k` steps through a straight-line run of assignments starting at statement `pre.length`. -/
theorem stepN_assigns {P : Program} {rest : List Frame} {Fn0 : Fn} {Bk : Block} :
    ∀ (ss pre post : List Stmt) (fr : Frame),
      nth? P.fns fr.fn = some Fn0 → nth? Fn0.blocks fr.block = some Bk →
      Bk.stmts = pre ++ ss ++ post → fr.pc = pre.length →
      (∀ s ∈ ss, ∃ x rv, s = .assign x rv) →
      stepN P ss.length (.running (fr :: rest)) =
        (.running ({ fr with pc := fr.pc + ss.length, store := execStores ss fr.store } :: rest), [])
  | [], _, _, fr, _, _, _, _, _ => by simp [stepN_zero, execStores_nil]
  | s :: ss, pre, post, fr, hF, hB, hstm, hpc, hall => by
    obtain ⟨x, rv, rfl⟩ := hall s (List.mem_cons_self ..)
    have hs : nth? Bk.stmts fr.pc = some (.assign x rv) := by
      rw [hstm, hpc, nth?_eq_getElem?, List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]
      simp
    rw [List.length_cons, stepN_succ_running, step_assign hF hB hs]
    have ih := stepN_assigns (rest := rest) ss (pre ++ [.assign x rv]) post
      { fr with pc := fr.pc + 1, store := upd fr.store x (evalRv fr.store rv) } hF hB
      (by rw [hstm]; simp) (by simp [hpc])
      (fun s hs => hall s (List.mem_cons_of_mem _ hs))
    rw [ih]
    simp only [List.nil_append, execStores_cons, stmtStore, Nat.add_assoc, Nat.add_comm 1 ss.length]

/-! ## The argument-binding prologue -/

theorem evalOp_congr {C D : Local → Nat} {o : Operand} (h : ∀ y ∈ o.locals, D y = C y) :
    evalOp D o = evalOp C o := by
  cases o with
  | const _ => rfl
  | var x => exact h x (by simp [Operand.locals])

theorem evalRv_congr {C D : Local → Nat} {rv : Rvalue} (h : ∀ y ∈ rv.locals, D y = C y) :
    evalRv D rv = evalRv C rv := by
  cases rv with
  | use o => exact evalOp_congr h
  | add a b =>
    simp only [evalRv]
    rw [evalOp_congr (fun y hy => h y (by simp [Rvalue.locals, hy])),
      evalOp_congr (fun y hy => h y (by simp [Rvalue.locals, hy]))]

theorem argOr_locals (args : List Operand) (i : Nat) :
    ∀ y ∈ (argOr args i).locals, ∃ a ∈ args, y ∈ a.locals := by
  intro y hy
  unfold argOr at hy
  cases h : nth? args (i - 1) with
  | none => rw [h] at hy; simp [Operand.locals] at hy
  | some a => rw [h] at hy; exact ⟨a, nth?_mem _ _ _ h, hy⟩

theorem evalOp_argOr (C : Local → Nat) (args : List Operand) (k : Nat) :
    evalOp C (argOr args (k + 1)) = bindArgs (args.map (evalOp C)) (k + 1) := by
  simp only [argOr, bindArgs, Nat.add_sub_cancel, nth?_map]
  cases nth? args k <;> rfl

theorem execStores_argAssigns (ρ : Nat → Local) (args : List Operand) :
    ∀ (L : List Nat) (C : Local → Nat), L.Pairwise (· ≠ ·) →
      (∀ i ∈ L, ∀ j ∈ L, ρ i = ρ j → i = j) →
      (∀ i ∈ L, ∀ a ∈ args, ∀ y ∈ a.locals, ρ i ≠ y) →
      (∀ x, (∀ i ∈ L, ρ i ≠ x) →
        execStores (L.map (fun i => Stmt.assign (ρ i) (.use (argOr args i)))) C x = C x) ∧
      (∀ i ∈ L, execStores (L.map (fun i => Stmt.assign (ρ i) (.use (argOr args i)))) C (ρ i) =
        evalOp C (argOr args i))
  | [], C, _, _, _ => ⟨fun _ _ => rfl, fun _ h => by cases h⟩
  | i :: L, C, hpw, hinj, havoid => by
    rw [List.pairwise_cons] at hpw
    simp only [List.map_cons, execStores_cons, stmtStore]
    have ih := execStores_argAssigns ρ args L (upd C (ρ i) (evalRv C (.use (argOr args i)))) hpw.2
      (fun a ha b hb => hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
      (fun a ha => havoid a (List.mem_cons_of_mem _ ha))
    have hagree : ∀ j, ∀ y ∈ (argOr args j).locals,
        upd C (ρ i) (evalRv C (.use (argOr args i))) y = C y := by
      intro j y hy
      obtain ⟨a, ha, hya⟩ := argOr_locals args j y hy
      have hne : y ≠ ρ i := fun h => havoid i (List.mem_cons_self ..) a ha y hya h.symm
      simp [upd, hne]
    refine ⟨fun x hx => ?_, fun j hj => ?_⟩
    · rw [ih.1 x (fun j hj => hx j (List.mem_cons_of_mem _ hj))]
      have hne : x ≠ ρ i := fun h => hx i (List.mem_cons_self ..) h.symm
      simp [upd, hne]
    · rcases List.mem_cons.mp hj with rfl | hj'
      · rw [ih.1 (ρ j) (fun k hk h => hpw.1 k hk (hinj j (List.mem_cons_self ..) k
          (List.mem_cons_of_mem _ hk) h.symm))]
        simp [upd, evalRv]
      · rw [ih.2 j hj', evalOp_congr (hagree j)]

theorem mem_range_tail {n i : Nat} : i ∈ (List.range n).tail ↔ 1 ≤ i ∧ i < n := by
  cases n with
  | zero => simp
  | succ m =>
    rw [List.range_succ_eq_map]
    simp only [List.tail_cons, List.mem_map, List.mem_range]
    constructor
    · intro h
      obtain ⟨k, hk, e⟩ := h
      subst e
      exact ⟨Nat.succ_le_succ (Nat.zero_le _), Nat.succ_lt_succ hk⟩
    · intro h
      obtain ⟨h1, h2⟩ := h
      refine ⟨i - 1, ?_, ?_⟩
      · omega
      · omega

theorem pairwise_lt_range : ∀ m, (List.range m).Pairwise (· < ·)
  | 0 => List.Pairwise.nil
  | m + 1 => by
    rw [List.range_succ, List.pairwise_append]
    refine ⟨pairwise_lt_range m, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb
    subst hb
    exact List.mem_range.mp ha

theorem pairwise_range_tail (n : Nat) : (List.range n).tail.Pairwise (· ≠ ·) := by
  cases n with
  | zero => exact List.Pairwise.nil
  | succ m =>
    rw [List.range_succ_eq_map, List.tail_cons, List.pairwise_map]
    exact (pairwise_lt_range m).imp (fun h1 h2 => Nat.ne_of_lt h1 (Nat.succ.inj h2))

theorem prologue_assigns (ρ : Nat → Local) (args : List Operand) (n : Nat) :
    ∀ s ∈ prologue ρ args n, ∃ x rv, s = .assign x rv := by
  intro s hs
  simp only [prologue, List.mem_append, List.mem_map] at hs
  rcases hs with ⟨i, _, rfl⟩ | hs
  · exact ⟨_, _, rfl⟩
  · split at hs
    · cases hs
    · simp only [List.mem_singleton] at hs; exact ⟨_, _, hs⟩

theorem prologue_spec (ρ : Nat → Local) (args : List Operand) (n : Nat) (C : Local → Nat)
    (hinj : ∀ i, i < n → ∀ j, j < n → ρ i = ρ j → i = j)
    (havoid : ∀ i, 1 ≤ i → i < n → ∀ a ∈ args, ∀ y ∈ a.locals, ρ i ≠ y) :
    (∀ x, (∀ i, i < n → ρ i ≠ x) → execStores (prologue ρ args n) C x = C x) ∧
      (∀ i, i < n → execStores (prologue ρ args n) C (ρ i) = bindArgs (args.map (evalOp C)) i) := by
  have hL := execStores_argAssigns ρ args (List.range n).tail C (pairwise_range_tail n)
    (fun i hi j hj h => hinj i (mem_range_tail.mp hi).2 j (mem_range_tail.mp hj).2 h)
    (fun i hi => havoid i (mem_range_tail.mp hi).1 (mem_range_tail.mp hi).2)
  unfold prologue
  rw [execStores_append]
  by_cases hn : n = 0
  · subst hn
    refine ⟨fun x _ => ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    simp [execStores]
  · simp only [hn, ↓reduceIte, execStores_cons, execStores_nil, stmtStore, evalRv, evalOp]
    refine ⟨fun x hx => ?_, fun i hi => ?_⟩
    · have hne : x ≠ ρ 0 := fun h => hx 0 (by omega) h.symm
      simp only [upd, hne, ↓reduceIte]
      exact hL.1 x (fun i hi => hx i (mem_range_tail.mp hi).2)
    · by_cases hi0 : i = 0
      · subst hi0; simp [upd, bindArgs]
      · have hne : ρ i ≠ ρ 0 := fun h => hi0 (hinj i hi 0 (by omega) h)
        simp only [upd, hne, ↓reduceIte]
        rw [hL.2 i (mem_range_tail.mpr ⟨by omega, hi⟩)]
        obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        exact evalOp_argOr C args k

/-! ## Caller locations in the merged scope table -/

theorem locValue_callee (tr : FnId → Bool) (F : Fn) (ci : CallInfo) (G : Fn) (s : ScopeId)
    (sp : Span) (il : Option Span)
    (hF : ScopeParentsBelow F.scopes) (hG : ScopeTreeWF G.scopes) (hs : s < G.scopes.length) :
    locValue tr (F.scopes ++ linkScopes .rustc F ci G) (F.scopes.length + s) sp il =
      locValue tr G.scopes s sp
        (if tr ci.callee then some (locValue tr F.scopes ci.scope ci.span il) else none) := by
  simp only [locValue]
  have hlen : (F.scopes ++ linkScopes .rustc F ci G).length = F.scopes.length + G.scopes.length := by
    simp [linkScopes, mapIdxFrom_length]
  rw [walk_callee_aux tr F ci G hF hG s sp _ _ hs (by rw [hlen]; dsimp [ScopeId] at *; omega) hs]
  cases walk tr G.scopes G.scopes.length s sp with
  | stop sp' => rfl
  | top sp' =>
    cases htr : tr ci.callee with
    | false => rfl
    | true => simp only [↓reduceIte, Option.getD_some]

theorem locValue_caller (tr : FnId → Bool) (link : LinkRule) (F : Fn) (ci : CallInfo) (G : Fn)
    (s : ScopeId) (sp : Span) (il : Option Span)
    (hF : ScopeParentsBelow F.scopes) (hs : s < F.scopes.length) :
    locValue tr (F.scopes ++ linkScopes link F ci G) s sp il = locValue tr F.scopes s sp il := by
  simp only [locValue]
  have h1 : s < (F.scopes ++ linkScopes link F ci G).length := by
    simp only [List.length_append]; exact Nat.lt_of_lt_of_le hs (Nat.le_add_right _ _)
  rw [walk_prefix_eq tr F.scopes (linkScopes link F ci G) hF s sp _ _ hs h1 hs]

namespace Site

variable {S : Site}

theorem Hyps.locHost (H : S.Hyps) {Bk : Block} (hBk : Bk ∈ S.F.blocks) :
    ∀ sc ∈ Bk.scopeRefs, ∀ sp il,
      locValue S.p.tracked S.F'.scopes sc sp il = locValue S.p.tracked S.F.scopes sc sp il := by
  intro sc hsc sp il
  rw [F'_scopes]
  exact locValue_caller _ _ _ _ _ _ _ _ H.scF.1.2 (H.scF.2 Bk hBk sc hsc)

theorem Hyps.locCallee (H : S.Hyps) {BG : Block} (hBG : BG ∈ S.G.blocks) (il : Option Span) :
    ∀ sc ∈ BG.scopeRefs, ∀ sp,
      locValue S.p.tracked S.F'.scopes (sc + S.F.scopes.length) sp il =
        locValue S.p.tracked S.G.scopes sc sp
          (if S.G.trackCaller then some (locValue S.p.tracked S.F.scopes S.ci.scope S.ci.span il)
           else none) := by
  intro sc hsc sp
  rw [F'_scopes, H.link, Nat.add_comm, ← H.tracked_callee]
  exact locValue_callee _ _ _ _ _ _ _ H.scF.1.2 H.scG.1 (H.scG.2 BG hBG sc hsc)

/-! ## Macro steps of the inlined program -/

theorem call_macro (H : S.Hyps) (M : Local → Nat) (il : Option Span) (sq : List Frame) :
    stepN S.q (S.prol.length + 1) (.running (⟨S.f, S.b, S.B.stmts.length, M, il⟩ :: sq)) =
      (.running (⟨S.f, S.base, 0, execStores S.prol M, il⟩ :: sq), []) := by
  rw [stepN_add, stepN_assigns S.prol S.B.stmts [] _ H.q_f (S.nth?_F'_b H.hb)
    (by simp [callBlk]) rfl (prologue_assigns _ _ _)]
  simp only [stepN_one, List.nil_append]
  rw [step_term (Fn0 := S.F') (Bk := S.callBlk) H.q_f (S.nth?_F'_b H.hb)
    (by simp [callBlk, nth?_eq_getElem?])]
  rfl

theorem retStmts_assigns (cfg : InlineCfg) (ci : CallInfo) :
    ∀ s ∈ retStmts cfg ci, ∃ x rv, s = .assign x rv := by
  intro s hs
  unfold retStmts at hs
  split at hs
  · simp only [List.mem_singleton] at hs; exact ⟨_, _, hs⟩
  · cases hs

theorem ret_macro (H : S.Hyps) {j pc : Nat} {M : Local → Nat} {il : Option Span} {sq : List Frame}
    {BG : Block} {t : BlockId} (hBG : nth? S.G.blocks j = some BG) (hs : nth? BG.stmts pc = none)
    (hT : BG.term = .ret) (ht : S.ci.target = some t) :
    stepN S.q (1 + (retStmts S.cfg S.ci).length + 1) (.running (⟨S.f, j + S.base, pc, M, il⟩ :: sq)) =
      (.running (⟨S.f, t, 0, execStores (retStmts S.cfg S.ci) M, il⟩ :: sq), []) := by
  have hBq : nth? S.F'.blocks (j + S.base) = some (S.ctx.block BG) := by
    rw [S.nth?_F'_base, hBG]; rfl
  have hsq : nth? (S.ctx.block BG).stmts pc = none := by
    simp [SpliceCtx.block, nth?_map, hs]
  rw [stepN_add, stepN_add, stepN_one]
  rw [step_term (Fn0 := S.F') (Bk := S.ctx.block BG) H.q_f hBq hsq]
  simp only [SpliceCtx.block, hT, SpliceCtx.term, ctx, ht, Option.map_some]
  rw [stepN_assigns (retStmts S.cfg S.ci) [] [] _ H.q_f (S.nth?_F'_nb t ht)
    (by simp [retBlock]) rfl (retStmts_assigns _ _)]
  simp only [stepN_one, List.nil_append]
  rw [step_term (Fn0 := S.F') (Bk := S.retBlock t) H.q_f (S.nth?_F'_nb t ht)
    (by simp [retBlock, nth?_eq_getElem?])]
  rfl

/-! ## The step simulation -/

/-- One step of the original program from `s` is matched by `k ≥ 1` steps of the inlined program
from `s'` with the same events, ending in related configurations. -/
def SimOK (S : Site) (s s' : List Frame) : Prop :=
  ∃ k, 0 < k ∧ ConfigRel S (step .walk S.p s).1 (stepN S.q k (.running s')).1 ∧
    (stepN S.q k (.running s')).2 = (step .walk S.p s).2

theorem SimOK.of_stepN {s s' : List Frame} {c c' : Config} {ev : List Event} {k : Nat} (hk : 0 < k)
    (hp : step .walk S.p s = (c, ev)) (hq : stepN S.q k (.running s') = (c', ev))
    (hc : ConfigRel S c c') : SimOK S s s' :=
  ⟨k, hk, by rw [hp, hq]; exact hc, by rw [hp, hq]⟩

theorem SimOK.of_eq {s s' : List Frame} {c c' : Config} {ev : List Event}
    (hp : step .walk S.p s = (c, ev)) (hq : step .walk S.q s' = (c', ev))
    (hc : ConfigRel S c c') : SimOK S s s' :=
  SimOK.of_stepN Nat.one_pos hp (by rw [stepN_one, hq]) hc

theorem plainRel_next {g blk pc : Nat} {il : Option Span} {C M C' M' : Local → Nat}
    (hP : S.PlainRel ⟨g, blk, pc, C, il⟩ ⟨g, blk, pc, M, il⟩)
    (hpcb : g = S.f → blk = S.b → pc + 1 ≤ S.B.stmts.length) (hst : S.PStore g blk C' M') :
    S.PlainRel ⟨g, blk, pc + 1, C', il⟩ ⟨g, blk, pc + 1, M', il⟩ :=
  ⟨rfl, rfl, rfl, rfl, hP.blk, hpcb, hst⟩

theorem plainRel_fresh (H : S.Hyps) (h : Nat) (st : Local → Nat) (il : Option Span) :
    S.PlainRel ⟨h, 0, 0, st, il⟩ ⟨h, 0, 0, st, il⟩ :=
  ⟨rfl, rfl, rfl, rfl, fun _ => Nat.lt_of_le_of_lt (Nat.zero_le _) H.hb, fun _ _ => Nat.zero_le _,
   ⟨fun _ => rfl, fun _ _ _ => Or.inl rfl⟩⟩

theorem sim_plain_body (H : S.Hyps) {g blk pc : Nat} {il : Option Span} {C M : Local → Nat}
    {sp sq : List Frame} {Fp Fq : Fn} {Bp Bq : Block}
    (hFp : nth? S.p.fns g = some Fp) (hFq : nth? S.q.fns g = some Fq)
    (hBp : nth? Fp.blocks blk = some Bp) (hBq : nth? Fq.blocks blk = some Bq)
    (hstmt : ∀ s, nth? Bp.stmts pc = some s → nth? Bq.stmts pc = some s)
    (hterm : nth? Bp.stmts pc = none →
      nth? Bq.stmts pc = none ∧ Bq.term = Bp.term ∧ Bq.stmts.length = Bp.stmts.length ∧
        ¬ (g = S.f ∧ blk = S.b))
    (hcaps : Fq.caps = Fp.caps)
    (hloc : ∀ sc ∈ Bp.scopeRefs, ∀ sp' il',
      locValue S.p.tracked Fq.scopes sc sp' il' = locValue S.p.tracked Fp.scopes sc sp' il')
    (hP : S.PlainRel ⟨g, blk, pc, C, il⟩ ⟨g, blk, pc, M, il⟩)
    (hnext : g = S.f → blk = S.b → pc + 1 ≤ S.B.stmts.length ∨ nth? Bp.stmts pc = none)
    (hR : RestRel S sp sq) :
    SimOK S (⟨g, blk, pc, C, il⟩ :: sp) (⟨g, blk, pc, M, il⟩ :: sq) := by
  have hreads := pstore_reads H hFp hBp hP.st
  have htr := S.q_tracked H.hF
  cases hs : nth? Bp.stmts pc with
  | some s =>
    have hsq := hstmt s hs
    have hsmem : s ∈ Bp.stmts := nth?_mem _ _ _ hs
    have hpcb : g = S.f → blk = S.b → pc + 1 ≤ S.B.stmts.length := by
      intro h1 h2
      rcases hnext h1 h2 with h | h
      · exact h
      · rw [hs] at h; cases h
    have hrd : ∀ y ∈ s.reads, M y = C y := fun y hy => hreads y (stmt_reads_sub_block hsmem y hy)
    cases s with
    | assign x rv =>
      have hv : evalRv M rv = evalRv C rv :=
        evalRv_congr (fun y hy => hrd y (by simpa [Stmt.reads] using hy))
      refine SimOK.of_eq (step_assign hFp hBp hs) (step_assign hFq hBq hsq) ?_
      simp only [hv]
      exact ConfigRel.running (StackRel.plain (plainRel_next hP hpcb (pstore_upd hP.st x _)) hR)
    | emit o =>
      have hv : evalOp M o = evalOp C o :=
        evalOp_congr (fun y hy => hrd y (by simpa [Stmt.reads] using hy))
      refine SimOK.of_eq (step_emit hFp hBp hs) (by rw [step_emit hFq hBq hsq, hv]) ?_
      exact ConfigRel.running (StackRel.plain (plainRel_next hP hpcb hP.st) hR)
    | needCap c =>
      have hp := step_needCap (fr := ⟨g, blk, pc, C, il⟩) (rest := sp) hFp hBp hs
      have hq := step_needCap (fr := ⟨g, blk, pc, M, il⟩) (rest := sq) hFq hBq hsq
      rw [hcaps] at hq
      cases hc : Fp.caps.contains c with
      | true =>
        simp only [hc, ↓reduceIte] at hp hq
        exact SimOK.of_eq hp hq (ConfigRel.running (StackRel.plain (plainRel_next hP hpcb hP.st) hR))
      | false =>
        simp only [hc, Bool.false_eq_true, ↓reduceIte] at hp hq
        exact SimOK.of_eq hp hq (ConfigRel.halted _)
    | loc sp' sc =>
      have hsc : sc ∈ Bp.scopeRefs := stmt_scopes_sub_block hsmem sc (by simp [Stmt.scopes])
      refine SimOK.of_eq (step_loc hFp hBp hs)
        (by rw [step_loc hFq hBq hsq, htr, hloc sc hsc]) ?_
      exact ConfigRel.running (StackRel.plain (plainRel_next hP hpcb hP.st) hR)
  | none =>
    obtain ⟨hsq, hBt, hlen, hncs⟩ := hterm hs
    have hp := step_term (fr := ⟨g, blk, pc, C, il⟩) (rest := sp) hFp hBp hs
    have hq := step_term (fr := ⟨g, blk, pc, M, il⟩) (rest := sq) hFq hBq hsq
    rw [hBt, hlen] at hq
    have htrd : ∀ y ∈ Bp.term.reads, M y = C y := fun y hy => hreads y (term_reads_sub_block Bp y hy)
    cases hT : Bp.term with
    | goto t =>
      simp only [hT] at hp hq
      exact SimOK.of_eq hp hq (ConfigRel.running (StackRel.plain
        (plainRel_succ H hFp hBp hP.st (by simp [hT, Term.succs]) il) hR))
    | branch o z nz =>
      have hv : evalOp M o = evalOp C o :=
        evalOp_congr (fun y hy => htrd y (by simpa [hT, Term.reads] using hy))
      simp only [hT, hv] at hp hq
      exact SimOK.of_eq hp hq (ConfigRel.running (StackRel.plain
        (plainRel_succ H hFp hBp hP.st (by rw [hT]; simp only [Term.succs]; split <;> simp) il) hR))
    | call ci2 =>
      simp only [hT] at hp hq
      cases hH : nth? S.p.fns ci2.callee with
      | none =>
        have hHq : nth? S.q.fns ci2.callee = none := (H.q_callee_none _).mpr hH
        simp only [hH] at hp
        simp only [hHq] at hq
        exact SimOK.of_eq hp hq (ConfigRel.halted _)
      | some Hp =>
        cases hHq : nth? S.q.fns ci2.callee with
        | none => exact absurd ((H.q_callee_none _).mp hHq) (by rw [hH]; simp)
        | some Hq =>
          have hc2 := H.q_callee ci2.callee
          rw [hH, hHq] at hc2
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc2
          have hargs : ci2.args.map (evalOp M) = ci2.args.map (evalOp C) := by
            apply List.map_congr_left
            intro a ha
            exact evalOp_congr (fun y hy => htrd y (by
              rw [hT]; simp only [Term.reads, List.mem_flatMap]; exact ⟨a, ha, hy⟩))
          have hsc : ci2.scope ∈ Bp.scopeRefs := term_scopes_sub_block Bp _ (by simp [hT, Term.scopes])
          simp only [hH] at hp
          simp only [hHq, hc2.1, hc2.2, hargs, htr, hloc _ hsc, hcaps, q_abi] at hq
          refine SimOK.of_eq hp hq (ConfigRel.running (StackRel.plain (plainRel_fresh H _ _ _)
            (RestRel.plain ⟨rfl, rfl, rfl, rfl, hP.blk, fun h1 h2 => absurd ⟨h1, h2⟩ hncs, hP.st⟩
              (fun h => hncs ⟨h.1, h.2.1⟩) hR)))
    | ret =>
      have hv : M 0 = C 0 := htrd 0 (by simp [hT, Term.reads])
      simp only [hT, hv] at hp hq
      exact SimOK.of_eq hp hq (returnInto_rel H hR _)
    | resume =>
      simp only [hT] at hp hq
      exact SimOK.of_eq hp hq (unwindInto_rel H hR)
    | panic u =>
      simp only [hT] at hp hq
      cases u with
      | cleanup c =>
        simp only [startUnwind] at hp hq
        exact SimOK.of_eq hp hq (ConfigRel.running (StackRel.plain
          (plainRel_succ H hFp hBp hP.st (by simp [hT, Term.succs, Unwind.blocks]) il) hR))
      | «continue» =>
        simp only [startUnwind] at hp hq
        exact SimOK.of_eq hp hq (unwindInto_rel H hR)
      | terminate =>
        simp only [startUnwind] at hp hq
        exact SimOK.of_eq hp hq (ConfigRel.halted _)
    | unreachable =>
      simp only [hT] at hp hq
      exact SimOK.of_eq hp hq (ConfigRel.halted _)
    | abort =>
      simp only [hT] at hp hq
      exact SimOK.of_eq hp hq (ConfigRel.halted _)

theorem sim_plain_call (H : S.Hyps) {il : Option Span} {C M : Local → Nat} {sp sq : List Frame}
    (hP : S.PlainRel ⟨S.f, S.b, S.B.stmts.length, C, il⟩ ⟨S.f, S.b, S.B.stmts.length, M, il⟩)
    (hR : RestRel S sp sq) :
    SimOK S (⟨S.f, S.b, S.B.stmts.length, C, il⟩ :: sp) (⟨S.f, S.b, S.B.stmts.length, M, il⟩ :: sq) := by
  have hst : S.StoreRelF S.b C M := hP.st.2 rfl
  have hreads := storeRelF_reads H H.hB hst
  have hs : nth? S.B.stmts S.B.stmts.length = none := by simp [nth?_eq_getElem?]
  have hp := step_term (fr := ⟨S.f, S.b, S.B.stmts.length, C, il⟩) (rest := sp) H.hF H.hB hs
  simp only [H.hBt, H.hG, H.abiCall, Bool.false_eq_true, ↓reduceIte] at hp
  have hargs : S.ci.args.map (evalOp M) = S.ci.args.map (evalOp C) := by
    apply List.map_congr_left
    intro a ha
    exact evalOp_congr (fun y hy => hreads y (term_reads_sub_block S.B y (by
      rw [H.hBt]; simp only [Term.reads, List.mem_flatMap]; exact ⟨a, ha, hy⟩)))
  have hpro := prologue_spec S.ρ S.ci.args S.G.nlocals M H.inj
    (fun i hi1 hi2 a ha y hy h => by
      have h1 := H.args_lt a ha y hy
      have h2 := H.slotGe i hi1 hi2
      rw [← h] at h1
      exact absurd h1 (Nat.not_lt.mpr h2))
  refine SimOK.of_stepN (Nat.succ_pos _) hp (call_macro H M il sq) ?_
  refine ConfigRel.running (StackRel.merged ⟨rfl, rfl, rfl, rfl, rfl, (Nat.zero_add _).symm, rfl, rfl,
    rfl, ?_, ?_⟩ hR)
  · intro x hx
    show execStores (prologue S.ρ S.ci.args S.G.nlocals) M x = C x ∨ S.loose = some x
    by_cases hall : ∀ i, i < S.G.nlocals → S.ρ i ≠ x
    · rw [hpro.1 x hall]
      rcases hst x hx with h | h
      · exact Or.inl h
      · exact Or.inr h.1
    · right
      have : ∃ i, i < S.G.nlocals ∧ S.ρ i = x := by
        apply Decidable.byContradiction
        intro hne
        exact hall (fun i hi h => hne ⟨i, hi, h⟩)
      obtain ⟨i, hi, rfl⟩ := this
      rcases H.fresh i hi with h | h
      · exact absurd hx (Nat.not_lt.mpr h)
      · exact h
  · intro i hi
    show execStores (prologue S.ρ S.ci.args S.G.nlocals) M (S.ρ i) = _
    rw [hpro.2 i hi, hargs]

theorem sim_merged (H : S.Hyps) {gp cp mq : Frame} {sp sq : List Frame} (hM : S.MergedRel gp cp mq)
    (hR : RestRel S sp sq) : SimOK S (gp :: cp :: sp) (mq :: sq) := by
  obtain ⟨h, j, pc, Gs, ilg⟩ := gp
  obtain ⟨cf, cb, cpc, C, il⟩ := cp
  obtain ⟨mf, mb, mpc, M, mil⟩ := mq
  have e1 := hM.gfn; have e2 := hM.cfn; have e3 := hM.cblk; have e4 := hM.cpc
  have e5 := hM.mfn; have e6 := hM.mblk; have e7 := hM.mpc; have e8 := hM.mil
  simp only at e1 e2 e3 e4 e5 e6 e7 e8
  subst e1 e2 e3 e4 e5 e6 mpc mil
  have htr := S.q_tracked H.hF
  have hgil : ilg = if S.G.trackCaller
      then some (locValue S.p.tracked S.F.scopes S.ci.scope S.ci.span il) else none := hM.gil
  cases hBG : nth? S.G.blocks j with
  | none =>
    have hBq : nth? S.F'.blocks (j + S.base) = none := by rw [S.nth?_F'_base, hBG]; rfl
    exact SimOK.of_eq (step_noBlk (fr := ⟨S.ci.callee, j, pc, Gs, ilg⟩) H.hG hBG)
      (step_noBlk (fr := ⟨S.f, j + S.base, pc, M, il⟩) H.q_f hBq) (ConfigRel.halted _)
  | some BG =>
    have hBq : nth? S.F'.blocks (j + S.base) = some (S.ctx.block BG) := by
      rw [S.nth?_F'_base, hBG]; rfl
    have hBGmem : BG ∈ S.G.blocks := nth?_mem _ _ _ hBG
    have hlocs : ∀ y ∈ BG.locals, y < S.G.nlocals := H.locG BG hBGmem
    have hev : ∀ o : Operand, (∀ y ∈ o.locals, y < S.G.nlocals) →
        evalOp M (o.rename S.ρ) = evalOp Gs o := by
      intro o ho
      cases o with
      | const _ => rfl
      | var x => exact hM.slots x (ho x (by simp [Operand.locals]))
    cases hs : nth? BG.stmts pc with
    | some s =>
      have hsq : nth? (S.ctx.block BG).stmts pc = some (s.rename S.ρ S.F.scopes.length) := by
        simp [SpliceCtx.block, nth?_map, hs, ctx]
      have hsmem : s ∈ BG.stmts := nth?_mem _ _ _ hs
      have hsl : ∀ y ∈ s.locals, y < S.G.nlocals := fun y hy => hlocs y (stmt_locals_sub_block hsmem y hy)
      cases s with
      | assign x rv =>
        have hx : x < S.G.nlocals := hsl x (by simp [Stmt.locals])
        have hv : evalRv M (rv.rename S.ρ) = evalRv Gs rv := by
          cases rv with
          | use o => exact hev o (fun y hy => hsl y (by simp [Stmt.locals, Rvalue.locals, hy]))
          | add a b =>
            simp only [Rvalue.rename, evalRv]
            rw [hev a (fun y hy => hsl y (by simp [Stmt.locals, Rvalue.locals, hy])),
              hev b (fun y hy => hsl y (by simp [Stmt.locals, Rvalue.locals, hy]))]
        simp only [Stmt.rename] at hsq
        refine SimOK.of_eq (step_assign (fr := ⟨S.ci.callee, j, pc, Gs, ilg⟩) H.hG hBG hs)
          (step_assign (fr := ⟨S.f, j + S.base, pc, M, il⟩) H.q_f hBq hsq) ?_
        obtain ⟨hh, hsl'⟩ := merged_store_upd H hM.host hM.slots hx (evalRv Gs rv)
        simp only [hv]
        exact ConfigRel.running (StackRel.merged ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hgil, hh, hsl'⟩ hR)
      | emit o =>
        simp only [Stmt.rename] at hsq
        have hv := hev o (fun y hy => hsl y (by simpa [Stmt.locals] using hy))
        refine SimOK.of_eq (step_emit (fr := ⟨S.ci.callee, j, pc, Gs, ilg⟩) H.hG hBG hs)
          (by rw [step_emit (fr := ⟨S.f, j + S.base, pc, M, il⟩) H.q_f hBq hsq, hv]) ?_
        exact ConfigRel.running (StackRel.merged ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hgil,
          hM.host, hM.slots⟩ hR)
      | needCap c =>
        simp only [Stmt.rename] at hsq
        have hp := step_needCap (fr := ⟨S.ci.callee, j, pc, Gs, ilg⟩) (rest := ⟨S.f, S.b, S.B.stmts.length, C, il⟩ :: sp) H.hG hBG hs
        have hq := step_needCap (fr := ⟨S.f, j + S.base, pc, M, il⟩) (rest := sq) H.q_f hBq hsq
        rw [F'_caps, H.caps BG hBGmem c hsmem] at hq
        cases hc : S.G.caps.contains c with
        | true =>
          simp only [hc, ↓reduceIte] at hp hq
          exact SimOK.of_eq hp hq (ConfigRel.running (StackRel.merged ⟨rfl, rfl, rfl, rfl, rfl, rfl,
            rfl, rfl, hgil, hM.host, hM.slots⟩ hR))
        | false =>
          simp only [hc, Bool.false_eq_true, ↓reduceIte] at hp hq
          exact SimOK.of_eq hp hq (ConfigRel.halted _)
      | loc sp' sc =>
        simp only [Stmt.rename] at hsq
        have hsc : sc ∈ BG.scopeRefs := stmt_scopes_sub_block hsmem sc (by simp [Stmt.scopes])
        refine SimOK.of_eq (step_loc (fr := ⟨S.ci.callee, j, pc, Gs, ilg⟩) H.hG hBG hs)
          (by rw [step_loc (fr := ⟨S.f, j + S.base, pc, M, il⟩) H.q_f hBq hsq, htr,
                H.locCallee hBGmem il sc hsc sp', ← hgil]) ?_
        exact ConfigRel.running (StackRel.merged ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hgil,
          hM.host, hM.slots⟩ hR)
    | none =>
      have hsq : nth? (S.ctx.block BG).stmts pc = none := by
        simp [SpliceCtx.block, nth?_map, hs]
      have hp := step_term (fr := ⟨S.ci.callee, j, pc, Gs, ilg⟩)
        (rest := ⟨S.f, S.b, S.B.stmts.length, C, il⟩ :: sp) H.hG hBG hs
      have hq := step_term (fr := ⟨S.f, j + S.base, pc, M, il⟩) (rest := sq) H.q_f hBq hsq
      simp only [SpliceCtx.block, List.length_map] at hq
      have htl : ∀ y ∈ BG.term.locals, y < S.G.nlocals := fun y hy => hlocs y (term_locals_sub_block BG y hy)
      have hmerged_jump : ∀ t, ConfigRel S
          (.running (⟨S.ci.callee, t, 0, Gs, ilg⟩ :: ⟨S.f, S.b, S.B.stmts.length, C, il⟩ :: sp))
          (.running (⟨S.f, t + S.base, 0, M, il⟩ :: sq)) := fun t =>
        ConfigRel.running (StackRel.merged ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hgil,
          hM.host, hM.slots⟩ hR)
      have hunw := unwind_from_cp H hM hR (unwindInto_rel H hR)
      cases hT : BG.term with
      | goto t =>
        simp only [hT, SpliceCtx.term] at hp hq
        exact SimOK.of_eq hp hq (hmerged_jump t)
      | branch o z nz =>
        have hv := hev o (fun y hy => htl y (by simp [hT, Term.locals, hy]))
        simp only [hT, SpliceCtx.term, ctx, hv] at hp hq
        refine SimOK.of_eq hp hq ?_
        by_cases hz : evalOp Gs o = 0
        · simp only [hz, ↓reduceIte]; exact hmerged_jump z
        · simp only [hz, ↓reduceIte]; exact hmerged_jump nz
      | call ci2 =>
        simp only [hT, SpliceCtx.term] at hp hq
        cases hH : nth? S.p.fns ci2.callee with
        | none =>
          have hHq : nth? S.q.fns ci2.callee = none := (H.q_callee_none _).mpr hH
          simp only [hH] at hp
          simp only [hHq] at hq
          exact SimOK.of_eq hp hq (ConfigRel.halted _)
        | some Hp =>
          cases hHq : nth? S.q.fns ci2.callee with
          | none => exact absurd ((H.q_callee_none _).mp hHq) (by rw [hH]; simp)
          | some Hq =>
            have hc2 := H.q_callee ci2.callee
            rw [hH, hHq] at hc2
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc2
            have hargs : (ci2.args.map (Operand.rename S.ρ)).map (evalOp M) = ci2.args.map (evalOp Gs) := by
              rw [List.map_map]
              apply List.map_congr_left
              intro a ha
              exact hev a (fun y hy => htl y (by
                rw [hT]; simp only [Term.locals, List.mem_cons, List.mem_flatMap]; exact Or.inr ⟨a, ha, hy⟩))
            have hsc : ci2.scope ∈ BG.scopeRefs := term_scopes_sub_block BG _ (by simp [hT, Term.scopes])
            have habi : (ci2.abiSensitive && (S.p.abi S.F.caps != S.p.abi Hp.caps)) =
                (ci2.abiSensitive && (S.p.abi S.G.caps != S.p.abi Hp.caps)) := by
              cases ha : ci2.abiSensitive with
              | false => rfl
              | true => rw [H.abiG BG hBGmem ci2 hT ha]
            simp only [hH] at hp
            simp only [hHq, hc2.1, hc2.2, ctx, hargs, htr, F'_caps, q_abi, habi] at hq
            rw [H.locCallee hBGmem il _ hsc, ← hgil] at hq
            exact SimOK.of_eq hp hq (ConfigRel.running (StackRel.plain (plainRel_fresh H _ _ _)
              (RestRel.merged ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hgil, hM.host, hM.slots⟩ hR)))
      | ret =>
        have h0 : 0 < S.G.nlocals := htl 0 (by simp [hT, Term.locals])
        simp only [hT] at hp
        rw [returnInto_cons_call (curTerm_cp H hM)] at hp
        cases ht : S.ci.target with
        | none =>
          simp only [ht] at hp
          simp only [hT, SpliceCtx.term, ctx, ht, Option.map_none] at hq
          exact SimOK.of_eq hp hq (ConfigRel.halted _)
        | some t =>
          simp only [ht] at hp
          refine SimOK.of_stepN (by omega) hp (ret_macro H hBG hs hT ht) ?_
          refine ConfigRel.running (StackRel.plain ⟨rfl, rfl, rfl, rfl, fun _ => H.target_lt ht,
            fun _ _ => Nat.zero_le _, fun h => absurd rfl h, fun _ => ?_⟩ hR)
          intro x hx
          left
          have hv : M (S.ρ 0) = Gs 0 := hM.slots 0 h0
          rcases H.mode with ⟨tt, hret, hl⟩ | ⟨hret, hl⟩
          · have hρ0 : S.ρ 0 = tt := by simp [ρ, InlineCfg.rename, hret]
            simp only [retStmts, hret, execStores_cons, execStores_nil, stmtStore, evalRv, evalOp]
            rw [hρ0] at hv
            by_cases hxd : x = S.ci.dest
            · subst hxd; simp [upd, hv]
            · simp only [upd, hxd, ↓reduceIte]
              rcases hM.host x hx with h | h
              · exact h
              · rw [hl] at h; cases h
          · have hρ0 : S.ρ 0 = S.ci.dest := by simp [ρ, InlineCfg.rename, hret]
            simp only [retStmts, hret, execStores_nil]
            rw [hρ0] at hv
            by_cases hxd : x = S.ci.dest
            · subst hxd; simp [upd, hv]
            · simp only [upd, hxd, ↓reduceIte]
              rcases hM.host x hx with h | h
              · exact h
              · rw [hl] at h; cases h; exact absurd rfl hxd
      | resume =>
        simp only [hT] at hp
        simp only [hT, SpliceCtx.term, ctx, H.res] at hq
        cases hu : S.ci.unwind with
        | cleanup c =>
          simp only [hu] at hq
          simp only [hu, startUnwind] at hunw
          exact SimOK.of_eq hp hq hunw
        | «continue» =>
          simp only [hu] at hq
          simp only [hu, startUnwind] at hunw
          exact SimOK.of_eq hp hq hunw
        | terminate =>
          simp only [hu] at hq
          simp only [hu, startUnwind] at hunw
          exact SimOK.of_eq hp hq hunw
      | panic u =>
        simp only [hT, SpliceCtx.term] at hp hq
        cases u with
        | cleanup c =>
          simp only [SpliceCtx.mapUnwind, startUnwind] at hp hq
          exact SimOK.of_eq hp hq (hmerged_jump c)
        | «continue» =>
          simp only [startUnwind] at hp
          rw [startUnwind_mapUnwind_continue H] at hq
          exact SimOK.of_eq hp hq hunw
        | terminate =>
          simp only [SpliceCtx.mapUnwind, startUnwind] at hp hq
          exact SimOK.of_eq hp hq (ConfigRel.halted _)
      | unreachable =>
        simp only [hT, SpliceCtx.term] at hp hq
        exact SimOK.of_eq hp hq (ConfigRel.halted _)
      | abort =>
        simp only [hT, SpliceCtx.term] at hp hq
        exact SimOK.of_eq hp hq (ConfigRel.halted _)

theorem sim_step (H : S.Hyps) {s s' : List Frame} (h : StackRel S s s') : SimOK S s s' := by
  cases h with
  | @plain fp fq sp sq hP hR =>
    obtain ⟨g, blk, pc, C, il⟩ := fp
    obtain ⟨g', blk', pc', M, il'⟩ := fq
    have e1 := hP.fn; have e2 := hP.block; have e3 := hP.pc; have e4 := hP.il
    simp only at e1 e2 e3 e4
    subst g' blk' pc' il'
    by_cases hg : g = S.f
    · subst hg
      have hblk : blk < S.nb := hP.blk rfl
      by_cases hb : blk = S.b
      · subst hb
        have hpc : pc ≤ S.B.stmts.length := hP.pcb rfl rfl
        by_cases hpcl : pc = S.B.stmts.length
        · subst hpcl
          exact sim_plain_call H hP hR
        · have hlt : pc < S.B.stmts.length := by omega
          refine sim_plain_body H H.hF H.q_f H.hB (S.nth?_F'_b H.hb) ?_ ?_ (F'_caps S)
            (H.locHost H.hBmem) hP (fun _ _ => Or.inl hlt) hR
          · intro st hst
            rw [← hst]
            simp only [callBlk, nth?_eq_getElem?]
            exact List.getElem?_append_left hlt
          · intro hn
            exfalso
            rw [nth?_eq_getElem?, List.getElem?_eq_none_iff] at hn
            omega
      · obtain ⟨Bp, hBp⟩ : ∃ Bp, nth? S.F.blocks blk = some Bp := by
          cases h : nth? S.F.blocks blk with
          | none => exact absurd h (nth?_ne_none_of_lt _ _ hblk)
          | some Bp => exact ⟨Bp, rfl⟩
        exact sim_plain_body H H.hF H.q_f hBp (by rw [S.nth?_F'_lt blk hblk hb]; exact hBp)
          (fun _ h => h) (fun hn => ⟨hn, rfl, rfl, fun h => hb h.2⟩) (F'_caps S)
          (H.locHost (nth?_mem _ _ _ hBp)) hP (fun _ h => absurd h hb) hR
    · have hq := H.q_ne hg
      cases hFp : nth? S.p.fns g with
      | none =>
        rw [hFp] at hq
        exact SimOK.of_eq (step_noFn (fr := ⟨g, blk, pc, C, il⟩) hFp)
          (step_noFn (fr := ⟨g, blk, pc, M, il⟩) hq) (ConfigRel.halted _)
      | some Fp =>
        rw [hFp] at hq
        have hst : M = C := hP.st.1 hg
        subst hst
        cases hBp : nth? Fp.blocks blk with
        | none =>
          exact SimOK.of_eq (step_noBlk (fr := ⟨g, blk, pc, M, il⟩) hFp hBp)
            (step_noBlk (fr := ⟨g, blk, pc, M, il⟩) hq hBp) (ConfigRel.halted _)
        | some Bp =>
          exact sim_plain_body H hFp hq hBp hBp (fun _ h => h) (fun hn => ⟨hn, rfl, rfl, fun h => hg h.1⟩)
            rfl (fun _ _ _ _ => rfl) hP (fun h => absurd h hg) hR
  | @merged gp cp mq sp sq hM hR => exact sim_merged H hM hR

theorem init_rel (H : S.Hyps) (e : Entry) : ConfigRel S (init S.p e) (init S.q e) := by
  unfold init
  by_cases hg : e.fn = S.f
  · rw [hg, H.hF, H.q_f]
    exact ConfigRel.running (StackRel.plain (plainRel_fresh H _ _ _) RestRel.nil)
  · rw [H.q_ne hg]
    cases nth? S.p.fns e.fn with
    | none => exact ConfigRel.halted _
    | some Fe => exact ConfigRel.running (StackRel.plain (plainRel_fresh H _ _ _) RestRel.nil)

theorem inline_eq_q (H : S.Hyps) : inline S.p S.f S.b S.cfg = S.q := by
  simp only [inline, H.hF, H.hB, H.hBt, H.hG]
  rfl

/-- The simulation theorem: under `Hyps`, inlining is a behavioural equivalence. -/
theorem behEquiv_of_hyps (H : S.Hyps) : BehEquiv S.p (inline S.p S.f S.b S.cfg) := by
  rw [inline_eq_q H]
  intro e
  refine behEquivAt_of_sim S.p S.q (ConfigRel S) ?_ ?_ ?_ e (init_rel H e)
  · intro o c' h; cases h; rfl
  · intro s c' h; cases h; exact ⟨_, rfl⟩
  · intro s s' h
    cases h with
    | running hs => exact sim_step H hs

end Site

/-! ## Establishing `Hyps` from the hypotheses of the whole-program theorems -/

theorem callSite_block {p : Program} {f b : Nat} {F : Fn} {ci : CallInfo} {G : Fn}
    (hsite : IsCallSite p f b F ci G) : ∃ B, nth? F.blocks b = some B ∧ B.term = .call ci := by
  obtain ⟨-, hB, -⟩ := hsite
  cases h : nth? F.blocks b with
  | none => rw [h] at hB; cases hB
  | some B => rw [h] at hB; exact ⟨B, rfl, Option.some.inj hB⟩

/-- Temporary return place: the facts of `Site.Hyps` with `loose = none`. -/
theorem hyps_temp (p : Program) (f b : Nat) (F : Fn) (B : Block) (ci : CallInfo) (G : Fn)
    (cfg : InlineCfg) (t : Local)
    (hF : nth? p.fns f = some F) (hB : nth? F.blocks b = some B) (hBt : B.term = .call ci)
    (hG : nth? p.fns ci.callee = some G)
    (hlocF : LocalsBounded F) (hlocG : LocalsBounded G) (hblkF : BlocksBounded F)
    (hscF : ScopesWF F) (hscG : ScopesWF G)
    (hfresh : SlotsFresh cfg F G) (hinj : SlotsInjective cfg G)
    (hret : cfg.ret = .temp t) (htemp : TempFresh t cfg F G)
    (hcont : cfg.redirectContinue = true) (hres : cfg.resumeMap = .unwind)
    (hlink : cfg.link = .rustc)
    (hcapsOk : ∀ BG ∈ G.blocks, ∀ c, Stmt.needCap c ∈ BG.stmts → F.caps.contains c = G.caps.contains c)
    (habiCall : (ci.abiSensitive && (p.abi F.caps != p.abi G.caps)) = false)
    (habiG : ∀ BG ∈ G.blocks, ∀ ci2, BG.term = .call ci2 → ci2.abiSensitive = true →
      p.abi F.caps = p.abi G.caps) :
    Site.Hyps ⟨p, f, b, F, B, ci, G, cfg, none⟩ := by
  have hρ : ∀ i, cfg.rename ci.dest i = if i = 0 then t else cfg.slot i := by
    intro i; simp [InlineCfg.rename, hret]
  refine ⟨hF, hB, hBt, hG, hlocF, hlocG, hblkF, hscF, hscG, ?_, ?_, ?_, ?_, Or.inl ⟨t, hret, rfl⟩,
    hcont, hres, hlink, hcapsOk, habiCall, habiG⟩
  · intro i hi j hj h
    simp only [Site.ρ, hρ] at h
    by_cases hi0 : i = 0
    · by_cases hj0 : j = 0
      · rw [hi0, hj0]
      · simp only [hi0, hj0, ↓reduceIte] at h
        exact absurd h.symm (htemp.2 j hj (by omega))
    · by_cases hj0 : j = 0
      · simp only [hi0, hj0, ↓reduceIte] at h
        exact absurd h (htemp.2 i hi (by omega))
      · simp only [hi0, hj0, ↓reduceIte] at h
        exact hinj i hi j hj (by omega) (by omega) h
  · intro i hi
    left
    simp only [Site.ρ, hρ]
    by_cases hi0 : i = 0
    · simp only [hi0, ↓reduceIte]; exact htemp.1
    · simp only [hi0, ↓reduceIte]; exact hfresh i hi (by omega)
  · intro i hi1 hi2
    simp only [Site.ρ, hρ]
    have hi0 : i ≠ 0 := by omega
    simp only [hi0, ↓reduceIte]
    exact hfresh i hi2 hi1
  · intro d hd; cases hd

/-- Destination return place: the facts of `Site.Hyps` with `loose = some ci.dest`. -/
theorem hyps_dest (p : Program) (f b : Nat) (F : Fn) (B : Block) (ci : CallInfo) (G : Fn)
    (cfg : InlineCfg)
    (hF : nth? p.fns f = some F) (hB : nth? F.blocks b = some B) (hBt : B.term = .call ci)
    (hG : nth? p.fns ci.callee = some G)
    (hlocF : LocalsBounded F) (hlocG : LocalsBounded G) (hblkF : BlocksBounded F)
    (hscF : ScopesWF F) (hscG : ScopesWF G)
    (hfresh : SlotsFresh cfg F G) (hinj : SlotsInjective cfg G)
    (hret : cfg.ret = .dest)
    (hclosed : CleanupClosed F) (hdest : DestNotReadInCleanup F ci.dest)
    (hcont : cfg.redirectContinue = true) (hres : cfg.resumeMap = .unwind)
    (hlink : cfg.link = .rustc)
    (hcapsOk : ∀ BG ∈ G.blocks, ∀ c, Stmt.needCap c ∈ BG.stmts → F.caps.contains c = G.caps.contains c)
    (habiCall : (ci.abiSensitive && (p.abi F.caps != p.abi G.caps)) = false)
    (habiG : ∀ BG ∈ G.blocks, ∀ ci2, BG.term = .call ci2 → ci2.abiSensitive = true →
      p.abi F.caps = p.abi G.caps) :
    Site.Hyps ⟨p, f, b, F, B, ci, G, cfg, some ci.dest⟩ := by
  have hρ : ∀ i, cfg.rename ci.dest i = if i = 0 then ci.dest else cfg.slot i := by
    intro i; simp [InlineCfg.rename, hret]
  have hBmem : B ∈ F.blocks := nth?_mem _ _ _ hB
  have hdlt : ci.dest < F.nlocals := by
    apply hlocF B hBmem
    apply term_locals_sub_block
    rw [hBt]
    simp [Term.locals]
  refine ⟨hF, hB, hBt, hG, hlocF, hlocG, hblkF, hscF, hscG, ?_, ?_, ?_, ?_, Or.inr ⟨hret, rfl⟩,
    hcont, hres, hlink, hcapsOk, habiCall, habiG⟩
  · intro i hi j hj h
    simp only [Site.ρ, hρ] at h
    by_cases hi0 : i = 0
    · by_cases hj0 : j = 0
      · rw [hi0, hj0]
      · simp only [hi0, hj0, ↓reduceIte] at h
        have := hfresh j hj (by omega)
        rw [← h] at this
        exact absurd hdlt (Nat.not_lt.mpr this)
    · by_cases hj0 : j = 0
      · simp only [hi0, hj0, ↓reduceIte] at h
        have := hfresh i hi (by omega)
        rw [h] at this
        exact absurd hdlt (Nat.not_lt.mpr this)
      · simp only [hi0, hj0, ↓reduceIte] at h
        exact hinj i hi j hj (by omega) (by omega) h
  · intro i hi
    simp only [Site.ρ, hρ]
    by_cases hi0 : i = 0
    · right; simp [hi0]
    · left; simp only [hi0, ↓reduceIte]; exact hfresh i hi (by omega)
  · intro i hi1 hi2
    simp only [Site.ρ, hρ]
    have hi0 : i ≠ 0 := by omega
    simp only [hi0, ↓reduceIte]
    exact hfresh i hi2 hi1
  · intro d hd
    cases hd
    exact ⟨hclosed, hdest⟩

/-- Capability legality: under `CapsSubset G F` and `CapLegal G`, every `needCap` of the callee
succeeds in the host exactly when it succeeds in the callee. -/
theorem capsOk_of_subset_legal {F G : Fn} (hsub : CapsSubset G F) (hlegal : CapLegal G) :
    ∀ BG ∈ G.blocks, ∀ c, Stmt.needCap c ∈ BG.stmts → F.caps.contains c = G.caps.contains c := by
  intro BG hBG c hc
  have hG : G.caps.contains c = true := hlegal BG hBG _ hc
  have hmem : c ∈ G.caps := List.elem_iff.mp hG
  have hF : F.caps.contains c = true := List.elem_iff.mpr (hsub c hmem)
  rw [hF, hG]

end InlineSim
end Toy.Inline
