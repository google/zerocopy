import ToyCFI.Lemmas
import ToyCFI.LSDA

/-!
# Multi-frame unwinding with call-site lookup

A stack of frames, innermost first.  Each frame is suspended at a `call`
operation of its function and carries that function's CFI program, an optional
call-site table, and a frame size.  The toy unwinder consults the call-site
table of the current frame (as a C++-style personality routine would), stops at
the first frame whose call site has a landing pad, and otherwise applies the
frame's row to obtain its caller's state.
-/

namespace Toy.CFI

/-- A suspended frame. `callPC` is the linear address of the `call` operation
at which it is suspended; `frameSize` locates its frame base below the CFA. -/
structure Frame where
  fn : Func
  prog : List CFIInst
  lsda : Option LSDA
  callPC : Nat
  frameSize : Nat

/-- Per-frame decision of the toy personality routine. -/
inductive FrameAction
  | handle (lp : Nat)
  | skip
  | terminate
  deriving DecidableEq, Repr

/-- No call-site table: skip the frame.  With a table (early-exit scan): a
landing pad handles, an entry without landing pad skips, and a call PC that no
entry covers terminates. -/
def frameAction (fr : Frame) : FrameAction :=
  match fr.lsda with
  | none => .skip
  | some t =>
    match lookupScan t fr.callPC with
    | .landingPad lp => .handle lp
    | .noLandingPad => .skip
    | .notFound => .terminate

/-- Caller state reconstructed by applying row `R` to `st`: `sp` becomes the
CFA, other registers follow their rules, memory is unchanged. -/
def unwindRegs (R : Row) (st : MState) : MState :=
  { regs := ⟨cfaOf R st, ruleVal R st .fp, ruleVal R st .s1, ruleVal R st .t1⟩, mem := st.mem }

/-- Outcome of unwinding. -/
inductive Outcome
  | caught (depth lp : Nat) (st : MState)
  | terminated (depth : Nat)
  | escaped
  | malformed (depth : Nat)

/-- Iterated unwinding from frame depth `d` in state `st`. -/
def unwindFrom : List Frame → Nat → MState → Outcome
  | [], _, _ => .escaped
  | fr :: rest, d, st =>
    match frameAction fr with
    | .handle lp => .caught d lp st
    | .terminate => .terminated d
    | .skip =>
      match rowAt? fr.prog fr.callPC with
      | none => .malformed d
      | some R => unwindFrom rest (d + 1) (unwindRegs R st)

/-- Unwind from the innermost frame. -/
def unwind (frames : List Frame) (st : MState) : Outcome := unwindFrom frames 0 st

/-- Frame base computed from a row: `CFA - frameSize`. -/
def frameBase (R : Row) (st : MState) (frameSize : Nat) : Int := cfaOf R st - frameSize

/-- Ground-truth caller of frame `j`: the true state of frame `j + 1` (its `sp`
is the CFA of frame `j`), or `top` for the outermost frame. -/
def callerCtx (truth : List MState) (top : Caller) (j : Nat) : Caller :=
  match truth[j + 1]? with
  | some s => ⟨s.regs.get .sp, s.regs⟩
  | none => top

/-- `st` is a reachable state of `fr.fn`, called by `c`, at the `call` operation
whose address is `fr.callPC`. -/
def AtCallSite (fr : Frame) (c : Caller) (st : MState) : Prop :=
  ∃ m b k, fr.fn.pcOf b k = some fr.callPC ∧ fr.fn.opAt b k = some .call ∧ Reach fr.fn c m b k st

/-- The true frame states form a call chain: frame `j`'s true state is reachable
in its function when called from frame `j + 1`'s true state. -/
def ChainReachable (frames : List Frame) (truth : List MState) (top : Caller) : Prop :=
  frames.length = truth.length ∧
    ∀ j fr st, frames[j]? = some fr → truth[j]? = some st → AtCallSite fr (callerCtx truth top j) st

/-- Agreement on `sp` and the callee-saved registers. -/
def Agree (st σ : MState) : Prop :=
  st.regs.get .sp = σ.regs.get .sp ∧ ∀ r ∈ calleeSaved, st.regs.get r = σ.regs.get r

/-- The CFA base register is `sp` or callee-saved (so a callee preserves it). -/
def CfaBaseSafe (R : Row) : Prop := R.cfaReg = .sp ∨ R.cfaReg ∈ calleeSaved

/-- Memory `M` agrees with the true memory of `σ` at every save slot read by
`R`'s callee-saved rules. -/
def SlotsPreserved (R : Row) (M : Int → Int) (σ : MState) : Prop :=
  ∀ r ∈ calleeSaved, ∀ k, R.rules.get r = .offset k → M (cfaOf R σ + k) = σ.mem (cfaOf R σ + k)

/-- Frames `0, …, j` form a call chain: frame `i`'s true state is reachable at
its `call` when its function is called from frame `i + 1`'s true state (or from
`top` if there is none). -/
def ChainUpTo (frames : List Frame) (truth : List MState) (top : Caller) (j : Nat) : Prop :=
  ∀ i fr st, i ≤ j → frames[i]? = some fr → truth[i]? = some st →
    AtCallSite fr (callerCtx truth top i) st

/-- The tables of frames `0, …, j` are correct. -/
def TablesUpTo (frames : List Frame) (j : Nat) : Prop :=
  ∀ i fr, i ≤ j → frames[i]? = some fr → TableCorrect fr.fn fr.prog

/-- Frames `0, …, j-1` are skipped by the toy personality routine. -/
def SkippedBelow (frames : List Frame) (j : Nat) : Prop :=
  ∀ i fr, i < j → frames[i]? = some fr → frameAction fr = .skip

/-- The call-site rows of frames `1, …, j` have a safe CFA base register. -/
def BaseSafeUpTo (frames : List Frame) (j : Nat) : Prop :=
  ∀ i fr R, 0 < i → i ≤ j → frames[i]? = some fr → rowAt? fr.prog fr.callPC = some R →
    CfaBaseSafe R

/-- Memory `M` still holds the save slots read by the call-site rows of frames
`1, …, j-1`. -/
def SlotsPreservedBelow (frames : List Frame) (truth : List MState) (M : Int → Int) (j : Nat) :
    Prop :=
  ∀ i fr σ R, 0 < i → i < j → frames[i]? = some fr → truth[i]? = some σ →
    rowAt? fr.prog fr.callPC = some R → SlotsPreserved R M σ

/-- The conclusion of the composition theorem: unwinding from `st0` stops at
frame `j` with landing pad `lp` in a state `st` that agrees with frame `j`'s
true state `stj` on `sp` and the callee-saved registers and whose memory is the
throw-time memory `st0.mem`; frame `j`'s CFI program has a row `R` at its call
site, and in `st` that row computes frame `j`'s true CFA and hence the frame
base `CFA - frameSize`. -/
def CaughtWithCallerState (frames : List Frame) (truth : List MState) (top : Caller)
    (st0 : MState) (j lp : Nat) (frj : Frame) (stj : MState) : Prop :=
  ∃ st R, unwind frames st0 = .caught j lp st ∧ Agree st stj ∧ st.mem = st0.mem ∧
    rowAt? frj.prog frj.callPC = some R ∧
    cfaOf R st = (callerCtx truth top j).cfa ∧
    frameBase R st frj.frameSize = (callerCtx truth top j).cfa - frj.frameSize

/-- Frames `0, …, j` have well-formed call-site tables at their call PCs:
sorted by start address and with at most one distinct entry value containing
the call PC. -/
def LsdaWellFormedUpTo (frames : List Frame) (j : Nat) : Prop :=
  ∀ i fr t, i ≤ j → frames[i]? = some fr → fr.lsda = some t →
    SortedByStart t ∧ UniqueAt t fr.callPC

/-- Declarative skip condition: the frame has no call-site table, or some entry
of its table contains the call PC and has no landing pad. -/
def DeclarativeSkip (fr : Frame) : Prop :=
  fr.lsda = none ∨ ∃ t e, fr.lsda = some t ∧ e ∈ t ∧ e.contains fr.callPC ∧ e.lp = none

/-- Frames `0, …, j-1` satisfy the declarative skip condition. -/
def DeclarativeSkippedBelow (frames : List Frame) (j : Nat) : Prop :=
  ∀ i fr, i < j → frames[i]? = some fr → DeclarativeSkip fr

/-- Declarative catch condition: some entry of the frame's call-site table
contains the call PC and has landing pad `lp`. -/
def DeclarativeCatch (fr : Frame) (lp : Nat) : Prop :=
  ∃ t e, fr.lsda = some t ∧ e ∈ t ∧ e.contains fr.callPC ∧ e.lp = some lp

/-! ## Single-step lemmas -/

theorem atCallSite_recovers {fr : Frame} {c : Caller} {σ : MState} (hat : AtCallSite fr c σ)
    (htab : TableCorrect fr.fn fr.prog) :
    ∃ R, rowAt? fr.prog fr.callPC = some R ∧ Recovers R c σ := by
  obtain ⟨m, b, k, hpc, -, hr⟩ := hat
  exact htab.row_at hr hpc

/-- The whole-chain hypothesis implies its prefix form. -/
theorem ChainReachable.upTo {frames : List Frame} {truth : List MState} {top : Caller}
    (h : ChainReachable frames truth top) (j : Nat) : ChainUpTo frames truth top j :=
  fun i fr st _ hf ht => h.2 i fr st hf ht

/-- **Frame lemma.** A row that recovers caller `c` from the true state `σ` also
recovers it from any state agreeing with `σ` on what the row reads. -/
theorem recovers_of_reads_agree {R : Row} {c : Caller} {σ st : MState} (hrec : Recovers R c σ)
    (hcfa : st.regs.get R.cfaReg = σ.regs.get R.cfaReg)
    (hsame : ∀ r ∈ calleeSaved, R.rules.get r = .same → st.regs.get r = σ.regs.get r)
    (hslot : ∀ r ∈ calleeSaved, ∀ k, R.rules.get r = .offset k →
      st.mem (cfaOf R σ + k) = σ.mem (cfaOf R σ + k)) :
    Recovers R c st := by
  have hc : cfaOf R st = cfaOf R σ := by simp only [cfaOf, hcfa]
  refine ⟨hc.trans hrec.1, fun r hr => ?_⟩
  have h := hrec.2 r hr
  unfold ruleVal at h ⊢
  cases hR : R.rules.get r with
  | same => simp only [hR] at h ⊢; rw [hsame r hr hR]; exact h
  | offset k => simp only [hR] at h ⊢; rw [hc, hslot r hr k hR]; exact h

theorem unwindRegs_agree {R : Row} {c : Caller} {st : MState} (h : Recovers R c st) :
    (unwindRegs R st).regs.get .sp = c.cfa ∧
      ∀ r ∈ calleeSaved, (unwindRegs R st).regs.get r = c.regs.get r := by
  refine ⟨h.1, fun r hr => ?_⟩
  have := h.2 r hr
  simp only [calleeSaved, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact this

/-! ## Composition -/

/-- Generalized form of the composition theorem: unwinding from a state `st`
that agrees with the true innermost state (on `sp`, callee-saved registers, and
whatever the innermost row reads). -/
theorem unwindFrom_caught_of_chain : ∀ (j : Nat) (frames : List Frame) (truth : List MState)
    (top : Caller) (d : Nat) (st σ0 : MState) (M : Int → Int),
    (∀ i fr st, i ≤ j → frames[i]? = some fr → truth[i]? = some st →
      AtCallSite fr (callerCtx truth top i) st) →
    (∀ i fr, i ≤ j → frames[i]? = some fr → TableCorrect fr.fn fr.prog) →
    truth[0]? = some σ0 → Agree st σ0 → st.mem = M →
    (∀ fr R, frames[0]? = some fr → rowAt? fr.prog fr.callPC = some R →
      st.regs.get R.cfaReg = σ0.regs.get R.cfaReg ∧
      (0 < j → (∀ r ∈ calleeSaved, R.rules.get r = .same → st.regs.get r = σ0.regs.get r) ∧
        ∀ r ∈ calleeSaved, ∀ k, R.rules.get r = .offset k →
          st.mem (cfaOf R σ0 + k) = σ0.mem (cfaOf R σ0 + k))) →
    (∀ i fr R, 0 < i → i ≤ j → frames[i]? = some fr → rowAt? fr.prog fr.callPC = some R →
      CfaBaseSafe R) →
    (∀ i fr σ R, 0 < i → i < j → frames[i]? = some fr → truth[i]? = some σ →
      rowAt? fr.prog fr.callPC = some R → SlotsPreserved R M σ) →
    (∀ i fr, i < j → frames[i]? = some fr → frameAction fr = .skip) →
    ∀ frj stj lp, frames[j]? = some frj → truth[j]? = some stj → frameAction frj = .handle lp →
    ∃ st', unwindFrom frames d st = .caught (d + j) lp st' ∧ Agree st' stj ∧ st'.mem = M ∧
      ∀ R, rowAt? frj.prog frj.callPC = some R → cfaOf R st' = (callerCtx truth top j).cfa := by
  intro j
  induction j with
  | zero =>
    intro frames truth top d st σ0 M hchain htab h0 hag hmem hfirst _ _ _ frj stj lp hj htj hcatch
    rw [h0] at htj
    cases htj
    cases frames with
    | nil => cases hj
    | cons fr rest =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      refine ⟨st, by simp [unwindFrom, hcatch], hag, hmem, fun R hR => ?_⟩
      obtain ⟨R', hR', hrec⟩ :=
        atCallSite_recovers (hchain 0 _ _ (Nat.le_refl _) rfl h0) (htab 0 _ (Nat.le_refl _) rfl)
      rw [hR] at hR'; cases hR'
      rw [← hrec.1]
      simp only [cfaOf, (hfirst _ R rfl hR).1]
  | succ j ih =>
    intro frames truth top d st σ0 M hchain htab h0 hag hmem hfirst hbase hslots hskip
      frj stj lp hj htj hcatch
    cases frames with
    | nil => cases hj
    | cons fr rest =>
    cases truth with
    | nil => cases h0
    | cons σ0' truth' =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
    subst σ0'
    have hskip0 : frameAction fr = .skip := hskip 0 fr (Nat.succ_pos _) rfl
    obtain ⟨R, hR, hrec⟩ :=
      atCallSite_recovers (hchain 0 fr σ0 (Nat.zero_le _) rfl rfl) (htab 0 fr (Nat.zero_le _) rfl)
    have hrj : rest[j]? = some frj := by simpa using hj
    have htj' : truth'[j]? = some stj := by simpa using htj
    -- the next true state exists
    obtain ⟨σ1, hσ1⟩ : ∃ σ1, truth'[0]? = some σ1 := by
      have : 0 < truth'.length := by
        have := (List.getElem?_eq_some_iff.mp htj').1; omega
      exact ⟨truth'[0]'this, by simp⟩
    have hc0 : callerCtx (σ0 :: truth') top 0 = ⟨σ1.regs.get .sp, σ1.regs⟩ := by
      simp [callerCtx, hσ1]
    rw [hc0] at hrec
    obtain ⟨hf_cfa, hf_rules⟩ := hfirst fr R rfl hR
    have hrecst : Recovers R ⟨σ1.regs.get .sp, σ1.regs⟩ st :=
      recovers_of_reads_agree hrec hf_cfa (hf_rules (Nat.succ_pos _)).1 (hf_rules (Nat.succ_pos _)).2
    obtain ⟨hsp', hcs'⟩ := unwindRegs_agree hrecst
    have hag' : Agree (unwindRegs R st) σ1 := ⟨hsp', hcs'⟩
    have hmem' : (unwindRegs R st).mem = M := hmem
    have hstep : unwindFrom (fr :: rest) d st = unwindFrom rest (d + 1) (unwindRegs R st) := by
      simp [unwindFrom, hskip0, hR]
    have hctx : ∀ i, callerCtx truth' top i = callerCtx (σ0 :: truth') top (i + 1) := by
      intro i; simp [callerCtx]
    obtain ⟨st', hrun, hag'', hmem'', hcfa''⟩ :=
      ih rest truth' top (d + 1) (unwindRegs R st) σ1 M
        (fun i fr' st' hi hf ht => by
          rw [hctx]
          exact hchain (i + 1) fr' st' (by omega) (by simpa using hf) (by simpa using ht))
        (fun i fr' hi hf => htab (i + 1) fr' (by omega) (by simpa using hf))
        hσ1 hag' hmem'
        (fun fr1 R1 hf1 hR1 => by
          have hb := hbase 1 fr1 R1 Nat.one_pos (by omega) (by simpa using hf1) hR1
          refine ⟨?_, fun hj0 => ⟨fun r hr _ => hag'.2 r hr, fun r hr k hk => ?_⟩⟩
          · rcases hb with hb | hb
            · rw [hb]; exact hag'.1
            · exact hag'.2 _ hb
          · rw [hmem']
            exact hslots 1 fr1 σ1 R1 Nat.one_pos (by omega) (by simpa using hf1)
              (by simpa using hσ1) hR1 r hr k hk)
        (fun i fr' R' hi hij hf hR' =>
          hbase (i + 1) fr' R' (Nat.succ_pos _) (by omega) (by simpa using hf) hR')
        (fun i fr' σ R' hi hij hf ht hR' =>
          hslots (i + 1) fr' σ R' (Nat.succ_pos _) (by omega) (by simpa using hf)
            (by simpa using ht) hR')
        (fun i fr' hi hf => hskip (i + 1) fr' (by omega) (by simpa using hf))
        frj stj lp hrj htj' hcatch
    refine ⟨st', ?_, hag'', hmem'', fun R' hR' => by rw [hcfa'' R' hR', hctx]⟩
    rw [hstep, hrun]
    congr 1
    omega

/-- **Multi-frame composition.** Let the true states of frames `0, …, j`
(innermost first) form a call chain — frame `i`'s true state is reachable at its
`call` when its function is called from frame `i + 1`'s true state (or from
`top`) — let `st0` be frame `0`'s true state, and let the tables of frames
`0, …, j` be correct.  Suppose the toy personality routine (`frameAction`, an
early-exit scan of the call-site table) returns `skip` for frames `0, …, j-1`
and `handle lp` for frame `j`; the call-site rows of frames `1, …, j` use `sp`
or a callee-saved register as CFA base; and the throw-time memory `st0.mem`
still holds the save slots read by the call-site rows of frames `1, …, j-1`.
Then unwinding from `st0` stops at frame `j` with landing pad `lp`, in a state
that agrees with frame `j`'s true state on `sp` and the callee-saved registers
and whose memory is `st0.mem`; frame `j`'s program has a row at its call site,
and that row computes frame `j`'s true CFA and hence the frame base
`CFA - frameSize`. -/
theorem unwind_caught_at_first_handler_frame_with_caller_registers
    (frames : List Frame) (truth : List MState) (top : Caller) (st0 : MState)
    (j lp : Nat) (frj : Frame) (stj : MState)
    (hchain : ChainUpTo frames truth top j) (htab : TablesUpTo frames j)
    (h0 : truth[0]? = some st0) (hj : frames[j]? = some frj) (htj : truth[j]? = some stj)
    (hskip : SkippedBelow frames j) (hcatch : frameAction frj = .handle lp)
    (hbase : BaseSafeUpTo frames j) (hslots : SlotsPreservedBelow frames truth st0.mem j) :
    CaughtWithCallerState frames truth top st0 j lp frj stj := by
  obtain ⟨st, hrun, hag, hmem, hcfa⟩ :=
    unwindFrom_caught_of_chain j frames truth top 0 st0 st0 st0.mem hchain htab h0
      ⟨rfl, fun _ _ => rfl⟩ rfl (fun _ _ _ _ => ⟨rfl, fun _ => ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩⟩)
      hbase hslots hskip frj stj lp hj htj hcatch
  obtain ⟨R, hR, _⟩ :=
    atCallSite_recovers (hchain j frj stj (Nat.le_refl _) hj htj) (htab j frj (Nat.le_refl _) hj)
  refine ⟨st, R, by simpa [unwind] using hrun, hag, hmem, hR, hcfa R hR, ?_⟩
  simp only [frameBase, hcfa R hR]

/-- Under a sorted table with a unique entry value at the call PC, the
declarative skip condition yields `frameAction = skip` (via the sorted
early-exit scan lemma). -/
theorem frameAction_eq_skip_of_declarativeSkip {fr : Frame}
    (hwf : ∀ t, fr.lsda = some t → SortedByStart t ∧ UniqueAt t fr.callPC)
    (h : DeclarativeSkip fr) : frameAction fr = .skip := by
  rcases h with hnone | ⟨t, e, ht, he, hc, hlp⟩
  · simp [frameAction, hnone]
  · obtain ⟨hs, hu⟩ := hwf t ht
    have hscan := lookupScan_eq_result_of_sorted_uniqueAt hs hu he hc
    simp [frameAction, ht, hscan, CallSite.result, hlp]

/-- Under a sorted table with a unique entry value at the call PC, the
declarative catch condition yields `frameAction = handle lp`. -/
theorem frameAction_eq_handle_of_declarativeCatch {fr : Frame} {lp : Nat}
    (hwf : ∀ t, fr.lsda = some t → SortedByStart t ∧ UniqueAt t fr.callPC)
    (h : DeclarativeCatch fr lp) : frameAction fr = .handle lp := by
  obtain ⟨t, e, ht, he, hc, hlp⟩ := h
  obtain ⟨hs, hu⟩ := hwf t ht
  have hscan := lookupScan_eq_result_of_sorted_uniqueAt hs hu he hc
  simp [frameAction, ht, hscan, CallSite.result, hlp]

/-- **Multi-frame composition with declarative call-site tables.** As
`unwind_caught_at_first_handler_frame_with_caller_registers`, but with the
personality outcomes replaced by conditions on the tables themselves: the
call-site tables of frames `0, …, j` are sorted by start and have at most one
distinct entry value containing the call PC (`LsdaWellFormedUpTo`); each of
frames `0, …, j-1` has no table or an entry containing its call PC without a
landing pad (`DeclarativeSkippedBelow`); frame `j`'s table has an entry containing its
call PC with landing pad `lp` (`DeclarativeCatch`). -/
theorem unwind_caught_at_first_handler_frame_of_sorted_unique_lsda
    (frames : List Frame) (truth : List MState) (top : Caller) (st0 : MState)
    (j lp : Nat) (frj : Frame) (stj : MState)
    (hchain : ChainUpTo frames truth top j) (htab : TablesUpTo frames j)
    (hlsda : LsdaWellFormedUpTo frames j)
    (h0 : truth[0]? = some st0) (hj : frames[j]? = some frj) (htj : truth[j]? = some stj)
    (hskip : DeclarativeSkippedBelow frames j) (hcatch : DeclarativeCatch frj lp)
    (hbase : BaseSafeUpTo frames j) (hslots : SlotsPreservedBelow frames truth st0.mem j) :
    CaughtWithCallerState frames truth top st0 j lp frj stj :=
  unwind_caught_at_first_handler_frame_with_caller_registers frames truth top st0 j lp frj stj
    hchain htab h0 hj htj
    (fun i fr hi hf =>
      frameAction_eq_skip_of_declarativeSkip (hlsda i fr · (Nat.le_of_lt hi) hf) (hskip i fr hi hf))
    (frameAction_eq_handle_of_declarativeCatch (hlsda j frj · (Nat.le_refl _) hj) hcatch)
    hbase hslots

/-! ## Tightness of the frame lemma's agreement hypotheses -/

/-- Caller, true state and rows used below. -/
def flCaller : Caller := ⟨100, ⟨0, 5, 6, 0⟩⟩
def flSigma : MState := ⟨⟨100, 5, 6, 0⟩, fun _ => 0⟩
def flRowSaved : Row := ⟨.sp, 0, ⟨.same, .offset (-1), .same, .same⟩⟩
def flSigmaSaved : MState := ⟨⟨100, 0, 6, 0⟩, fun a => if a = 99 then 5 else 0⟩

theorem recovers_initRow_flSigma : Recovers initRow flCaller flSigma := by
  refine ⟨by decide, fun r hr => ?_⟩
  simp only [calleeSaved, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> decide

/-- Without agreement on the CFA base register the conclusion fails. -/
theorem recovers_of_reads_agree_fails_without_cfa :
    let st : MState := ⟨⟨101, 5, 6, 0⟩, fun _ => 0⟩
    Recovers initRow flCaller flSigma ∧ st.regs.get initRow.cfaReg ≠ flSigma.regs.get initRow.cfaReg ∧
      (∀ r ∈ calleeSaved, initRow.rules.get r = .same → st.regs.get r = flSigma.regs.get r) ∧
      (∀ r ∈ calleeSaved, ∀ k, initRow.rules.get r = .offset k →
        st.mem (cfaOf initRow flSigma + k) = flSigma.mem (cfaOf initRow flSigma + k)) ∧
      ¬ Recovers initRow flCaller st := by
  intro st
  refine ⟨recovers_initRow_flSigma, by decide, ?_, ?_, fun h => absurd h.1 (by decide)⟩
  · intro r hr _
    simp only [calleeSaved, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  · intro r _ k hk; simp [initRow] at hk

/-- Without agreement on a callee-saved register with rule `same` the conclusion fails. -/
theorem recovers_of_reads_agree_fails_without_same :
    let st : MState := ⟨⟨100, 9, 6, 0⟩, fun _ => 0⟩
    Recovers initRow flCaller flSigma ∧ st.regs.get initRow.cfaReg = flSigma.regs.get initRow.cfaReg ∧
      ¬ (∀ r ∈ calleeSaved, initRow.rules.get r = .same → st.regs.get r = flSigma.regs.get r) ∧
      (∀ r ∈ calleeSaved, ∀ k, initRow.rules.get r = .offset k →
        st.mem (cfaOf initRow flSigma + k) = flSigma.mem (cfaOf initRow flSigma + k)) ∧
      ¬ Recovers initRow flCaller st := by
  intro st
  refine ⟨recovers_initRow_flSigma, rfl, fun h => absurd (h .fp (by decide) rfl) (by decide), ?_,
    fun h => absurd (h.2 .fp (by decide)) (by decide)⟩
  intro r _ k hk; simp [initRow] at hk

/-- Without agreement on a read save slot the conclusion fails. -/
theorem recovers_of_reads_agree_fails_without_slot :
    let st : MState := ⟨flSigmaSaved.regs, fun _ => 0⟩
    Recovers flRowSaved flCaller flSigmaSaved ∧
      st.regs.get flRowSaved.cfaReg = flSigmaSaved.regs.get flRowSaved.cfaReg ∧
      (∀ r ∈ calleeSaved, flRowSaved.rules.get r = .same → st.regs.get r = flSigmaSaved.regs.get r) ∧
      ¬ (∀ r ∈ calleeSaved, ∀ k, flRowSaved.rules.get r = .offset k →
        st.mem (cfaOf flRowSaved flSigmaSaved + k) = flSigmaSaved.mem (cfaOf flRowSaved flSigmaSaved + k)) ∧
      ¬ Recovers flRowSaved flCaller st := by
  intro st
  refine ⟨⟨by decide, fun r hr => ?_⟩, rfl, fun _ _ _ => rfl,
    fun h => absurd (h .fp (by decide) (-1) rfl) (by decide),
    fun h => absurd (h.2 .fp (by decide)) (by decide)⟩
  simp only [calleeSaved, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> decide

/-- Tightness of `hrec` in the frame lemma: a row that does not recover the
caller from `σ` (its CFA rule `sp + 0` gives `99`, not `100`); every agreement
hypothesis holds trivially for `st = σ`, and the conclusion fails. -/
theorem recovers_of_reads_agree_fails_without_rec :
    let σ : MState := ⟨⟨99, 5, 6, 0⟩, fun _ => 0⟩
    ¬ Recovers initRow flCaller σ ∧ σ.regs.get initRow.cfaReg = σ.regs.get initRow.cfaReg ∧
      (∀ r ∈ calleeSaved, initRow.rules.get r = .same → σ.regs.get r = σ.regs.get r) ∧
      (∀ r ∈ calleeSaved, ∀ k, initRow.rules.get r = .offset k →
        σ.mem (cfaOf initRow σ + k) = σ.mem (cfaOf initRow σ + k)) ∧
      ¬ Recovers initRow flCaller σ := by
  intro σ
  have hn : ¬ Recovers initRow flCaller σ := fun h => absurd h.1 (by decide)
  exact ⟨hn, rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl, hn⟩

/-- Non-vacuity of the frame lemma: a state that differs from the true state in
the scratch register and in unread memory, but agrees on what the row reads. -/
theorem recovers_of_reads_agree_nonvacuity :
    let st : MState := ⟨⟨100, 0, 6, 77⟩, fun a => if a = 99 then 5 else 42⟩
    Recovers flRowSaved flCaller flSigmaSaved ∧
      st.regs.get flRowSaved.cfaReg = flSigmaSaved.regs.get flRowSaved.cfaReg ∧
      (∀ r ∈ calleeSaved, flRowSaved.rules.get r = .same → st.regs.get r = flSigmaSaved.regs.get r) ∧
      (∀ r ∈ calleeSaved, ∀ k, flRowSaved.rules.get r = .offset k →
        st.mem (cfaOf flRowSaved flSigmaSaved + k) = flSigmaSaved.mem (cfaOf flRowSaved flSigmaSaved + k)) ∧
      st ≠ flSigmaSaved := by
  intro st
  refine ⟨(recovers_of_reads_agree_fails_without_slot).1, rfl, ?_, ?_, fun h => ?_⟩
  · intro r hr _
    simp only [calleeSaved, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp [flRowSaved, RegFile.get] at *
    · rfl
  · intro r hr k hk
    simp only [calleeSaved, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [flRowSaved, RegFile.get, RegRule.offset.injEq] at hk
      subst hk; decide
    · simp [flRowSaved, RegFile.get] at hk
  · have := congrArg (fun s : MState => s.regs.get .t1) h
    revert this; decide

end Toy.CFI
