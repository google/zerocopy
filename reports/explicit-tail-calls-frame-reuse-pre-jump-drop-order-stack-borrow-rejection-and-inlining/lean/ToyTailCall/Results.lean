import ToyTailCall.Machine
import ToyTailCall.Borrow
import ToyTailCall.Inline
import ToyTailCall.Layout
import ToyTailCall.Examples
import ToyTailCall.Lemmas
import ToyTailCall.CountUpProof
import ToyTailCall.MutualRecProof
import ToyTailCall.CallFreeProof
import ToyTailCall.EscapeProof
import ToyTailCall.SpliceMain

/-!
# Main results

These are statements about the toy model; they neither establish nor refute the
corresponding claims about any real compiler. Model–system relation: none proved.
-/

namespace Toy.TailCall

/-! ### Frame reuse versus pre-jump finalization -/

/-- In the unbounded-stack semantics, if no executed tail call of the `preJump` run passes a
pointer into the current frame, then `frameReuse` and `preJump` halt with the same outcomes
and event traces (in particular, one halts iff the other does). -/
theorem frameReuse_observes_iff_preJump_of_noStackBorrow (p : Prog) (hnb : NoStackBorrow p)
    (o : Outcome) (es : List Event) :
    Observes .frameReuse none p o es ↔ Observes .preJump none p o es :=
  ReuseProof.equiv hnb o es

/-- Under any stack bound `D`, if no executed tail call of the unbounded `preJump` run passes
a pointer into the current frame, every non-overflow outcome and trace of the bounded `preJump`
run is also produced by the bounded `frameReuse` run. -/
theorem frameReuse_observes_of_preJump_of_ne_stackOverflow_of_noStackBorrow (p : Prog)
    (hnb : NoStackBorrow p) (D : Option Nat) (o : Outcome) (es : List Event)
    (hso : o ≠ .stackOverflow) :
    Observes .preJump D p o es → Observes .frameReuse D p o es :=
  ReuseProof.transfer hnb D o es hso

/-! ### Exact depth and drop-order equations for self-tail-recursion -/

/-- `countUp N` under `frameReuse`: returns `0`, destructor events `drop 0, …, drop (N-1)`
(ascending, outermost frame first), maximum depth `2`, `N` tail-call jumps. -/
theorem countUp_frameReuse_runsTo (N : Nat) :
    RunsTo .frameReuse none (countUp N)
      ⟨.returned 0, (List.range N).map Event.drop, 2, N⟩ :=
  CountUpProof.frameReuse_runsTo N

/-- `countUp N` under `preJump`: the same outcome and events as `frameReuse`, but maximum
depth `N + 2`. -/
theorem countUp_preJump_runsTo (N : Nat) :
    RunsTo .preJump none (countUp N)
      ⟨.returned 0, (List.range N).map Event.drop, N + 2, N⟩ :=
  CountUpProof.preJump_runsTo N

/-- `countUp N` under `callReturn`: destructor events `drop (N-1), …, drop 0` (descending,
innermost frame first), maximum depth `N + 2`. -/
theorem countUp_callReturn_runsTo (N : Nat) :
    RunsTo .callReturn none (countUp N)
      ⟨.returned 0, ((List.range N).reverse).map Event.drop, N + 2, N⟩ :=
  CountUpProof.callReturn_runsTo N

/-! ### Depth equations for every call-free tail-call chain -/

/-- For a call-free program whose entry function exists and takes no parameters, every halted
unbounded `frameReuse` run has maximum depth `1`. -/
theorem callFree_frameReuse_maxDepth_of_entryOk (p : Prog) (hcf : CallFree p = true)
    (hentry : EntryOk p) (r : Result) (hr : RunsTo .frameReuse none p r) : r.maxDepth = 1 :=
  CallFreeProof.frameReuse_maxDepth p hcf hentry r hr

/-- For a call-free program whose entry function exists and takes no parameters, every halted
unbounded `preJump` run has maximum depth equal to the number of tail-call jumps plus one. -/
theorem callFree_preJump_maxDepth_of_entryOk (p : Prog) (hcf : CallFree p = true)
    (hentry : EntryOk p) (r : Result) (hr : RunsTo .preJump none p r) :
    r.maxDepth = r.tailCalls + 1 :=
  CallFreeProof.preJump_maxDepth p hcf hentry r hr

/-! ### Finalization order -/

/-- A slot is pending exactly when it is in range, owns a value, and has a destructor. -/
theorem mem_pendingDrops_iff (fn : Fn) (fr : Frame) (s : Slot) :
    s ∈ pendingDrops fn fr ↔ s < fr.vals.length ∧ fr.isLive s = true ∧ fn.dtor s ≠ .none := by
  simp [pendingDrops, List.mem_filter, List.mem_reverse, List.mem_range]

/-- Pending slots are listed in strictly decreasing slot order. -/
theorem pendingDrops_pairwise_gt (fn : Fn) (fr : Frame) :
    (pendingDrops fn fr).Pairwise (· > ·) := by
  unfold pendingDrops
  apply List.Pairwise.filter
  rw [List.pairwise_reverse]
  simpa using List.pairwise_lt_range (n := fr.vals.length)

/-! ### The static escape check -/

/-- Soundness of the escape check: if it accepts `p`, then `p` satisfies `NoStackBorrow`. -/
theorem noStackBorrow_of_escapeCheckAccepts (p : Prog) (hacc : EscapeCheckAccepts p = true) :
    NoStackBorrow p :=
  EscapeProof.noStackBorrow p hacc

/-! ### Inlining a function that contains tail calls -/

/-- The corrected splice at a `call` site preserves, for every stack bound `D` (including
`none`), every `frameReuse` outcome other than `ub` and `stackOverflow`, together with its
event trace. -/
theorem correctedCallSiteSplice_preserves_frameReuse_of_ne_ub_of_ne_stackOverflow (p : Prog)
    (ci k : Nat) (D : Option Nat) (o : Outcome) (es : List Event) (hub : o ≠ .ub)
    (hso : o ≠ .stackOverflow) :
    Observes .frameReuse D p o es →
      Observes .frameReuse D (inlineCallSite .corrected p ci k) o es := by
  exact SpliceProof.preserves p ci k D o es hub hso

/-- At the tail site of `mutualRec N`, the corrected splice (after the pre-jump desugaring)
turns constant depth `2` into depth `N + 2`, with the same outcome and (empty) trace. -/
theorem correctedTailSiteSplice_mutualRec_runsTo (N : Nat) :
    RunsTo .frameReuse none (mutualRec N) ⟨.returned 0, [], 2, 2 * N⟩ ∧
      RunsTo .frameReuse none (inlineTailSite .corrected (mutualRec N) 1 1)
        ⟨.returned 0, [], N + 2, 0⟩ :=
  ⟨MutualRecProof.orig_runsTo none rfl rfl N, MutualRecProof.inl_runsTo N⟩

/-- For every additive slack `C`, under stack bound `2 + C` the program `mutualRec (C + 1)`
(whose unbounded run has maximum depth `2`) returns `0`, while its corrected tail-site splice
overflows: no additive constant bounds the extra depth of the splice at tail sites. -/
theorem correctedTailSiteSplice_mutualRec_overflows_any_slack (C : Nat) :
    Observes .frameReuse (some (2 + C)) (mutualRec (C + 1)) (.returned 0) [] ∧
      Observes .frameReuse (some (2 + C)) (inlineTailSite .corrected (mutualRec (C + 1)) 1 1)
        .stackOverflow [] :=
  ⟨⟨_, MutualRecProof.orig_runsTo (some (2 + C)) (by simp [overflows])
      (by simp [overflows]; omega) (C + 1), rfl, rfl⟩,
    ⟨_, MutualRecProof.inl_overflow C, rfl, rfl⟩⟩

/-! ### Finalization, panics and unwinding under frame reuse -/

/-- A finalization that does not abort leaves no pending drop in the frame. -/
theorem dropList_clears_pending_of_ne_abort (fn : Fn) (fr : Frame)
    (hna : (dropList fn fr (pendingDrops fn fr) false).2.2 ≠ .abort) :
    pendingDrops fn (dropList fn fr (pendingDrops fn fr) false).1 = [] := by
  have ⟨hv, hpres, hmem⟩ := dropList_kills_mem fn fr (pendingDrops fn fr) false hna
  rw [List.eq_nil_iff_forall_not_mem]
  intro s hs
  rw [mem_pendingDrops_iff, hv] at hs
  have hlive_orig : fr.isLive s = true := by
    cases h0 : fr.isLive s
    · exfalso; have := hpres s h0; rw [this] at hs; cases hs.2.1
    · rfl
  have hin : s ∈ pendingDrops fn fr := (mem_pendingDrops_iff fn fr s).2 ⟨hs.1, hlive_orig, hs.2.2⟩
  rw [hmem s hin] at hs
  cases hs.2.1

/-- At a tail call under `frameReuse` (not unwinding, no pending return, arguments evaluated
without `ub`), if no pending destructor of the evaluated frame panics, the step emits one `drop`
per pending slot in `pendingDrops` order and then performs `push` of the callee on the frames
below the current one (the current frame is gone); if that push succeeds, the tail-call counter
is incremented (`bumpTail`). -/
theorem frameReuse_tailCall_finalizes_then_push_of_noPanic {p : Prog} {st : State} {fn : Fn}
    {fr : Frame} {rest : List Frame} {f : FnId} {args : List Operand} {vs : List Val}
    {fr1 : Frame} (D : Option Nat) (hat : AtTailCall p st fn fr rest f args vs fr1)
    (hnp : panickingPending fn fr1 = []) :
    step .frameReuse D p st =
      bumpTail (push D p { st with events := st.events ++ finalizationEvents fn fr1 } rest f vs) := by
  simp only [step, hat.stack_eq, hat.fn_eq, hat.not_unwinding, hat.no_pendingRet, hat.instr_eq,
    hat.args_eq, Bool.false_eq_true, ↓reduceIte, doTailCall]
  have ⟨he, hd⟩ := dropList_no_panics fn fr1 (pendingDrops fn fr1) false hnp
  simp [he, hd, finalizationEvents]

/-- At a tail call under `frameReuse` (not unwinding, no pending return, arguments evaluated
without `ub`), if exactly one pending destructor of the evaluated frame panics, the step still
emits one `drop` per pending slot, in `pendingDrops` order, removes the frame, and continues
unwinding with the frames below (the original caller's cleanup). -/
theorem frameReuse_finalization_unique_panic_drops_rest_then_unwinds {p : Prog} {st : State}
    {fn : Fn} {fr : Frame} {rest : List Frame} {f : FnId} {args : List Operand} {vs : List Val}
    {fr1 : Frame} (D : Option Nat) (hat : AtTailCall p st fn fr rest f args vs fr1)
    (hone : (panickingPending fn fr1).length = 1) :
    step .frameReuse D p st =
      unwindBelow { st with events := st.events ++ finalizationEvents fn fr1 } rest := by
  simp only [step, hat.stack_eq, hat.fn_eq, hat.not_unwinding, hat.no_pendingRet, hat.instr_eq,
    hat.args_eq, Bool.false_eq_true, ↓reduceIte, doTailCall]
  have ⟨he, hd⟩ := dropList_one_panic fn fr1 (pendingDrops fn fr1) hone
  simp [he, hd, finalizationEvents]

end Toy.TailCall

namespace Toy.TailCall.Layout

/-! ### Argument-area compatibility -/

/-- A callee area larger than the current one overwrites a cell below `b - inG`. -/
private theorem overwrite_of_lt {inG inH : Nat} (hgt : inG < inH) (δ : Int) :
    writeArgs (fun _ => 0) (δ - inH) (List.replicate inH 1) (δ - inH) = 1 := by
  cases inH with
  | zero => omega
  | succ k =>
    simp only [List.replicate_succ, writeArgs]
    rw [writeArgs_eq_of_lt _ _ _ _ (by omega)]
    simp

/-- At the fixed boundary `b` (no return-address relocation), under caller cleanup, frame
reuse is sound exactly when the callee's incoming area fits in the current function's. -/
theorem reuseSound_callerPops_iff (inG inH : Nat) :
    ReuseSound .callerPops inG inH ↔ inH ≤ inG := by
  constructor
  · intro h
    refine Nat.le_of_not_lt fun hgt => ?_
    have h1 := (h (fun _ => 0) 0 (List.replicate inH 1) (by simp)).1 (0 - inH) (by omega)
    simp only [reuseWrite] at h1
    rw [overwrite_of_lt hgt 0] at h1
    exact absurd h1 (by decide)
  · intro hle m b args hlen
    exact ⟨fun x hx => writeArgs_eq_of_lt m (b - inH) args x (by omega),
      readArgs_reuseWrite m b inH args hlen, rfl⟩

/-- At the fixed boundary `b` (no return-address relocation), under callee cleanup, frame
reuse is sound exactly when the two incoming areas are equal. -/
theorem reuseSound_calleePops_iff (inG inH : Nat) :
    ReuseSound .calleePops inG inH ↔ inH = inG := by
  constructor
  · intro h
    have hsp := (h (fun _ => 0) 0 (List.replicate inH 0) (by simp)).2.2
    simp [spAfterReturn] at hsp
    omega
  · intro heq
    subst heq
    intro m b args hlen
    exact ⟨fun x hx => writeArgs_eq_of_lt m (b - inH) args x (by omega),
      readArgs_reuseWrite m b inH args hlen, rfl⟩

/-- At the fixed boundary, equal signatures, hidden parameter included, make frame reuse sound
under either cleanup convention. -/
theorem reuseSound_of_sigCheckFull (g h : Sig) (hchk : sigCheckFull g h = true) (cl : Cleanup) :
    ReuseSound cl g.areaSize h.areaSize := by
  have heq : g = h := by simpa [sigCheckFull] using hchk
  subst heq
  cases cl
  · exact (reuseSound_callerPops_iff _ _).2 (Nat.le_refl _)
  · exact (reuseSound_calleePops_iff _ _).2 rfl

/-! ### Argument-area compatibility with return-address relocation -/

/-- The relocated model with `δ = 0` is the fixed-boundary model. -/
theorem reuseSoundAt_zero_iff (cl : Cleanup) (inG inH : Nat) :
    ReuseSoundAt cl 0 inG inH ↔ ReuseSound cl inG inH := by
  have hw : ∀ m b args, reuseWriteAt m b 0 inH args = reuseWrite m b inH args := by
    intro m b args; simp [reuseWriteAt, reuseWrite]
  have hs : ∀ b, spAfterReturnAt cl b 0 inG inH = spAfterReturn cl b inG inH := by
    intro b; cases cl <;> simp [spAfterReturnAt, spAfterReturn]
  constructor
  · intro h m b args hlen
    have ⟨h1, h2, h3⟩ := h m b args hlen
    refine ⟨fun x hx => by rw [← hw]; exact h1 x hx, ?_, by rw [← hs]; exact h3⟩
    rw [← hw]; simpa using h2
  · intro h m b args hlen
    have ⟨h1, h2, h3⟩ := h m b args hlen
    refine ⟨fun x hx => by rw [hw]; exact h1 x hx, ?_, by rw [hs]; exact h3⟩
    rw [hw]; simpa using h2

/-- Under callee cleanup, frame reuse with the boundary moved by `δ` cells is sound exactly when
`δ = inH - inG` (integer subtraction); in particular a suitable relocation exists for all
area sizes. -/
theorem reuseSoundAt_calleePops_iff (δ : Int) (inG inH : Nat) :
    ReuseSoundAt .calleePops δ inG inH ↔ δ = (inH : Int) - inG := by
  constructor
  · intro h
    have hsp := (h (fun _ => 0) 0 (List.replicate inH 0) (by simp)).2.2
    simp only [spAfterReturnAt] at hsp
    omega
  · intro hδ m b args hlen
    exact ⟨fun x hx => writeArgs_eq_of_lt m _ args x (by omega),
      readArgs_reuseWriteAt m b δ inH args hlen, by simp only [spAfterReturnAt]; omega⟩

/-- Under caller cleanup, frame reuse with the boundary moved by `δ` cells is sound exactly when
the boundary is not moved and the callee's area fits: relocation does not help. -/
theorem reuseSoundAt_callerPops_iff (δ : Int) (inG inH : Nat) :
    ReuseSoundAt .callerPops δ inG inH ↔ δ = 0 ∧ inH ≤ inG := by
  constructor
  · intro h
    have hsp := (h (fun _ => 0) 0 (List.replicate inH 1) (by simp)).2.2
    simp only [spAfterReturnAt] at hsp
    have hδ : δ = 0 := by omega
    refine ⟨hδ, Nat.le_of_not_lt fun hgt => ?_⟩
    subst hδ
    have h1 := (h (fun _ => 0) 0 (List.replicate inH 1) (by simp)).1 (0 + 0 - inH) (by omega)
    simp only [reuseWriteAt] at h1
    rw [overwrite_of_lt hgt (0 + 0)] at h1
    exact absurd h1 (by decide)
  · rintro ⟨hδ, hle⟩ m b args hlen
    subst hδ
    exact ⟨fun x hx => writeArgs_eq_of_lt m _ args x (by omega),
      readArgs_reuseWriteAt m b 0 inH args hlen, by simp only [spAfterReturnAt]; omega⟩

end Toy.TailCall.Layout
