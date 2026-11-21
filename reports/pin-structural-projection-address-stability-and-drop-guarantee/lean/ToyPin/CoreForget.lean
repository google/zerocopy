import ToyPin.Necessity
import ToyPin.Leak

/-!
# The core discipline: tightness, non-vacuity and scope; `forget` versus memory reuse
-/

namespace Toy.Pin

open State

/-! ## Tightness of the hypotheses of the core theorem -/

/-- Pin a non-`Unpin` value, let it store its own address, then move it. -/
def coreMoveActs : List Act :=
  [.alloc [some false], .pinObj 0, .pinField (0, 0), .setSelf (0, 0), .moveOut (0, 0)]

/-- **`hmove` is tight** (witness: a one-object, one-field trace of 5 primitive actions from
`State.init`): the trace satisfies `hdrop`, and `AddrInv` fails along it. -/
theorem noPinnedMove_tight :
    Always DropGuaranteeAct State.init coreMoveActs ∧
      ¬ ∀ s ∈ states State.init coreMoveActs, AddrInv s := by decide

/-- Pin a non-`Unpin` value, let it store its address and link itself into the external list,
then reuse its memory without running its destructor. -/
def coreReuseActs : List Act :=
  [.alloc [some false], .pinObj 0, .pinField (0, 0), .setSelf (0, 0), .register (0, 0),
    .write (0, 0) false]

/-- **`hdrop` is tight** (witness: a one-object, one-field trace of 6 primitive actions from
`State.init`): the trace satisfies `hmove`, and `AddrInv` fails along it. -/
theorem dropGuarantee_tight :
    Always NoPinnedMove State.init coreReuseActs ∧
      ¬ ∀ s ∈ states State.init coreReuseActs, AddrInv s := by decide

/-- A trace exercising every kind of action while respecting both hypotheses: a pinned
non-`Unpin` value with a self-reference and a list entry; a pinned `Unpin` value that is
moved; an unpinned non-`Unpin` value that is moved and swapped; in-place drops, writes into
emptied locations, and deallocation. -/
def coreNonVacuousActs : List Act :=
  [.alloc [some false, some true, some false], .pinObj 0, .pinField (0, 0), .pinField (0, 1),
    .setSelf (0, 0), .register (0, 0), .setSelf (0, 2), .moveOut (0, 1), .dropTemp 1,
    .freeTemp, .write (0, 1) true, .alloc [some false], .swap (0, 2) (2, 0),
    .moveObj 2, .dropLeaf (0, 0), .write (0, 0) false, .dropLeaf (0, 0), .dropLeaf (0, 1),
    .dropLeaf (0, 2), .dealloc 0, .forget 3]

/-- **Non-vacuity of the core theorem.** Both hypotheses hold on `coreNonVacuousActs`, and
the self-reference and the list entry are actually established along the way. -/
theorem core_nonvacuous :
    Always NoPinnedMove State.init coreNonVacuousActs ∧
      Always DropGuaranteeAct State.init coreNonVacuousActs ∧
      (runActs State.init (coreNonVacuousActs.take 6)).registry ≠ [] ∧
      (runActs State.init (coreNonVacuousActs.take 6)).leafAt (0, 0) =
        some ⟨0, false, some (0, 0)⟩ := by decide

/-! ## The hypotheses are not necessary on individual traces or programs -/

/-- Moving a pinned non-`Unpin` value that never stored its address or linked itself breaks
no invariant: on this trace `hmove` fails, `hdrop` holds, and `AddrInv` holds throughout. -/
theorem noPinnedMove_not_necessary_on_a_trace :
    let acts : List Act := [.alloc [some false], .pinObj 0, .pinField (0, 0), .moveOut (0, 0)]
    ¬ Always NoPinnedMove State.init acts ∧ Always DropGuaranteeAct State.init acts ∧
      ∀ s ∈ states State.init acts, AddrInv s := by decide

/-- Overwriting a pinned non-`Unpin` value that set only a self-pointer (no list entry) breaks
no invariant: on this trace `hdrop` fails, `hmove` holds, and `AddrInv` holds throughout. -/
theorem dropGuaranteeAct_not_necessary_on_a_trace :
    let acts : List Act :=
      [.alloc [some false], .pinObj 0, .pinField (0, 0), .setSelf (0, 0), .write (0, 0) false]
    Always NoPinnedMove State.init acts ∧ ¬ Always DropGuaranteeAct State.init acts ∧
      ∀ s ∈ states State.init acts, AddrInv s := by decide

/-- A program not accepted by `SafeProgram` (pinning an object that does not exist) still
keeps `AddrInv`. -/
theorem safeProgram_not_necessary_for_a_program :
    ¬ SafeProgram dBase State.init [.pin 0] ∧
      ∀ s ∈ states State.init (compile dBase [.pin 0]), AddrInv s := by decide

/-! ## Scope of the core model: pinning an object alone protects nothing -/

/-- **`pinObj` is inert at the action level.** It changes no leaf, pinned location or list
entry, hence no `PinnedNonUnpin` fact; only `pinField` makes a location protected. (In safe
programs, `Op.projPin` requires the object to be pinned first.) -/
theorem pinObj_inert_in_core (st : State) (b : Nat) (l : Loc) :
    (applyAct st (.pinObj b)).leafAt l = st.leafAt l ∧
      (applyAct st (.pinObj b)).isPinnedLoc l = st.isPinnedLoc l ∧
      (applyAct st (.pinObj b)).registry = st.registry ∧
      (PinnedNonUnpin (applyAct st (.pinObj b)) l ↔ PinnedNonUnpin st l) := by
  have h1 : (applyAct st (.pinObj b)).leafAt l = st.leafAt l :=
    leafAt_modifyObj_of_fields (f := fun o => { o with pinned := true }) (fun _ => rfl) l
  have h2 : (applyAct st (.pinObj b)).isPinnedLoc l = st.isPinnedLoc l :=
    isPinnedLoc_modifyObj_of_pf (f := fun o => { o with pinned := true }) (fun _ => rfl) l
  refine ⟨h1, h2, rfl, ?_⟩
  unfold PinnedNonUnpin
  rw [h1, h2]

/-- A location pinned by `pinField` alone, on an object that was never pinned, is protected,
and pinning an object without projecting a field protects nothing. -/
theorem pinField_without_pinObj_protects :
    PinnedNonUnpin (runActs State.init [.alloc [some false], .pinField (0, 0)]) (0, 0) ∧
      (runActs State.init [.alloc [some false], .pinField (0, 0)]).isPinned 0 = false ∧
      ¬ PinnedNonUnpin (runActs State.init [.alloc [some false], .pinObj 0]) (0, 0) := by
  decide

/-! ## `forget` -/

/-- **Frame of `forget`.** It changes no leaf, pinned location, pinned flag, liveness or
list entry. -/
theorem forget_frame (st : State) (b : Nat) :
    (∀ l, (applyAct st (.forget b)).leafAt l = st.leafAt l) ∧
      (∀ l, (applyAct st (.forget b)).isPinnedLoc l = st.isPinnedLoc l) ∧
      (∀ c, (applyAct st (.forget b)).isPinned c = st.isPinned c) ∧
      (∀ c, (applyAct st (.forget b)).isLive c = st.isLive c) ∧
      (applyAct st (.forget b)).registry = st.registry := by
  refine ⟨fun l => leafAt_modifyObj_of_fields (f := fun o => { o with leaked := true })
      (fun _ => rfl) l,
    fun l => isPinnedLoc_modifyObj_of_pf (f := fun o => { o with leaked := true })
      (fun _ => rfl) l,
    fun c => isPinned_modifyObj_of_pinned (f := fun o => { o with leaked := true })
      (fun _ => rfl) c,
    fun c => ?_, rfl⟩
  show (st.modifyObj b fun o => { o with leaked := true }).isLive c = st.isLive c
  unfold State.isLive
  rw [modifyObj_heap]
  by_cases hbc : b = c
  · subst hbc; cases st.heap[b]? <;> simp
  · simp [hbc]

/-- `forget` preserves both invariants. -/
theorem forget_preserves_addrInv (st : State) (b : Nat) (h : AddrInv st) :
    AddrInv (applyAct st (.forget b)) := by
  have key := (forget_frame st b).1
  refine ⟨fun l v hv => ?_, fun e he => ?_⟩
  · rw [key] at hv; exact h.1 l v hv
  · rw [key]; exact h.2 e he

/-- **The hypothesis `h` of `forget_preserves_addrInv` is tight** (witness: the state reached
by the 5-action trace `coreMoveActs`): it violates `AddrInv`, and so does the state after
`forget`. -/
theorem forget_preserves_addrInv_h_tight :
    ¬ AddrInv (runActs State.init coreMoveActs) ∧
      ¬ AddrInv (applyAct (runActs State.init coreMoveActs) (.forget 0)) := by decide

/-- `forget` neither moves nor invalidates anything. -/
theorem forget_respects_contract (st : State) (b : Nat) :
    NoPinnedMove st (.forget b) ∧ DropGuaranteeAct st (.forget b) := ⟨trivial, trivial⟩

/-- Pin, self-reference, link, then leak with `forget`. -/
def leakProg : List Op := pinAndInit ++ [.link (0, 0), .forget 0]

/-- For the sound base declaration, the leaking program is safe and keeps both invariants,
and in the state it reaches `Op.drop 0` is not a safe operation. -/
theorem forget_keeps_addrInv_and_blocks_drop :
    SafeProgram dBase State.init leakProg ∧
      (∀ s ∈ states State.init (compile dBase leakProg), AddrInv s) ∧
      ¬ SafeOp dBase (runActs State.init (compile dBase leakProg)) (.drop 0) := by decide

/-- The state reached by `leakProg` on `dBase`. -/
def stLeaked : State := runActs State.init (compile dBase leakProg)

/-- **Non-vacuity of `leaked_object_never_dropped_or_deallocated`**: in `stLeaked`, object 0
is leaked, and a continuation that links the leaked value again, then creates, pins and drops
another object, is safe. -/
theorem leaked_object_nonvacuous :
    stLeaked.isLeaked 0 = true ∧
      SafeProgram dBase stLeaked [.link (0, 0), .new, .pin 1, .projPin 1 0, .drop 1] := by
  decide

/-- **The hypothesis `hleak` of `leaked_object_never_dropped_or_deallocated` is tight**
(witness: `dBase`, the state after `pinAndInit`, the one-operation continuation `drop 0`):
the object is not leaked, the continuation is safe, and the conclusion fails. -/
theorem leaked_object_hleak_tight :
    (runActs State.init (compile dBase pinAndInit)).isLeaked 0 = false ∧
      SafeProgram dBase (runActs State.init (compile dBase pinAndInit)) [.drop 0] ∧
      ¬ (Op.drop 0 ∉ [Op.drop 0] ∧
        ∀ s ∈ states (runActs State.init (compile dBase pinAndInit)) (compile dBase [.drop 0]),
          s.isLive 0 = (runActs State.init (compile dBase pinAndInit)).isLive 0 ∧
            s.isLeaked 0 = true) := by decide

/-- **The hypothesis `hsafe` of `leaked_object_never_dropped_or_deallocated` is tight**
(witness: `dBase`, `stLeaked`, the one-operation continuation `drop 0`): the object is
leaked, the continuation is not safe, and the conclusion fails (the object is deallocated). -/
theorem leaked_object_hsafe_tight :
    stLeaked.isLeaked 0 = true ∧ ¬ SafeProgram dBase stLeaked [.drop 0] ∧
      ¬ (Op.drop 0 ∉ [Op.drop 0] ∧
        ∀ s ∈ states stLeaked (compile dBase [.drop 0]),
          s.isLive 0 = stLeaked.isLive 0 ∧ s.isLeaked 0 = true) := by decide

/-- **Non-vacuity of `unmentioned_object_unchanged`**: object 0 exists in `stLeaked`, and a
safe 6-operation continuation that never mentions it (creating, pinning, self-referencing,
linking and dropping another object) exists. -/
theorem unmentioned_object_nonvacuous :
    0 < stLeaked.heap.length ∧
      (∀ op ∈ [Op.new, .pin 1, .projPin 1 0, .initSelf (1, 0), .link (1, 0), .drop 1],
        ¬ op.Mentions 0) ∧
      SafeProgram dBase stLeaked
        [.new, .pin 1, .projPin 1 0, .initSelf (1, 0), .link (1, 0), .drop 1] := by decide

/-- **The hypothesis `hb` of `unmentioned_object_unchanged` is tight** (witness:
`State.init`, `b = 0`, the continuation `[new]`): no object exists at 0, the continuation does
not mention 0, and the conclusion fails (an object appears at 0). -/
theorem unmentioned_object_hb_tight :
    ¬ (0 < State.init.heap.length) ∧ (∀ op ∈ [Op.new], ¬ op.Mentions 0) ∧
      ¬ ∀ s ∈ states State.init (compile dBase [.new]),
        s.heap[0]? = State.init.heap[0]? ∧
          ∀ e ∈ State.init.registry, e.1.1 = 0 → e ∈ s.registry := by decide

/-- **The hypothesis `hmention` of `unmentioned_object_unchanged` is tight** (witness:
`dBase`, `stLeaked`, the continuation `[assignField 0 0]`): object 0 exists, the continuation
mentions it, and the conclusion fails (the field's value changes). -/
theorem unmentioned_object_hmention_tight :
    0 < stLeaked.heap.length ∧ ¬ (∀ op ∈ [Op.assignField 0 0], ¬ op.Mentions 0) ∧
      ¬ ∀ s ∈ states stLeaked (compile dBase [.assignField 0 0]),
        s.heap[0]? = stLeaked.heap[0]? ∧
          ∀ e ∈ stLeaked.registry, e.1.1 = 0 → e ∈ s.registry := by decide

/-! ## Memory reuse without drop versus leaking -/

/-- **On `coreReuseActs`, reusing pinned memory without running the destructor breaks the
intrusive list, but not the self-reference.** On this 6-action trace nothing pinned is moved,
the drop guarantee is violated by the final write, the list invariant fails at the end, and
the self-reference invariant holds in every state (the self-referential value vanishes with
its memory). -/
theorem reuse_breaks_list_not_selfRef :
    Always NoPinnedMove State.init coreReuseActs ∧
      ¬ Always DropGuaranteeAct State.init coreReuseActs ∧
      ¬ ListOK (runActs State.init coreReuseActs) ∧
      ∀ s ∈ states State.init coreReuseActs, SelfRefOK s := by decide

/-- Positive control for `reuse_breaks_list_not_selfRef`: the same trace with `forget` in
place of the reusing write keeps both invariants. -/
theorem forget_instead_of_reuse_keeps_addrInv :
    let acts : List Act := [.alloc [some false], .pinObj 0, .pinField (0, 0), .setSelf (0, 0),
      .register (0, 0), .forget 0]
    Always NoPinnedMove State.init acts ∧ Always DropGuaranteeAct State.init acts ∧
      ∀ s ∈ states State.init acts, AddrInv s := by decide

end Toy.Pin
