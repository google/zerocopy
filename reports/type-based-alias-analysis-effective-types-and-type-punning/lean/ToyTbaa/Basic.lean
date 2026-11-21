/-!
# Toy model: typed and untyped byte memory (shared vocabulary)

This module fixes the toy vocabulary shared by both memory semantics:

* a small type universe (`u8`, `u16`, `u32`, `f32`, and a two-field struct `pair`), each type
  described by its per-byte *leaf* layout;
* straight-line programs over registers holding byte lists;
* deterministic execution with faults, observable traces, behaviours, and refinement.

Nothing here is specific to effective types; the two semantics live in
`ToyTbaa.Semantics`.
-/

namespace Toy.Tbaa

/-- Abstract byte values. Every natural number is a byte value; no bit width is modeled. -/
abbrev Byte := Nat

/-- A value is the list of bytes of its representation. -/
abbrev Val := List Byte

/-- Register names. -/
abbrev Reg := Nat

/-- Scalar leaf types. `u8` is the character (byte) type; `u16` is a 2-byte scalar type; `u32`
and `f32` are two distinct 4-byte scalar types. A memory byte that belongs to a `u32` object has
leaf `u32`. -/
inductive Scalar where
  | u8
  | u32
  | f32
  | u16
  deriving DecidableEq, Repr

/-- The access types of the toy language: the character type `u8`, two 4-byte scalar types
`u32` and `f32`, a 2-byte scalar type `u16`, and `pair`, a struct `{ fst : u32, snd : f32 }`
laid out without padding. (`u16` shares no leaf with `pair`, so results whose hypotheses
exclude shared leaves have struct instances.) -/
inductive Ty where
  | u8
  | u32
  | f32
  | pair
  | u16
  deriving DecidableEq, Repr

namespace Ty

/-- The per-byte leaf layout of a type: byte `i` of a `T` object belongs to a scalar of
type `T.leaves[i]`. A `pair` is four `u32` bytes followed by four `f32` bytes. -/
def leaves : Ty → List Scalar
  | .u8 => [.u8]
  | .u32 => [.u32, .u32, .u32, .u32]
  | .f32 => [.f32, .f32, .f32, .f32]
  | .pair => [.u32, .u32, .u32, .u32, .f32, .f32, .f32, .f32]
  | .u16 => [.u16, .u16]

/-- The size in bytes of a type (the length of its leaf layout). -/
def size (T : Ty) : Nat := T.leaves.length

/-- The leaf scalar at byte offset `i` (defaulting to `u8` past the end; never used there). -/
def leafAt (T : Ty) (i : Nat) : Scalar := T.leaves.getD i .u8

/-- Validity of a byte list as a value of type `T`: in this toy every byte list of the right
length is valid for every type. The toy has no uninitialized bytes, no pointer provenance and
no alignment requirement, so this is the analogue of Rust's rule for *initialized,
provenance-free* bytes of `u8`, `u16`, `u32`, `f32` and a padding-free struct of them read at
an aligned address; it does not model Rust's rejection of uninitialized or provenance-carrying
bytes, nor misaligned accesses. Types with invalid bit patterns are not modeled. -/
def Valid (T : Ty) (v : Val) : Prop := v.length = T.size

instance (T : Ty) (v : Val) : Decidable (T.Valid v) :=
  inferInstanceAs (Decidable (v.length = T.size))

end Ty

/-- Instructions of the straight-line toy language.

* `set r v` puts the constant byte list `v` in register `r`;
* `load r T p` reads `T.size` bytes at addresses `p, p+1, …` at type `T` into `r`;
* `store T p r` writes the bytes of register `r` at type `T` to `p, p+1, …`;
* `memcpy dst src n` copies `n` bytes from `src` to `dst` byte by byte, as if through a
  temporary buffer (so overlapping ranges are allowed);
* `out r` emits the contents of register `r` as an observable event. -/
inductive Instr where
  | set (r : Reg) (v : Val)
  | load (r : Reg) (T : Ty) (p : Nat)
  | store (T : Ty) (p : Nat) (r : Reg)
  | memcpy (dst src n : Nat)
  | out (r : Reg)
  deriving DecidableEq, Repr

/-- Whether an instruction is a load (used only to state a counterexample). -/
def Instr.isLoad : Instr → Bool
  | .load .. => true
  | _ => false

/-- Fault kinds. A `base` fault is one the untyped semantics also has (an unallocated byte
or an ill-sized value); a `type` fault is raised only by an effective-type check. -/
inductive Fault where
  | base
  | type
  deriving DecidableEq, Repr

/-- The result of one execution step over states `S`. -/
inductive Step (S : Type) where
  | next (s : S)
  | emit (v : Val) (s : S)
  | fault (k : Fault)

/-- The result of running a program prefix: a final state and trace, or a fault after a
trace. -/
inductive Final (S : Type) where
  | ok (s : S) (t : List Val)
  | fault (k : Fault) (t : List Val)

/-- Observable outcome of a whole run: normal termination with trace `t`, or undefined
behaviour after trace `t`. -/
inductive Outcome where
  | done (t : List Val)
  | ub (t : List Val)
  deriving DecidableEq, Repr

/-- Run a program from state `s`, accumulating the trace `t`. Execution is deterministic and
stops at the first fault. -/
def runFrom {S : Type} (step : Instr → S → Step S) : List Instr → S → List Val → Final S
  | [], s, t => .ok s t
  | i :: P, s, t =>
    match step i s with
    | .next s' => runFrom step P s' t
    | .emit v s' => runFrom step P s' (t ++ [v])
    | .fault k => .fault k t

/-- Forget the final state and fault kind. -/
def Final.outcome {S : Type} : Final S → Outcome
  | .ok _ t => .done t
  | .fault _ t => .ub t

/-- The outcome of running `P` from `s` with an empty initial trace. -/
def exec {S : Type} (step : Instr → S → Step S) (P : List Instr) (s : S) : Outcome :=
  (runFrom step P s []).outcome

/-- The trace of an outcome. -/
def Outcome.trace : Outcome → List Val
  | .done t => t
  | .ub t => t

/-- Whether an outcome is normal termination. -/
def Outcome.isDone : Outcome → Bool
  | .done _ => true
  | .ub _ => false

/-- `Allows o o'`: `o'` is a behaviour permitted by a run whose outcome is `o`. A terminating
run permits only itself; undefined behaviour after trace `t` permits every outcome whose
trace extends `t` (UB does not retract events already emitted). -/
def Allows : Outcome → Outcome → Prop
  | .done t, o' => o' = .done t
  | .ub t, o' => t <+: o'.trace

instance (o o' : Outcome) : Decidable (Allows o o') := by
  cases o <;> unfold Allows <;> infer_instance

/-- The behaviour set of program `P` from state `s` under semantics `step`. -/
def Beh {S : Type} (step : Instr → S → Step S) (P : List Instr) (s : S) : Outcome → Prop :=
  Allows (exec step P s)

/-- Refinement: every behaviour of the target is a behaviour of the source. -/
def Refines (tgt src : Outcome → Prop) : Prop := ∀ o, tgt o → src o

/-- Replacing block `src` by block `tgt` is sound under `step` from initial states satisfying
`Pre`: for every program prefix `pre`, suffix `post`, and initial state `s` with `Pre s`, the
behaviours of `pre ++ tgt ++ post` are behaviours of `pre ++ src ++ post`. -/
def ReorderSoundFrom {S : Type} (Pre : S → Prop) (step : Instr → S → Step S)
    (src tgt : List Instr) : Prop :=
  ∀ pre post s, Pre s → Refines (Beh step (pre ++ tgt ++ post) s) (Beh step (pre ++ src ++ post) s)

/-- Replacing block `src` by block `tgt` is sound under `step` in every context and from every
initial state. -/
def ReorderSound {S : Type} (step : Instr → S → Step S) (src tgt : List Instr) : Prop :=
  ReorderSoundFrom (fun _ => True) step src tgt

/-! ## Basic facts about behaviours (fully proved) -/

theorem Allows.trace_prefix {o o' : Outcome} (h : Allows o o') : o.trace <+: o'.trace := by
  cases o with
  | done t => simp only [Allows] at h; subst h; exact List.prefix_refl _
  | ub t => exact h

theorem Allows.refl (o : Outcome) : Allows o o := by
  cases o with
  | done t => rfl
  | ub t => exact List.prefix_refl _

theorem Allows.trans {a b c : Outcome} (hab : Allows a b) (hbc : Allows b c) : Allows a c := by
  cases a with
  | done t => simp only [Allows] at hab; subst hab; exact hbc
  | ub t => exact List.IsPrefix.trans hab hbc.trace_prefix

/-- Refinement between behaviour sets of deterministic runs reduces to one `Allows` check. -/
theorem refines_allows_iff (a b : Outcome) : Refines (Allows a) (Allows b) ↔ Allows b a :=
  ⟨fun h => h a (Allows.refl a), fun h _ ho => Allows.trans h ho⟩

theorem refines_beh_iff {S : Type} (step : Instr → S → Step S) (P Q : List Instr) (s : S) :
    Refines (Beh step P s) (Beh step Q s) ↔ Allows (exec step Q s) (exec step P s) :=
  refines_allows_iff _ _

/-- Soundness for all initial states implies soundness under any precondition. -/
theorem ReorderSound.from {S : Type} {step : Instr → S → Step S} {src tgt : List Instr}
    (h : ReorderSound step src tgt) (Pre : S → Prop) : ReorderSoundFrom Pre step src tgt :=
  fun pre post s _ => h pre post s trivial

/-- Every block can be replaced by itself (positive example of `ReorderSound`). -/
theorem reorderSound_refl {S : Type} (step : Instr → S → Step S) (B : List Instr) :
    ReorderSound step B B :=
  fun _ _ _ _ _ h => h

/-- A single context and initial state in which the source run does not allow the target run
refutes soundness of the replacement (used to prove counterexamples). -/
theorem not_reorderSoundFrom_of {S : Type} {Pre : S → Prop} {step : Instr → S → Step S}
    {src tgt : List Instr} (pre post : List Instr) (s : S) (hs : Pre s)
    (h : ¬ Allows (exec step (pre ++ src ++ post) s) (exec step (pre ++ tgt ++ post) s)) :
    ¬ ReorderSoundFrom Pre step src tgt :=
  fun H => h ((refines_beh_iff _ _ _ _).1 (H pre post s hs))

/-- Equal outcomes give equal behaviour sets. -/
theorem beh_eq_of_exec_eq {S T : Type} {step : Instr → S → Step S} {step' : Instr → T → Step T}
    {P P' : List Instr} {s : S} {s' : T} (h : exec step P s = exec step' P' s') :
    Beh step P s = Beh step' P' s' := by
  unfold Beh; rw [h]

end Toy.Tbaa
