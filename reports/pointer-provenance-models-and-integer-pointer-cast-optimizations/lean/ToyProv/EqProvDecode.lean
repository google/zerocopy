import ToyProv.Monotone
import ToyProv.IntEq

/-!
# Variant: decoding that requires identical provenance on both fragments (R7a)

A natural alternative byte decoder accepts two pointer fragments only if they carry the *same*
pointer, provenance included, and treats same-address fragments with different provenances as
UB. This module defines the semantics obtained by swapping in that decoder (everything except
`load` is the semantics of `ToyProv.Basic`) and shows, on concrete programs, that it breaks
provenance monotonicity at program level: the exposed model no longer refines the strict model,
folding `int2ptr k` into `p` is no longer a refinement in `strict`, the exposed-model fold of
R2b fails when there is no candidate, and both transfer principles of R6e fail. The same
programs are well behaved under the decoder of `ToyProv.Basic` (positive controls).

The variant semantics lives in namespace `Toy.Prov.EqProvDecode`; nothing else in the package
uses it.
-/

namespace Toy.Prov.EqProvDecode

open Toy.Prov

/-- Integer decoding that requires the two fragments to carry identical pointers. -/
def decodeIntEq : AByte → AByte → Option (Nat × List AllocId)
  | .intFrag n 0, .intFrag n' 1 => if n = n' then some (n, []) else none
  | .ptrFrag p 0, .ptrFrag p' 1 => if p = p' then some (p.addr, p.prov.toList) else none
  | _, _ => none

/-- Pointer decoding that requires the two fragments to carry identical pointers. -/
def decodePtrEq : AByte → AByte → Option (Ptr ⊕ Nat)
  | .ptrFrag p 0, .ptrFrag p' 1 => if p = p' then some (.inl p) else none
  | .intFrag n 0, .intFrag n' 1 => if n = n' then some (.inr n) else none
  | _, _ => none

/-- One step of the variant semantics: `load` uses `decodeIntEq` / `decodePtrEq`; every other
instruction steps exactly as in `Toy.Prov.step`. -/
def stepE (m : Model) (s : St) : Instr → List (Option St)
  | .load d ty p =>
    match s.regs p with
    | some (.ptr x) =>
      if canAccess m s x 2 then
        match ty with
        | .int =>
          match decodeIntEq (s.mem x.addr) (s.mem (x.addr + 1)) with
          | some (n, ps) => [some ((s.setReg d (.int n)).expose ps)]
          | none => [none]
        | .ptr =>
          match decodePtrEq (s.mem x.addr) (s.mem (x.addr + 1)) with
          | some (.inl q) => [some (s.setReg d (.ptr q))]
          | some (.inr n) => castToPtr m s d n
          | none => [none]
      else [none]
    | _ => [none]
  | i => step m s i

/-- The variant differs from the main semantics only on `load`. -/
theorem stepE_eq_step_of_not_load (m : Model) (s : St) (i : Instr)
    (h : ∀ d ty p, i ≠ .load d ty p) : stepE m s i = step m s i := by
  cases i with
  | load d ty p => exact absurd rfl (h d ty p)
  | _ => rfl

def execE (m : Model) : Prog → St → List (Option St)
  | [], s => [some s]
  | i :: is, s =>
    (stepE m s i).flatMap (fun o =>
      match o with
      | none => [none]
      | some s' => execE m is s')

def runsE (m : Model) (P : Prog) : List Outcome :=
  (execE m P init).map (fun o => match o with
    | none => .ub
    | some s => .done s.out)

def behE (m : Model) (P : Prog) : List Outcome :=
  let r := runsE m P
  if r.all (fun o => decide (o = .ub)) then [.ub] else r.filter (fun o => decide (o ≠ .ub))

def RefinesE (m : Model) (tgt src : Prog) : Prop :=
  Outcome.ub ∈ behE m src ∨ ∀ o ∈ behE m tgt, o ∈ behE m src

instance (m : Model) (tgt src : Prog) : Decidable (RefinesE m tgt src) := by
  unfold RefinesE; infer_instance

def SemRefinesE (m₁ m₂ : Model) (P : Prog) : Prop :=
  Outcome.ub ∈ behE m₂ P ∨ ∀ o ∈ behE m₁ P, o ∈ behE m₂ P

instance (m₁ m₂ : Model) (P : Prog) : Decidable (SemRefinesE m₁ m₂ P) := by
  unfold SemRefinesE; infer_instance

def AllAfterE (m : Model) (pre : Prog) (c : St → Bool) : Prop :=
  ∀ s ∈ (execE m pre init).filterMap id, c s = true

instance (m : Model) (pre : Prog) (c : St → Bool) : Decidable (AllAfterE m pre c) := by
  unfold AllAfterE; infer_instance

/-- The variant decoder is not monotone: adding provenance to one fragment turns a defined
decoding into UB (`AByteLE` is the order of `ToyProv.Monotone`). -/
theorem decodeEq_not_monotone :
    AByteLE (.ptrFrag ⟨none, 16⟩ 1) (.ptrFrag ⟨some 0, 16⟩ 1) ∧
      decodeIntEq (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨none, 16⟩ 1) = some (16, []) ∧
      decodeIntEq (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨some 0, 16⟩ 1) = none ∧
      decodePtrEq (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨none, 16⟩ 1) = some (.inl ⟨none, 16⟩) ∧
      decodePtrEq (.ptrFrag ⟨none, 16⟩ 0) (.ptrFrag ⟨some 0, 16⟩ 1) = none :=
  ⟨ex_AByteLE_pos, by decide, by decide, by decide, by decide⟩

/-! ### Program-level counterexamples -/

/-- A, B, C; `r := int2ptr 16` before A is exposed (no provenance in both models); then A is
exposed and `q := int2ptr 16` (no provenance in `strict`, A's in `exposed`); `r` is stored into
B and `q` into C; one byte of B is copied over C's first byte, and C is loaded at integer type. -/
def tornProg : Prog :=
  [.alloc 0 2, .alloc 1 2, .alloc 2 2, .const 3 16, .int2ptr 4 3,
   .ptr2int 5 0, .int2ptr 6 5, .store 1 4, .store 2 6, .memcpy 2 1 1,
   .load 7 .int 2, .obs 7]

/-- **R7a (ordering).** Under identical-provenance decoding the exposed model does not refine
the strict model: `tornProg` outputs `[16]` in `strict` and is UB in `exposed`. -/
theorem eqProvDecode_exposed_not_semRefines_strict :
    behE .strict tornProg = [.done [16]] ∧ behE .exposed tornProg = [.ub] ∧
      ¬ SemRefinesE .exposed .strict tornProg := by
  decide

/-- The programs of `int2ptrToCopy_refines_exposed_no_candidate_example` (R2b): A (unexposed),
B, C; `k := 16` (A's address); `q := int2ptr k` (no provenance) is stored into B; after the
rewrite point `d` is stored into C, B's first byte is copied over C's, and C is loaded at
integer type. -/
abbrev foldPre : Prog := r2bPreTorn
abbrev foldPost : Prog := r2bPostTorn

/-- **R7a (cast fold).** Under identical-provenance decoding, folding `d := int2ptr k` into
`d := p` with `k == (int)p` is not a refinement in `strict` (the source outputs `[16]`, the
target is UB), and the exposed-model fold of R2b fails in the case with no candidate (both of
R2b's side conditions hold). -/
theorem eqProvDecode_fold_not_refinement :
    AllAfterE .strict foldPre (intIsAddrOfC 3 0) ∧
      behE .strict (foldPre ++ .int2ptr 5 3 :: foldPost) = [.done [16]] ∧
      behE .strict (foldPre ++ .copy 5 0 :: foldPost) = [.ub] ∧
      ¬ RefinesE .strict (foldPre ++ .copy 5 0 :: foldPost) (foldPre ++ .int2ptr 5 3 :: foldPost) ∧
      AllAfterE .exposed foldPre (intIsAddrOfC 3 0) ∧ AllAfterE .exposed foldPre (candSubProvC 0) ∧
      ¬ RefinesE .exposed (foldPre ++ .copy 5 0 :: foldPost) (foldPre ++ .int2ptr 5 3 :: foldPost) := by
  decide

/-- **R7a (transfer principles).** Under identical-provenance decoding both R6e principles fail,
even with list-equal behaviour of the source (resp. target) in the two models. -/
theorem eqProvDecode_transfer_fails :
    (RefinesE .strict tornProg [.const 0 16, .obs 0] ∧
        behE .exposed [.const 0 16, .obs 0] = behE .strict [.const 0 16, .obs 0] ∧
        ¬ RefinesE .exposed tornProg [.const 0 16, .obs 0]) ∧
      (RefinesE .exposed [.const 0 99, .obs 0] tornProg ∧
        behE .strict [.const 0 99, .obs 0] = behE .exposed [.const 0 99, .obs 0] ∧
        ¬ RefinesE .strict [.const 0 99, .obs 0] tornProg) := by
  decide

/-- **R7a positive control.** Under the decoder of `ToyProv.Basic` (mixed provenance yields no
provenance) the same programs are well behaved: `tornProg` outputs `[16]` in both models, and
the fold is behaviour-preserving in `strict` and in `exposed`. -/
theorem mainDecode_same_programs_ok :
    beh .strict tornProg = [.done [16]] ∧ beh .exposed tornProg = [.done [16]] ∧
      SemRefines .exposed .strict tornProg ∧
      beh .strict (foldPre ++ .copy 5 0 :: foldPost) = [.done [16]] ∧
      beh .strict (foldPre ++ .int2ptr 5 3 :: foldPost) = [.done [16]] ∧
      beh .exposed (foldPre ++ .copy 5 0 :: foldPost) = [.done [16]] ∧
      beh .exposed (foldPre ++ .int2ptr 5 3 :: foldPost) = [.done [16]] := by
  decide

/-- The same programs with a pointer-typed final load. -/
def tornProgPtr : Prog :=
  [.alloc 0 2, .alloc 1 2, .alloc 2 2, .const 3 16, .int2ptr 4 3,
   .ptr2int 5 0, .int2ptr 6 5, .store 1 4, .store 2 6, .memcpy 2 1 1,
   .load 7 .ptr 2, .obs 7]
def foldPostPtr : Prog := [.store 2 5, .memcpy 2 1 1, .load 6 .ptr 2, .obs 6]

/-- **R7a, pointer-typed loads.** The failures also occur with a pointer-typed final load under
identical-provenance decoding, and disappear under the decoder of `ToyProv.Basic` (where the
reassembled pointer gets no provenance and only its address is observed). -/
theorem eqProvDecode_ptr_load_variants :
    behE .strict tornProgPtr = [.done [16]] ∧ behE .exposed tornProgPtr = [.ub] ∧
      behE .strict (foldPre ++ .int2ptr 5 3 :: foldPostPtr) = [.done [16]] ∧
      behE .strict (foldPre ++ .copy 5 0 :: foldPostPtr) = [.ub] ∧
      beh .strict tornProgPtr = [.done [16]] ∧ beh .exposed tornProgPtr = [.done [16]] ∧
      beh .strict (foldPre ++ .copy 5 0 :: foldPostPtr) = [.done [16]] ∧
      beh .exposed (foldPre ++ .copy 5 0 :: foldPostPtr) = [.done [16]] ∧
      beh .exposed (foldPre ++ .int2ptr 5 3 :: foldPostPtr) = [.done [16]] := by
  decide

end Toy.Prov.EqProvDecode
