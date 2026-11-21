import ToyPacked.Hyps

/-!
# Concrete instances used by examples, counterexamples and non-vacuity witnesses
-/

namespace Toy.Packed

/-- `u8`: alignment 1, no destructor. -/
def tU8 : TyInfo := ⟨1, true, .scalar⟩
/-- A value of alignment 4 with a destructor. -/
def tR4 : TyInfo := ⟨4, true, .res false⟩
/-- A value of alignment 4 whose destructor prints its own address. -/
def tR4obs : TyInfo := ⟨4, true, .res true⟩
/-- A value of alignment 2 with a destructor. -/
def tR2 : TyInfo := ⟨2, true, .res false⟩

/-- `packed { u8, R4 }` (ids 0, 1, 2), field 1 at offset 1. -/
def envA : Env := [tU8, tR4, ⟨1, true, .agg (some 1) [0, 1]⟩]
/-- Layout of `envA` (and of `envObs`, `envU`): field 1 of type 2 at offset 1. -/
def LA : Layout := fun t j => if t = 2 ∧ j = 1 then 1 else 0

/-- `packed { u8, R4obs }` with an address-observing destructor. -/
def envObs : Env := [tU8, tR4obs, ⟨1, true, .agg (some 1) [0, 1]⟩]

/-- `packed { u8, Tail }` with an unsized tail `Tail` (alignment 4, destructor). -/
def envU : Env := [tU8, ⟨4, false, .res false⟩, ⟨1, false, .agg (some 1) [0, 1]⟩]

/-- `packed { u8, Box<R4> }` (ids 0..3): box alignment 8, field 1 at offset 1. -/
def envB : Env := [tU8, tR4, ⟨8, true, .box 1⟩, ⟨1, true, .agg (some 1) [0, 2]⟩]
/-- Layout of `envB`. -/
def LB : Layout := fun t j => if t = 3 ∧ j = 1 then 1 else 0

/-- `S = { R4 }` (non-packed, id 2) nested in `Q = packed { u8, S }` (id 3). -/
def envQ : Env := [tU8, tR4, ⟨4, true, .agg none [1]⟩, ⟨1, true, .agg (some 1) [0, 2]⟩]
/-- Layout of `envQ`: field 1 of `Q` at offset 1. -/
def LQ : Layout := fun t j => if t = 3 ∧ j = 1 then 1 else 0

/-- `Pk = packed { u8, u8, R2 }` (id 2) inside `Outer = { R2, Pk }` (id 3, alignment 2). -/
def envOuter : Env := [tU8, tR2, ⟨1, true, .agg (some 1) [0, 0, 1]⟩, ⟨2, true, .agg none [1, 2]⟩]
/-- Layout of `envOuter`: `Pk` fields at 0, 1, 2; `Outer` fields at 0, 2. -/
def LOuter : Layout := fun t j =>
  if t = 2 ∧ j = 1 then 1 else if t = 2 ∧ j = 2 then 2 else if t = 3 ∧ j = 1 then 2 else 0

/-- `A8 = align(8) { u64 }` (id 2) inside `P2 = packed(2) { u8, A8 }` (id 3). -/
def envP2 : Env := [tU8, ⟨8, true, .scalar⟩, ⟨8, true, .agg none [1]⟩,
  ⟨2, true, .agg (some 2) [0, 2]⟩]
/-- Layout of `envP2`: field 1 of `P2` at offset 2. -/
def LP2 : Layout := fun t j => if t = 3 ∧ j = 1 then 2 else 0

/-- A non-power-of-two environment: `W = { U2 }` with `align W = 3`, `U2` of alignment 2 at
offset 2. -/
def envW : Env := [⟨2, true, .scalar⟩, ⟨3, true, .agg none [0]⟩]
/-- Layout of `envW`. -/
def LW : Layout := fun t j => if t = 1 ∧ j = 0 then 2 else 0

/-- `S = { R4 }` (id 1) with a layout that does not respect packing (offset 1). -/
def envRP : Env := [tR4, ⟨4, true, .agg none [0]⟩]
/-- Layout of `envRP`: field 0 of `S` at offset 1. -/
def LRP : Layout := fun t j => if t = 1 ∧ j = 0 then 1 else 0

/-- A cyclic environment: `C = packed { C }` with declared alignment 2. -/
def envCyc : Env := [⟨2, true, .agg (some 1) [0]⟩]

/-- An acyclic environment listed out of topological order: `packed { R4 }` (id 0) before `R4`
(id 1). -/
def envRev : Env := [⟨1, true, .agg (some 1) [1]⟩, tR4]

/-- `packed { u8, Box<R4obs> }` (ids 0..3): the box's pointee has an address-printing destructor. -/
def envBoxObs : Env := [tU8, tR4obs, ⟨8, true, .box 1⟩, ⟨1, true, .agg (some 1) [0, 2]⟩]

/-- A struct `S = { R4 }` (id 1) whose declared alignment 1 is below its field's alignment 4
(the toy does not require a struct's alignment to be at least its fields'). -/
def envUnder : Env := [tR4, ⟨1, true, .agg none [0]⟩]

/-- A single local `x : packed { u8, R4 }` at address 0, dropped in place at scope end. The
source body creates no reference. -/
def progInPlace : Prog := ⟨envA, LA, [2], [0], [.comp .dropGlue ⟨0, []⟩]⟩

/-- As `progInPlace` with the address-observing destructor. -/
def progObs : Prog := ⟨envObs, LA, [2], [0], [.comp .dropGlue ⟨0, []⟩]⟩

/-- As `progInPlace` with the unsized tail. -/
def progU : Prog := ⟨envU, LA, [2], [0], [.comp .dropGlue ⟨0, []⟩]⟩

/-- A local `x : R4` placed at the misaligned address 2. -/
def progMisFrame : Prog := ⟨[tR4], fun _ _ => 0, [0], [2], [.comp .dropGlue ⟨0, []⟩]⟩

/-- A local `y : R4` at the aligned address 8, dropped (an aligned place). -/
def progAligned : Prog := ⟨envA, LA, [1], [8], [.comp .dropGlue ⟨0, []⟩]⟩

/-- A local `y : R4obs` at the aligned address 8, dropped (an aligned place whose destructor
prints its address). -/
def progAlignedObs : Prog := ⟨envObs, LA, [1], [8], [.comp .dropGlue ⟨0, []⟩]⟩

/-- Drop of `x : packed { u8, Box<R4obs> }` at address 0. -/
def progBoxObs : Prog := ⟨envBoxObs, LB, [3], [0], [.comp .dropGlue ⟨0, []⟩]⟩

/-- Compiler drop of the field `s.0 : R4` of a local `s : S` in `envUnder` at address 1 (aligned
for `S`'s declared alignment 1): a one-step path. -/
def progUnder : Prog := ⟨envUnder, fun _ _ => 0, [1], [1], [.comp .dropGlue ⟨0, [0]⟩]⟩

/-- A local `x : packed { u8, Tail }` with the unsized tail of `envU`, never used (empty source
body). -/
def progEmptyU : Prog := ⟨envU, LA, [2], [0], []⟩

/-- Three locals over `envB`: `x : packed { u8, Box<R4> }` (local 0, address 0), `y : R4` (local 1,
address 8) and `z : packed { u8, Box<R4> }` (local 2, address 24). The source body drops `z`
(whose drop glue drops its box field at offset 1, a misalignable drop), then deref-moves out of
the box field of `x` into `y`, then frees the box through the box field of `x`, then drops `y`.
The toy does not track ownership: `moveOut` is a no-op marker, and the program states which
operations follow it. -/
def progBox : Prog := ⟨envB, LB, [3, 1, 3], [0, 8, 24],
  [.comp .dropGlue ⟨2, []⟩, .moveOut ⟨0, [1]⟩, .comp .boxFree ⟨0, [1]⟩, .comp .dropGlue ⟨1, []⟩]⟩

/-- `progBox` without its `moveOut` marker. -/
def progBoxNoMove : Prog := ⟨envB, LB, [3, 1, 3], [0, 8, 24],
  [.comp .dropGlue ⟨2, []⟩, .comp .boxFree ⟨0, [1]⟩, .comp .dropGlue ⟨1, []⟩]⟩

/-- Compiler drop of the nested place `x.1.0` of `x : Q = packed { u8, S }`. -/
def progNested : Prog := ⟨envQ, LQ, [3], [0], [.comp .dropGlue ⟨0, [1, 0]⟩]⟩

/-- Compiler drop of the whole value `x : Q = packed { u8, S }`. -/
def progWholeQ : Prog := ⟨envQ, LQ, [3], [0], [.comp .dropGlue ⟨0, []⟩]⟩

/-- Unsafe client: passes the raw pointer with address 1, which is the address of `x.1` (as
`&raw mut x.1` would produce; the toy passes the literal address), to the drop glue of `R4`. -/
def progClient : Prog := ⟨envA, LA, [2], [0], [.rawCall .dropGlue 1 1]⟩

/-- Two locals `w, x : packed { u8, R4 }` (local 0 at address 0, local 1 at address 8). The source
body drops `w` (whose drop glue drops its field `R4` at offset 1, a misalignable drop), then
unsafe client code passes the raw pointer with address 9, which is the address of `x.1` (as
`&raw mut x.1` would produce; the toy passes the literal address), to the drop glue of `R4`. The
toy does not track ownership: the program states which operations happen (the compiler does not
drop `x` in this program). -/
def progEscape : Prog := ⟨envA, LA, [2, 2], [0, 8],
  [.comp .dropGlue ⟨0, []⟩, .rawCall .dropGlue 1 9]⟩

/-- Two locals `w, x : packed { u8, R4 }` (local 0 at address 0, local 1 at address 8). The source
body drops `w` (a misalignable drop of its field `R4` inside its drop glue), then makes a
user-written `&*ptr` for `R4` at the misaligned address 9 (the address of `x.1`). -/
def progUserRef : Prog := ⟨envA, LA, [2, 2], [0, 8], [.comp .dropGlue ⟨0, []⟩, .rawRef 1 9]⟩

/-- A mixed program: scope-end drop of `x`, an aligned client call, and a misaligned user
reference (last, so that every operation executes). -/
def progMixed : Prog := ⟨envA, LA, [2], [0],
  [.comp .dropGlue ⟨0, []⟩, .rawCall .dropGlue 1 4, .rawRef 1 1]⟩

/-- No checks. -/
def instrNone : BodyId → Nat → Bool := fun _ _ => false
/-- Checks everywhere. -/
def instrAll : BodyId → Nat → Bool := fun _ _ => true
/-- Checks at every source position, none in any shim. -/
def instrSrc : BodyId → Nat → Bool := fun b _ => decide (b = .src)

/-- Original program: no staging, no checks. -/
def cfgNone : Cfg := ⟨critNone, fun _ _ => 16, instrNone⟩
/-- Type-based staging into temporaries at address 16. -/
def cfgType (env : Env) : Cfg := ⟨critType env, fun _ _ => 16, instrNone⟩

end Toy.Packed
