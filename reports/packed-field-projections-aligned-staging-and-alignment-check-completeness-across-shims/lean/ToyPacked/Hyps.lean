import ToyPacked.Semantics

/-!
# Staging criteria, staging positions, and the hypotheses of the main results
-/

namespace Toy.Packed

/-- Exact misalignability for a fixed layout: a place at offset `o` from a base aligned to `A`
can be misaligned for alignment `n` iff `n` does not divide `gcd A o`. Holds for all naturals
(including `A = 0`, `n = 0`, `o = 0`). -/
theorem misalignable_iff_not_dvd_gcd (A n o : Nat) :
    Misalignable A n o ↔ ¬ n ∣ Nat.gcd A o := by
  rw [Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨a, hA, hn⟩ ⟨h1, h2⟩
    exact hn (Nat.dvd_add (Nat.dvd_trans h1 hA) h2)
  · intro h
    by_cases ho : n ∣ o
    · refine ⟨A, Nat.dvd_refl A, fun hAo => h ⟨?_, ho⟩⟩
      exact (Nat.dvd_add_right ho).mp (by rwa [Nat.add_comm] at hAo)
    · exact ⟨0, Nat.dvd_zero A, by simpa using ho⟩

instance (A n o : Nat) : Decidable (Misalignable A n o) :=
  decidable_of_iff _ (misalignable_iff_not_dvd_gcd A n o).symm

/-- Never stage. -/
def critNone : Crit := fun _ _ _ _ => false

/-- Always stage (over-staging). -/
def critAll : Crit := fun _ _ _ _ => true

/-- Offset-aware criterion for a fixed layout: stage iff the place's type alignment does not
divide `gcd A o`, where `o` is the total offset along the whole path. -/
def critExact (env : Env) (L : Layout) : Crit := fun _ A t0 path =>
  match resolve env L t0 path with
  | some (u, o) => !decide (env.align u ∣ Nat.gcd A o)
  | none => false

/-- Type-based criterion: stage iff the place's type alignment does not divide its type-based
guaranteed alignment `typeGA` (computed along the whole path from the base alignment). -/
def critType (env : Env) : Crit := fun _ A t0 path =>
  match typeAt env t0 path with
  | some u => !decide (env.align u ∣ typeGA env t0 path A)
  | none => false

/-- Leaf-only criterion: stage iff the immediate parent of the place is `packed(n)`, the place is
a field `f` of it, and the alignment of `f` does not divide `n`. It ignores the base alignment and
every ancestor other than the immediate parent. -/
def critLeaf (env : Env) : Crit := fun _ _ t0 path =>
  match path.getLast?, typeAt env t0 path.dropLast with
  | some j, some par =>
    match (env.ty par).kind, env.field? par j with
    | .agg (some n) _, some f => !decide (env.align f ∣ n)
    | _, _ => false
  | _, _ => false

/-- Restrict a criterion to drops: frees and clones are never staged ("stage the moved-out
value, not the pointer field"). -/
def dropsOnly (c : Crit) : Crit := fun k A t0 path => decide (k = .dropGlue) && c k A t0 path

/-- The unstaged version of a configuration (the original program). -/
def Cfg.unstaged (cfg : Cfg) : Cfg := { cfg with crit := critNone }

/-- A compiler-operation position: body, op index, kind, base alignment, base type, path, type
of the operated place, and its offset from the base. -/
structure Pos where
  b : BodyId
  i : Nat
  k : ShimKind
  A : Nat
  t0 : Nat
  path : List Nat
  u : Nat
  o : Nat
  deriving DecidableEq, Repr

/-- Positions of compiler operations in the source body (operations that call no shim and
ill-formed places are not operations). -/
def srcPositions (P : Prog) : List Pos :=
  P.src.zipIdx.filterMap fun q =>
    match q.1 with
    | .comp k p =>
      if p.root < P.locals.length then
        match resolve P.env P.layout (P.locals.getD p.root 0) p.path with
        | some (u, o) =>
          if callsShim P.env P.fuel k u then
            some ⟨.src, q.2, k, P.env.align (P.locals.getD p.root 0),
              P.locals.getD p.root 0, p.path, u, o⟩
          else none
        | none => none
      else none
    | _ => none

/-- The shims a run may enter from shim `k` of type `t` with nesting fuel `fuel`: the shim itself,
the drop glue of a box's pointee (if it has drop glue), and the field drops (fields with drop glue)
or field clones of an aggregate, recursively. -/
def reach (env : Env) : Nat → ShimKind → Nat → List (ShimKind × Nat)
  | 0, _, _ => []
  | fuel + 1, k, t => (k, t) ::
    match k, (env.ty t).kind with
    | .dropGlue, .box p => if needsDrop env fuel p then reach env fuel .dropGlue p else []
    | .dropGlue, .agg _ fs =>
      fs.flatMap fun f => if needsDrop env fuel f then reach env fuel .dropGlue f else []
    | .clone, .agg _ fs => fs.flatMap fun f => reach env fuel .clone f
    | _, _ => []

/-- The shim called directly by a source operation, if any: by a compiler operation that calls a
shim, or by a raw client call of an existing shim (`shimExists`; a raw call of a shim that does
not exist is a no-op and enters no shim). -/
def Op.shimRoot (P : Prog) : Op → Option (ShimKind × Nat)
  | .comp k p =>
    match P.place p with
    | some (_, _, u, _) => if callsShim P.env P.fuel k u then some (k, u) else none
    | none => none
  | .rawCall k t _ => if shimExists P.env k t then some (k, t) else none
  | _ => none

/-- The shims a run of `P` may enter (with repetitions). -/
def reachableShims (P : Prog) : List (ShimKind × Nat) :=
  (P.src.filterMap (Op.shimRoot P)).flatMap fun r => reach P.env P.fuel r.1 r.2

/-- Positions of compiler operations in the body of shim `k` for type `t`: field drops (fields
with drop glue) in drop glue, and field clones in clone shims; a box-free shim has none. The
shim's incoming pointer is taken to be aligned for its type, so the base alignment is
`env.align t`. -/
def bodyPositions (env : Env) (L : Layout) (fuel : Nat) (k : ShimKind) (t : Nat) : List Pos :=
  match k with
  | .boxFree => []
  | _ =>
    (env.fields t).zipIdx.filterMap fun q =>
      if callsShim env fuel k q.1 then
        some ⟨.shim k t, q.2 + 1, k, env.align t, t, [q.2], q.1, L t q.2⟩
      else none

/-- Positions of compiler operations in the shims a run of `P` may enter (`reachableShims`). -/
def shimPositions (P : Prog) : List Pos :=
  (reachableShims P).flatMap fun r => bodyPositions P.env P.layout P.fuel r.1 r.2

/-- All compiler-operation positions of a program: those of its source body and those of the
shims it may enter. -/
def positions (P : Prog) : List Pos := srcPositions P ++ shimPositions P

/-- Does the configuration stage position `q`? -/
def Pos.staged (cfg : Cfg) (q : Pos) : Bool := cfg.crit q.k q.A q.t0 q.path

/-- Every compiler-operation position whose place is misalignable is staged ("every
reference-taking compiler operation on a may-be-disaligned place is staged"). -/
def CritCovers (P : Prog) (cfg : Cfg) : Prop :=
  ∀ q, q ∈ positions P → Misalignable q.A (P.env.align q.u) q.o → q.staged cfg = true

instance (P : Prog) (cfg : Cfg) : Decidable (CritCovers P cfg) := by
  unfold CritCovers; infer_instance

/-- (H1) Every staged value is of a sized type. -/
def StagedSized (P : Prog) (cfg : Cfg) : Prop :=
  ∀ q, q ∈ positions P → q.staged cfg = true → (P.env.ty q.u).sized = true

instance (P : Prog) (cfg : Cfg) : Decidable (StagedSized P cfg) := by
  unfold StagedSized; infer_instance

/-- (H2) No destructor reachable from a staged drop through inline sub-values (`AddrBlind`)
observes its own address. -/
def StagedAddrBlind (P : Prog) (cfg : Cfg) : Prop :=
  ∀ q, q ∈ positions P → q.staged cfg = true → q.k = .dropGlue → AddrBlind P.env P.fuel q.u = true

instance (P : Prog) (cfg : Cfg) : Decidable (StagedAddrBlind P cfg) := by
  unfold StagedAddrBlind; infer_instance

/-- (H3) Every staging temporary is allocated at an address aligned for the staged type. -/
def TempsAligned (P : Prog) (cfg : Cfg) : Prop :=
  ∀ q, q ∈ positions P → q.staged cfg = true → P.env.align q.u ∣ cfg.tmp q.b q.i

instance (P : Prog) (cfg : Cfg) : Decidable (TempsAligned P cfg) := by
  unfold TempsAligned; infer_instance

/-- Every local is placed at an address aligned for its type. -/
def FrameAligned (P : Prog) : Prop :=
  ∀ x, x < P.locals.length → P.env.align (P.locals.getD x 0) ∣ P.frame.getD x 0

instance (P : Prog) : Decidable (FrameAligned P) := by unfold FrameAligned; infer_instance

/-- Is this a safe source operation (no raw-pointer reference creation, no raw shim call)? -/
def Op.isSafe : Op → Bool
  | .comp _ _ => true
  | .moveOut _ => true
  | .readUnaligned _ _ => true
  | .rawRef _ _ => false
  | .rawCall _ _ _ => false

/-- The source body contains no unsafe raw-pointer operations. -/
def SafeSrc (P : Prog) : Prop := ∀ op, op ∈ P.src → op.isSafe = true

instance (P : Prog) : Decidable (SafeSrc P) := by unfold SafeSrc; infer_instance

/-- Does this operation pass an aligned pointer if it is a raw call of an existing shim? A raw call
of a shim that does not exist (`shimExists`) is a no-op and passes no pointer to any shim. -/
def Op.ptrAligned (env : Env) : Op → Bool
  | .rawCall k t a => !shimExists env k t || decide (env.align t ∣ a)
  | _ => true

/-- Every raw pointer that unsafe client code passes to an existing shim is aligned for the shim's
type. -/
def ClientPtrsAligned (P : Prog) : Prop := ∀ op, op ∈ P.src → op.ptrAligned P.env = true

instance (P : Prog) : Decidable (ClientPtrsAligned P) := by
  unfold ClientPtrsAligned; infer_instance

/-- Is this a user-written raw-pointer reference creation? -/
def Op.isRawRef : Op → Bool
  | .rawRef _ _ => true
  | _ => false

/-- Every user-written reference creation in the source body is instrumented. -/
def SrcRefsInstrumented (P : Prog) (cfg : Cfg) : Prop :=
  ∀ q, q ∈ P.src.zipIdx → q.1.isRawRef = true → cfg.instr .src q.2 = true

instance (P : Prog) (cfg : Cfg) : Decidable (SrcRefsInstrumented P cfg) := by
  unfold SrcRefsInstrumented; infer_instance

/-- The policy covers every reference creation that can be misaligned: op `0` of every existing
shim (`shimExists`) of every type of the environment whose alignment is not `1`, and, if the
environment has a type whose alignment is not `1`, every source position (a user reference
creation can occur at any source position). Reference creations requiring alignment `1` can
never be misaligned. -/
def AlignRelevantCovered (env : Env) (I : BodyId → Nat → Bool) : Prop :=
  (∀ k t, t < env.length → env.align t ≠ 1 → shimExists env k t = true →
    I (.shim k t) 0 = true) ∧
  ((∃ t, t < env.length ∧ env.align t ≠ 1) → ∀ i, I .src i = true)

/-- Relabel a UB event as a trap where the policy has a check. -/
def toTrap (I : BodyId → Nat → Bool) : Ev → Ev
  | .ub b i => if I b i then .trap b i else .ub b i
  | e => e

end Toy.Packed
