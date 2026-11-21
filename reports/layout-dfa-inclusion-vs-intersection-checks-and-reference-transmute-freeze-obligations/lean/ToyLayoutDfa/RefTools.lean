import ToyLayoutDfa.Refs
import ToyLayoutDfa.Fixtures
import ToyLayoutDfa.Tools

/-!
# Proof tools and fixtures for the reference model

`sound_of_invariant` reduces `Sound` to an invariant on the region's contents; it is a
fully proved helper, not a result of the package. The fixtures are the referent types
used by the examples and counterexamples.
-/

namespace Toy.LayoutDfa

instance instDecidableOfLayoutValid (A : Layout) (fz : Bool) (w : List Sym) :
    Decidable ((RefTy.ofLayout A fz).valid w) :=
  inferInstanceAs (Decidable (A.Lang w))

theorem runOK_of_invariant {ms md : Mode} {S D : RefTy} (I : List Sym → Prop)
    (hop : ∀ m op, I m → Permitted ms md S D op → OpOK ms md S D m op ∧ I (op.next m))
    (hfin : ∀ m, I m → S.valid m) :
    ∀ (ops : List Op) (m : List Sym), I m → (∀ op ∈ ops, Permitted ms md S D op) →
      RunOK ms md S D m ops
  | [], m, hm, _ => hfin m hm
  | op :: ops, m, hm, hp => by
    have h1 := hop m op hm (hp op (List.mem_cons_self ..))
    exact ⟨h1.1, runOK_of_invariant I hop hfin ops (op.next m) h1.2
      (fun o ho => hp o (List.mem_cons_of_mem _ ho))⟩

/-- Soundness from an invariant `I` on the contents: `I` holds initially, is preserved by
every permitted operation whose assertions it implies, and implies `S`-validity. -/
theorem sound_of_invariant {ms md : Mode} {S D : RefTy} (I : List Sym → Prop)
    (h0 : ∀ m, S.valid m → I m)
    (hop : ∀ m op, I m → Permitted ms md S D op → OpOK ms md S D m op ∧ I (op.next m))
    (hfin : ∀ m, I m → S.valid m) : Sound ms md S D :=
  fun m hm ops hp => runOK_of_invariant I hop hfin ops m (h0 m hm) hp

/-- The one-operation form of `Sound`: from every `S`-valid contents, every single permitted
operation satisfies its assertions and leaves `S`-valid contents. -/
def SoundOneStep (ms md : Mode) (S D : RefTy) : Prop :=
  ∀ m, S.valid m → ∀ op, Permitted ms md S D op → OpOK ms md S D m op ∧ S.valid (op.next m)

/-- `Sound` is equivalent to its one-operation form: runs of several operations add nothing
in this model, because a write replaces the whole region. -/
theorem sound_iff_soundOneStep {ms md : Mode} {S D : RefTy} :
    Sound ms md S D ↔ SoundOneStep ms md S D :=
  ⟨fun h m hm op hp => h m hm [op] (by simp [hp]),
   fun h => sound_of_invariant S.valid (fun _ hm => hm) (fun m op hm hp => h m hm op hp)
     (fun _ hm => hm)⟩

/-- Sufficient condition for the `& → &` cell (no satisfiability assumption). -/
theorem sound_shared_shared_of {S D : RefTy} (hinc : Includes S D) (hfz : S.freeze = D.freeze)
    (hrev : D.freeze = false → Includes D S) : Sound .shared .shared S D := by
  rw [sound_iff_soundOneStep]
  intro m hm op hp
  cases op with
  | read v =>
    cases v
    · exact ⟨⟨hm, by decide⟩, hm⟩
    · exact ⟨⟨hinc m hm, by decide⟩, hm⟩
  | write v b =>
    cases v
    · obtain ⟨_, hsf, hb⟩ := hp
      have hdf : D.freeze = false := by rw [← hfz]; exact hsf
      exact ⟨⟨by simp [FrozenDuring, hsf, hdf], by decide⟩, hb⟩
    · obtain ⟨hmd, hb⟩ := hp
      have hdf : D.freeze = false := by
        rcases hmd with h | h
        · cases h
        · exact h
      have hsf : S.freeze = false := by rw [hfz]; exact hdf
      exact ⟨⟨by simp [FrozenDuring, hsf, hdf], by decide⟩, hrev hdf b hb⟩

/-- Sufficient condition for the `&mut → &` cell (no satisfiability assumption). -/
theorem sound_mutable_shared_of {S D : RefTy} (hinc : Includes S D)
    (hrev : D.freeze = false → Includes D S) : Sound .mutable .shared S D := by
  rw [sound_iff_soundOneStep]
  intro m hm op hp
  cases op with
  | read v =>
    cases v
    · exact absurd (show Mode.mutable = Mode.shared from hp) (by decide)
    · exact ⟨⟨hinc m hm, by decide⟩, hm⟩
  | write v b =>
    cases v
    · exact absurd hp.1 (by decide)
    · obtain ⟨hmd, hb⟩ := hp
      have hdf : D.freeze = false := by
        rcases hmd with h | h
        · cases h
        · exact h
      exact ⟨⟨by simp [FrozenDuring, hdf], by decide⟩, hrev hdf b hb⟩

/-- Sufficient condition for the `&mut → &mut` cell (no satisfiability assumption). -/
theorem sound_mutable_mutable_of {S D : RefTy} (hinc : Includes S D) (hrev : Includes D S) :
    Sound .mutable .mutable S D := by
  rw [sound_iff_soundOneStep]
  intro m hm op hp
  cases op with
  | read v =>
    cases v
    · exact absurd (show Mode.mutable = Mode.shared from hp) (by decide)
    · exact ⟨⟨hinc m hm, by decide⟩, hm⟩
  | write v b =>
    cases v
    · exact absurd hp.1 (by decide)
    · exact ⟨⟨by simp [FrozenDuring], by decide⟩, hrev b hp.2⟩

/-- `u8` as a referent: any one initialised byte; `Freeze`. -/
abbrev byteRef : RefTy := RefTy.ofLayout u8L true

/-- `Cell<u8>` as a referent: same validity as `u8`, not `Freeze`. -/
abbrev cellByteRef : RefTy := RefTy.ofLayout u8L false

/-- `bool` as a referent: byte 0 or 1; `Freeze`. -/
abbrev boolRef : RefTy := RefTy.ofLayout boolL true

/-- `Cell<bool>` as a referent: byte 0 or 1; not `Freeze`. -/
abbrev cellBoolRef : RefTy := RefTy.ofLayout boolL false

/-- An uninhabited referent type (no valid byte string), flagged `Freeze`. -/
def neverRef : RefTy := ⟨fun _ => False, true⟩

theorem byteRef_valid (b : Fin 256) : byteRef.valid [Sym.byte b] := by
  show u8L.Lang [Sym.byte b]
  exact Layout.Path.cons (by decide)
    (by simp [u8L, byteEdges, List.mem_map, List.mem_finRange]) (Layout.Path.nil _)

theorem cellByteRef_valid (b : Fin 256) : cellByteRef.valid [Sym.byte b] :=
  byteRef_valid b

theorem neverRef_not_satisfiable : ¬ Satisfiable neverRef := fun ⟨_, h⟩ => h

end Toy.LayoutDfa
