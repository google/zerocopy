import ToyProv.Exec

/-!
# Disjointness of allocations

`DisjointBlocks s`: every block of `s` has positive size, lies below `s.top`, and blocks with
smaller ids lie entirely below blocks with larger ids. It holds initially and is preserved by
every instruction in every model (bump allocation, `alloc 0` is UB, blocks are never removed).
Consequently two pointers that are in bounds of live blocks (`base ≤ address < base + size`) and have equal addresses have
the same provenance (used by R1c), and accesses through pointers of different provenance touch
disjoint bytes (used by R4c, R4d).
-/

namespace Toy.Prov

theorem lookup_eq_getElem? {α : Type} (bs : List α) (i : Nat) :
    lookup bs i = bs[i]? := by
  induction bs generalizing i with
  | nil => cases i <;> rfl
  | cons b bs ih =>
    cases i with
    | zero => rfl
    | succ i => simp [lookup, ih]

def DisjointBlocks (s : St) : Prop :=
  (∀ (i : Nat) (b : Block), s.blocks[i]? = some b → 0 < b.size ∧ b.base + b.size ≤ s.top) ∧
  (∀ (i j : Nat) (bi bj : Block), i < j → s.blocks[i]? = some bi → s.blocks[j]? = some bj →
    bi.base + bi.size ≤ bj.base)

theorem disjointBlocks_init : DisjointBlocks init :=
  ⟨fun _ _ h => by simp [init] at h, fun _ _ _ _ _ h => by simp [init] at h⟩

theorem disjointBlocks_of_eq {s s' : St} (hs : DisjointBlocks s)
    (hb : s'.blocks = s.blocks) (ht : s'.top = s.top) : DisjointBlocks s' := by
  refine ⟨fun i b hi => ?_, fun i j bi bj hlt hi hj => ?_⟩
  · rw [hb] at hi; rw [ht]; exact hs.1 i b hi
  · rw [hb] at hi hj; exact hs.2 i j bi bj hlt hi hj

theorem killBlock_getElem? (bs : List Block) (id i : Nat) :
    (killBlock bs id)[i]? = (bs[i]?).map (fun b => if i = id then { b with live := false } else b) := by
  induction bs generalizing id i with
  | nil => cases id <;> cases i <;> rfl
  | cons b bs ih =>
    cases id with
    | zero =>
      cases i with
      | zero => simp [killBlock]
      | succ i =>
        simp only [killBlock, List.getElem?_cons_succ]
        cases bs[i]? <;> simp
    | succ id =>
      cases i with
      | zero => simp [killBlock]
      | succ i =>
        simp only [killBlock, List.getElem?_cons_succ, ih]
        cases bs[i]? <;> simp

theorem step_preserves_disjointBlocks {m : Model} {s s' : St} {i : Instr}
    (hs : DisjointBlocks s) (hstep : some s' ∈ step m s i) : DisjointBlocks s' := by
  cases i with
  | alloc d n =>
    by_cases hn : n = 0
    · simp [step, hn] at hstep
    · simp only [step, hn, ↓reduceIte, List.mem_singleton, Option.some.injEq] at hstep
      subst hstep
      refine ⟨fun k b hk => ?_, fun j k bj bk hjk hj hk => ?_⟩
      · simp only [List.getElem?_append] at hk
        split at hk
        · have ⟨hsz, hbend⟩ := hs.1 k b hk; dsimp only [Addr] at *; exact ⟨hsz, by omega⟩
        · rw [List.getElem?_singleton] at hk
          split at hk
          · simp only [Option.some.injEq] at hk; subst hk
            dsimp only [Addr] at *; exact ⟨by omega, by omega⟩
          · contradiction
      · simp only [List.getElem?_append] at hj hk
        split at hj <;> split at hk
        · exact hs.2 j k bj bk hjk hj hk
        · rw [List.getElem?_singleton] at hk
          split at hk
          · simp only [Option.some.injEq] at hk; subst hk; exact (hs.1 j bj hj).2
          · contradiction
        · omega
        · rw [List.getElem?_singleton] at hj hk
          split at hj <;> split at hk <;> try contradiction
          omega
  | free p =>
    simp only [step] at hstep
    split at hstep <;> try (simp at hstep; done)
    split at hstep <;> simp at hstep
    subst hstep
    refine ⟨fun k b hk => ?_, fun j k bj bk hjk hj hk => ?_⟩
    · rw [killBlock_getElem?] at hk
      cases hbk : s.blocks[k]? with
      | none => simp [hbk] at hk
      | some b₀ =>
        simp only [hbk, Option.map_some, Option.some.injEq] at hk
        have hkb := hs.1 k b₀ hbk
        split at hk <;> subst hk <;> exact hkb
    · rw [killBlock_getElem?] at hj hk
      cases hbj : s.blocks[j]? with
      | none => simp [hbj] at hj
      | some bj₀ =>
        cases hbk : s.blocks[k]? with
        | none => simp [hbk] at hk
        | some bk₀ =>
          simp only [hbj, hbk, Option.map_some, Option.some.injEq] at hj hk
          have h2 := hs.2 j k bj₀ bk₀ hjk hbj hbk
          split at hj <;> split at hk <;> subst hj <;> subst hk <;> exact h2
  | load d ty p =>
    simp only [step] at hstep
    split at hstep <;> try (simp at hstep; done)
    split at hstep <;> try (simp at hstep; done)
    cases ty with
    | int =>
      simp only at hstep
      split at hstep <;> simp at hstep
      subst hstep; exact disjointBlocks_of_eq hs rfl rfl
    | ptr =>
      simp only at hstep
      split at hstep
      · simp at hstep; subst hstep; exact disjointBlocks_of_eq hs rfl rfl
      · cases m <;> simp [castToPtr] at hstep
        · subst hstep; exact disjointBlocks_of_eq hs rfl rfl
        · subst hstep; exact disjointBlocks_of_eq hs rfl rfl
        · split at hstep
          · simp at hstep; subst hstep; exact disjointBlocks_of_eq hs rfl rfl
          · simp at hstep
            rcases hstep with rfl | ⟨_, _, rfl⟩ <;> exact disjointBlocks_of_eq hs rfl rfl
      · simp at hstep
  | store p r =>
    simp only [step] at hstep
    split at hstep <;> try (simp at hstep; done)
    split at hstep <;> try (simp at hstep; done)
    simp at hstep; subst hstep; exact disjointBlocks_of_eq hs rfl rfl
  | memcpy d r n =>
    simp only [step] at hstep
    split at hstep <;> try (simp at hstep; done)
    split at hstep <;> try (simp at hstep; done)
    simp at hstep; subst hstep; exact disjointBlocks_of_eq hs rfl rfl
  | ptr2int d p =>
    simp only [step] at hstep
    split at hstep <;> simp at hstep
    subst hstep; exact disjointBlocks_of_eq hs rfl rfl
  | int2ptr d i =>
    simp only [step] at hstep
    split at hstep <;> try (simp at hstep; done)
    cases m <;> simp [castToPtr] at hstep
    · subst hstep; exact disjointBlocks_of_eq hs rfl rfl
    · subst hstep; exact disjointBlocks_of_eq hs rfl rfl
    · split at hstep
      · simp at hstep; subst hstep; exact disjointBlocks_of_eq hs rfl rfl
      · simp at hstep
        rcases hstep with rfl | ⟨_, _, rfl⟩ <;> exact disjointBlocks_of_eq hs rfl rfl
  | ptrEq d p q =>
    simp only [step] at hstep
    split at hstep <;> simp at hstep
    subst hstep; exact disjointBlocks_of_eq hs rfl rfl
  | intEq d i j =>
    simp only [step] at hstep
    split at hstep <;> simp at hstep
    subst hstep; exact disjointBlocks_of_eq hs rfl rfl
  | offset d p k =>
    simp only [step] at hstep
    split at hstep <;> try (simp at hstep; done)
    split at hstep <;> simp at hstep
    subst hstep; exact disjointBlocks_of_eq hs rfl rfl
  | const d n =>
    simp only [step, List.mem_singleton, Option.some.injEq] at hstep
    subst hstep; exact disjointBlocks_of_eq hs rfl rfl
  | copy d r =>
    simp only [step] at hstep
    split at hstep <;> simp at hstep
    subst hstep; exact disjointBlocks_of_eq hs rfl rfl
  | obs r =>
    simp only [step] at hstep
    cases hr : s.regs r with
    | none => simp [hr] at hstep
    | some v => cases v <;> (simp [hr] at hstep; subst hstep; exact disjointBlocks_of_eq hs rfl rfl)

theorem execOk_preserves_disjointBlocks {m : Model} {P : Prog} {s s' : St}
    (hs : DisjointBlocks s) (h : s' ∈ execOk m P s) : DisjointBlocks s' := by
  induction P generalizing s with
  | nil => simp [execOk_nil] at h; subst h; exact hs
  | cons i P ih =>
    rw [execOk_cons, List.mem_flatMap] at h
    rcases h with ⟨s₁, hs₁, hs'⟩
    rw [List.mem_filterMap] at hs₁
    rcases hs₁ with ⟨o, ho, ho_eq⟩
    cases o with
    | none => simp at ho_eq
    | some s₁' =>
      simp only [id_eq, Option.some.injEq] at ho_eq
      subst ho_eq
      exact ih (step_preserves_disjointBlocks hs ho) hs'

theorem after_disjointBlocks (m : Model) (P : Prog) : ∀ s ∈ after m P, DisjointBlocks s :=
  fun _ hs => execOk_preserves_disjointBlocks disjointBlocks_init hs

theorem disjoint_eq_of_in_range {s : St} (hd : DisjointBlocks s) {i j : Nat}
    {bi bj : Block} {a : Addr}
    (hi : s.blocks[i]? = some bi) (hj : s.blocks[j]? = some bj)
    (hai : bi.base ≤ a ∧ a + 1 ≤ bi.base + bi.size)
    (haj : bj.base ≤ a ∧ a + 1 ≤ bj.base + bj.size) : i = j := by
  rcases hai with ⟨hai1, hai2⟩
  rcases haj with ⟨haj1, haj2⟩
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · have hlt2 := hd.2 i j bi bj hlt hi hj; dsimp only [Addr] at *; omega
  · exact heq
  · have hgt2 := hd.2 j i bj bi hgt hj hi; dsimp only [Addr] at *; omega

theorem disjoint_two_bytes_of_ne {s : St} (hd : DisjointBlocks s) {i j : Nat}
    {bi bj : Block} {a₁ a₂ : Addr}
    (hne : i ≠ j) (hi : s.blocks[i]? = some bi) (hj : s.blocks[j]? = some bj)
    (ha₁ : bi.base ≤ a₁ ∧ a₁ + 2 ≤ bi.base + bi.size)
    (ha₂ : bj.base ≤ a₂ ∧ a₂ + 2 ≤ bj.base + bj.size) :
    a₁ + 2 ≤ a₂ ∨ a₂ + 2 ≤ a₁ := by
  rcases ha₁ with ⟨ha11, ha12⟩
  rcases ha₂ with ⟨ha21, ha22⟩
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · left; have hlt2 := hd.2 i j bi bj hlt hi hj; dsimp only [Addr] at *; omega
  · exact absurd heq hne
  · right; have hgt2 := hd.2 j i bj bi hgt hj hi; dsimp only [Addr] at *; omega

end Toy.Prov
