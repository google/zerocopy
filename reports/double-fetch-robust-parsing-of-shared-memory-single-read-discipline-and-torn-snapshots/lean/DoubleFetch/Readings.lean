import DoubleFetch.Results

/-!
# Reading (ii) of "R-valid iff equivalent to a single-read parser": the forward direction

`rvalid_equivalence_readings_refuted` refutes the backward direction of reading (ii) (agreement in
private memory with a single-read, R-valid parser does not give R-valid). This file records what
happens in the forward direction, for the two choices of what the single-read witness must satisfy:

* witness R-valid for the spec: the forward direction holds
  (`rvalid_imp_exists_singleRead_rvalid_privRefines`);
* witness implementing the spec in private memory: such a witness exists iff the parser itself
  implements the spec (`exists_singleRead_implements_privRefines_iff_implements`), so the forward
  direction fails for an R-valid parser that does not implement the spec
  (`rvalid_not_imp_exists_singleRead_implements_privRefines`).

These are statements about the toy model; they neither establish nor refute the corresponding
claims about real parsers, compilers, kernels or hypervisors. Model–system relation: none proved.
-/

namespace Toy.DoubleFetch

section Readings

variable {n : Nat} {α : Type}

/-- Forward direction of reading (ii) with an R-valid witness. If `p` is R-valid for `spec`, then
the byte-by-byte copy parser of `p`'s own private-memory function, `copyParse (fun s => p.eval s)`,
is single-read, is R-valid for `spec`, and agrees with `p` in private memory. -/
theorem rvalid_imp_exists_singleRead_rvalid_privRefines (spec : Region n → α) (p : Prog n α)
    (hp : RValid spec p) :
    ∃ q : Prog n α, SingleRead q ∧ RValid spec q ∧ PrivRefines p q := by
  obtain ⟨hs, hi⟩ := copyParse_singleRead_implements (fun s => p.eval s)
  refine ⟨copyParse (fun s => p.eval s), hs, fun adv => ?_, fun s => (hi s).symm⟩
  obtain ⟨s', hs'⟩ := hp (Adversary.const (fun j => adv j.val j))
  refine ⟨s', ?_⟩
  rw [(copyParse_exec_eq_diagonal_and_rvalid (fun s => p.eval s)).1 adv, ← Prog.exec_const]
  exact hs'

/-- Reading (ii) with a witness that implements `spec`: some single-read parser implements `spec`
in private memory and agrees with `p` in private memory iff `p` itself implements `spec` in private
memory. -/
theorem exists_singleRead_implements_privRefines_iff_implements (spec : Region n → α)
    (p : Prog n α) :
    (∃ q : Prog n α, SingleRead q ∧ Implements q spec ∧ PrivRefines p q) ↔ Implements p spec := by
  constructor
  · rintro ⟨q, _, hq, hpq⟩ s
    rw [hpq s, hq s]
  · intro hp
    obtain ⟨hs, hi⟩ := copyParse_singleRead_implements spec
    exact ⟨copyParse spec, hs, hi, fun s => by rw [hp s, hi s]⟩

end Readings

/-- The forward direction of reading (ii) with a witness that implements the spec fails: the
constant parser `Prog.ret (0, 0)` is R-valid for `pairSpec`, but no single-read parser that
implements `pairSpec` in private memory agrees with it in private memory. -/
theorem rvalid_not_imp_exists_singleRead_implements_privRefines :
    RValid pairSpec (Prog.ret (0, 0) : Prog 2 (Byte × Byte)) ∧
      ¬ ∃ q : Prog 2 (Byte × Byte), SingleRead q ∧ Implements q pairSpec ∧
        PrivRefines (Prog.ret (0, 0)) q := by
  refine ⟨fun _ => ⟨fun _ => 0, rfl⟩, fun h => ?_⟩
  have h1 := (exists_singleRead_implements_privRefines_iff_implements pairSpec _).1 h (fun _ => 1)
  exact absurd h1 (by decide)

end Toy.DoubleFetch
