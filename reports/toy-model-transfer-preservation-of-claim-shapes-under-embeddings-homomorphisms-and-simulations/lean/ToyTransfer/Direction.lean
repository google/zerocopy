import ToyTransfer.Countermodels

/-!
# Counterexamples go the opposite way to proofs

Restatement of `univ_preserved_to_substructure_of_embedding` and
`exist_preserved_to_extension_of_embedding` for the two orientations of an embedding
between a model and a system, with countermodels for the unlicensed directions.

* **Model embeds into system** (`h : M → S` an embedding, so `M` is isomorphic to the
  induced substructure of `S` on the image of `h`: every element of `M` has an image in
  `S`, and `R` and `P` hold in `M` exactly when they hold at the images): model
  counterexamples to universal formulas, and model witnesses to existential formulas,
  transfer to the system; model truth of a universal formula does not determine the
  truth of that formula in the system.
* **System embeds into model** (`h : S → M` an embedding, so `M` extends `S` by extra
  elements while agreeing with `S` on the atomic facts about `S`'s elements): universal
  formulas true in the model transfer to the system; model counterexamples to universal
  formulas, and model witnesses to existential formulas, may be spurious.

An injective homomorphism that does not reflect `R` or `P` (a submodel obtained by
deleting edges, or a model that adds edges between existing elements) is not an
embedding, and none of the transfers below is claimed for it.
-/

namespace Toy.Transfer

/-! ## The model embeds into the system -/

/-- **Model embeds into system: universal counterexamples transfer.** Let `h : M → S` be
an embedding. If a universal formula fails in the model `M` at `e`, it fails in the
system `S` at `h ∘ e`. -/
theorem univ_counterexample_transfers_along_model_embedding {M S : Str}
    (h : M.carrier → S.carrier) (hemb : IsEmbedding h)
    {n : Nat} {φ : Fml n} (hφ : IsUniv φ) (e : Fin n → M.carrier) :
    ¬ Sat M φ e → ¬ Sat S φ (h ∘ e) :=
  fun hM hS => hM (univ_preserved_to_substructure_of_embedding h hemb.inj hemb.presR
    hemb.presP hemb.reflR hemb.reflP hφ e hS)

/-- **Model embeds into system: existential witnesses transfer.** Let `h : M → S` be an
embedding. If an existential formula holds in the model at `e`, it holds in the system
at `h ∘ e`. -/
theorem exist_witness_transfers_along_model_embedding {M S : Str}
    (h : M.carrier → S.carrier) (hemb : IsEmbedding h)
    {n : Nat} {φ : Fml n} (hφ : IsExist φ) (e : Fin n → M.carrier) :
    Sat M φ e → Sat S φ (h ∘ e) :=
  exist_preserved_to_extension_of_embedding h hemb.inj hemb.presR hemb.presP hemb.reflR
    hemb.reflP hφ e

/-- **Model embeds into system: model truth of `∀x, P x` does not determine its truth in
the system.** The model `S1P` satisfies `∀x, P x`. It has two non-surjective embeddings:
into `S2PP`, where the sentence holds, and into `S2PN`, where it fails. -/
theorem allP_truth_in_model_undetermined_in_system_along_embedding :
    IsUniv allP ∧ Sat S1P.toStr allP Fin.elim0 ∧
    IsEmbedding inclPP ∧ ¬ Function.Surjective inclPP ∧
      Sat S2PP.toStr allP (inclPP ∘ Fin.elim0) ∧
    IsEmbedding inclPN ∧ ¬ Function.Surjective inclPN ∧
      ¬ Sat S2PN.toStr allP (inclPN ∘ Fin.elim0) := by
  decide

/-- Model truth of a universal sentence can still license other claims about the system:
if a non-empty model satisfies `∀x, P x` and embeds into the system, the system
satisfies `∃x, P x`. -/
theorem allP_in_nonempty_model_gives_exP_in_system {M S : Str} (m₀ : M.carrier)
    (h : M.carrier → S.carrier) (hemb : IsEmbedding h) :
    SatS M allP → SatS S exP :=
  fun hall => ⟨h m₀, hemb.presP m₀ (hall m₀)⟩

/-- Non-vacuity of the model-embeds-into-system statements: `∀x, P x` fails in the model
`S1N`, which embeds into `S2NP`; `∃x, P x` holds in the model `S1P`, which embeds into
`S2PN`. -/
theorem model_embeds_into_system_nonvacuous :
    IsUniv allP ∧ IsEmbedding inclNP ∧ ¬ Sat S1N.toStr allP Fin.elim0 ∧
    IsExist exP ∧ IsEmbedding inclPN ∧ Sat S1P.toStr exP Fin.elim0 := by
  decide

/-! ## The system embeds into the model -/

/-- **System embeds into model: universal truths transfer down.** Let `h : S → M` be an
embedding of the system into the model. If a universal formula holds in the model at
`h ∘ e`, it holds in the system at `e`. -/
theorem univ_truth_transfers_down_from_model_extension {S M : Str}
    (h : S.carrier → M.carrier) (hemb : IsEmbedding h)
    {n : Nat} {φ : Fml n} (hφ : IsUniv φ) (e : Fin n → S.carrier) :
    Sat M φ (h ∘ e) → Sat S φ e :=
  univ_preserved_to_substructure_of_embedding h hemb.inj hemb.presR hemb.presP hemb.reflR
    hemb.reflP hφ e

/-- **System embeds into model: model counterexamples may be spurious.** The system
`S1P` embeds into the model `S2PN` by `inclPN`; the universal sentence `∀x, P x` fails in
the model and holds in the system. -/
theorem model_counterexample_may_be_spurious_in_model_extension :
    IsUniv allP ∧ IsEmbedding inclPN ∧
    ¬ Sat S2PN.toStr allP (inclPN ∘ Fin.elim0) ∧ Sat S1P.toStr allP Fin.elim0 := by
  decide

/-- **System embeds into model: model witnesses may be spurious.** The system `S1N`
embeds into the model `S2NP` by `inclNP`; the existential sentence `∃x, P x` holds in the
model and fails in the system. -/
theorem model_witness_may_be_spurious_in_model_extension :
    IsExist exP ∧ IsEmbedding inclNP ∧
    Sat S2NP.toStr exP (inclNP ∘ Fin.elim0) ∧ ¬ Sat S1N.toStr exP Fin.elim0 := by
  decide

end Toy.Transfer
