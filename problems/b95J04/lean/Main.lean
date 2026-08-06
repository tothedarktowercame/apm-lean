import Mathlib

open Polynomial

noncomputable section

/-!
# APM b95J04

## Statement repairs

None.

## Encoding notes

The radical extension is the actual intermediate field `F⟮α⟯`; its Galois group
and the cyclic group `Multiplicative (ZMod p)` are retained explicitly.
-/

theorem apm_b95j04
    (p : ℕ) (hp : p.Prime)
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    (z : F) (hz : z ^ p = 1) (hz1 : z ≠ 1) :
    ringChar F ≠ p ∧
    (X ^ p - 1 : F[X]) =
      ∏ i ∈ Finset.range p, (X - C (z ^ (i + 1))) ∧
    (∀ α : E, α ∉ (algebraMap F E).range →
      α ^ p ∈ (algebraMap F E).range →
      IsGalois F ↥(IntermediateField.adjoin F {α}) ∧
        ∃ e : (↥(IntermediateField.adjoin F {α}) ≃ₐ[F]
            ↥(IntermediateField.adjoin F {α})) ≃* Multiplicative (ZMod p),
          ∀ σ : (↥(IntermediateField.adjoin F {α}) ≃ₐ[F]
              ↥(IntermediateField.adjoin F {α})),
            σ ⟨α, IntermediateField.subset_adjoin (F := F)
              (S := {α}) (Set.mem_singleton α)⟩ =
              (algebraMap F ↥(IntermediateField.adjoin F {α}) z) ^
                  (Multiplicative.toAdd (e σ)).val *
                ⟨α, IntermediateField.subset_adjoin (F := F)
                  (S := {α}) (Set.mem_singleton α)⟩) ∧
    (FiniteDimensional F E → IsGalois F E →
      Nat.card (E ≃ₐ[F] E) = p → IsCyclic (E ≃ₐ[F] E) →
      ∀ σ : (E ≃ₐ[F] E), σ ≠ 1 →
        ∃ α : E, α ≠ 0 ∧
          σ α = algebraMap F E z * α ∧
          α ∉ (algebraMap F E).range ∧
          α ^ p ∈ (algebraMap F E).range ∧
          IntermediateField.adjoin F {α} = ⊤) := by
  sorry
