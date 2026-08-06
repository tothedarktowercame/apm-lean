import Mathlib

/-!
# APM b97J03

## Statement repairs

None.

## Encoding questions

None. The number `r` is the finite cardinality of the set of complex roots
lying in the actual intermediate field `ℚ(α)`, and the Galois group is the
automorphism group of an arbitrary splitting field.
-/

open Polynomial

/-- The number of roots of `P` contained in `ℚ(α)`. -/
noncomputable def apm_b97j03_rootCount (P : Polynomial ℚ) (α : ℂ) : ℕ :=
  Set.ncard {z : ℂ |
    (P.map (algebraMap ℚ ℂ)).IsRoot z ∧
      z ∈ IntermediateField.adjoin ℚ ({α} : Set ℂ)}

/-- The polynomial `X⁶ - 2`. -/
noncomputable def apm_b97j03_special : Polynomial ℚ :=
  X ^ 6 - C 2

theorem apm_b97j03 :
    (∀ (P : Polynomial ℚ) (α : ℂ),
      Irreducible P → (P.map (algebraMap ℚ ℂ)).IsRoot α →
      apm_b97j03_rootCount P α ∣ P.natDegree ∧
      (∀ (K : Type*) [Field K] [Algebra ℚ K] [IsSplittingField ℚ K P],
        (∀ σ τ : K ≃ₐ[ℚ] K, σ * τ = τ * σ) →
        apm_b97j03_rootCount P α = P.natDegree)) ∧
    (∀ α : ℂ, (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α →
      apm_b97j03_rootCount apm_b97j03_special α = 2) := by
  sorry
