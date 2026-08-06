import Mathlib

/-!
# APM b93J04

## Statement repairs

None.

## Encoding questions

None. The splitting field is quantified abstractly; the witnesses `r₂` and
`r₃` encode `√2` and `√3`, so the basis, automorphism action, and complete
intermediate-field list are stated inside the actual splitting field.
-/

open Polynomial

/-- The polynomial `X⁴ - 10X² + 1` over `ℚ`. -/
noncomputable def apm_b93j04_poly : Polynomial ℚ :=
  X ^ 4 - C 10 * X ^ 2 + C 1

theorem apm_b93j04 :
    ∀ (K : Type*) [Field K] [Algebra ℚ K]
        [IsSplittingField ℚ K apm_b93j04_poly],
      ∃ (r₂ r₃ : K) (basis : Module.Basis (Fin 4) ℚ K)
          (σ τ : K ≃ₐ[ℚ] K),
        r₂ ^ 2 = algebraMap ℚ K 2 ∧
        r₃ ^ 2 = algebraMap ℚ K 3 ∧
        IntermediateField.adjoin ℚ ({r₂, r₃} : Set K) = ⊤ ∧
        basis 0 = 1 ∧ basis 1 = r₂ ∧ basis 2 = r₃ ∧ basis 3 = r₂ * r₃ ∧
        Nonempty ((K ≃ₐ[ℚ] K) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) ∧
        σ r₂ = -r₂ ∧ σ r₃ = r₃ ∧
        τ r₂ = r₂ ∧ τ r₃ = -r₃ ∧
        (∀ φ : K ≃ₐ[ℚ] K, φ = 1 ∨ φ = σ ∨ φ = τ ∨ φ = σ * τ) ∧
        (∀ E : IntermediateField ℚ K,
          E = ⊥ ∨
          E = IntermediateField.adjoin ℚ ({r₂} : Set K) ∨
          E = IntermediateField.adjoin ℚ ({r₃} : Set K) ∨
          E = IntermediateField.adjoin ℚ ({r₂ * r₃} : Set K) ∨
          E = ⊤) := by
  /- PASS-1 boundary: searched the splitting-field API, notably
     `IsSplittingField.adjoin_rootSet`, `IsSplittingField.splits`,
     `IntermediateField.adjoin_rootSet_isSplittingField`, and the finite
     Galois correspondence (`intermediateFieldEquivSubgroup`).  The intended
     route is to identify the four roots as `±√2 ± √3`, prove the abstract
     splitting field is the biquadratic extension `ℚ(√2, √3)`, and then
     enumerate the Klein-four automorphisms and its five subgroups.  I could
     not find a packaged Mathlib realization of this polynomial, and building
     the square-root witnesses, four-element basis, automorphisms, group
     equivalence, and exhaustive intermediate-field list from the generic
     root-set API exceeded pass 1. -/
  sorry
