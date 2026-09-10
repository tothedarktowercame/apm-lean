import ConstructionTargets.CoefficientSubcomplexRelativeMayerVietorisDegreewiseCriterion

noncomputable section
namespace ConstructionTargets.CoefficientSubmoduleInfQuotientDiagonal

variable (R : Type) [CommRing R]
variable {M : Type} [AddCommGroup M] [Module R M]

/-- The diagonal map from the quotient by an intersection to the product of
quotients by the two submodules. -/
def infQuotientDiagonal (P Q : Submodule R M) :
    M ⧸ (P ⊓ Q) →ₗ[R] (M ⧸ P) × (M ⧸ Q) :=
  (P ⊓ Q).liftQ (P.mkQ.prod Q.mkQ) (by
    rw [LinearMap.ker_prod, P.ker_mkQ, Q.ker_mkQ])

@[simp]
theorem infQuotientDiagonal_mk (P Q : Submodule R M) (x : M) :
    infQuotientDiagonal R P Q (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x, Submodule.Quotient.mk x) := rfl

theorem infQuotientDiagonal_injective (P Q : Submodule R M) :
    Function.Injective (infQuotientDiagonal R P Q) := by
  rw [← LinearMap.ker_eq_bot]
  apply Submodule.ker_liftQ_eq_bot
  rw [LinearMap.ker_prod, P.ker_mkQ, Q.ker_mkQ]

#print axioms infQuotientDiagonal_injective
end ConstructionTargets.CoefficientSubmoduleInfQuotientDiagonal
