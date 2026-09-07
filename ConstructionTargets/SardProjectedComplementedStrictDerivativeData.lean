import ConstructionTargets.SardLocalRankNormalForm
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

noncomputable section
namespace SardProjectedImplicitFunctionDataProbe

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Projecting a strict derivative onto its range and pairing it with projection
onto its kernel supplies all derivative and algebraic fields of the local rank datum. -/
theorem projected_complemented_strictDerivative_data
    (f : E → F) (x : E) (L : E →L[ℝ] F) (hf : HasStrictFDerivAt f L x) :
    let R := LinearMap.range L.toLinearMap
    let A : E →L[ℝ] R := R.orthogonalProjection.comp L
    let G := A.ker
    let B : E →L[ℝ] G := G.orthogonalProjection
    HasStrictFDerivAt (fun y => R.orthogonalProjection (f y)) A x ∧
      HasStrictFDerivAt (fun y => G.orthogonalProjection y) B x ∧
      A.range = ⊤ ∧ B.range = ⊤ ∧ IsCompl A.ker B.ker := by
  dsimp only
  let R := LinearMap.range L.toLinearMap
  let A : E →L[ℝ] R := R.orthogonalProjection.comp L
  let G := A.ker
  let B : E →L[ℝ] G := G.orthogonalProjection
  have hA : A.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    rcases y.property with ⟨z, hz⟩
    refine ⟨z, Subtype.ext ?_⟩
    have hp : R.orthogonalProjection (L z) = y := by
      rw [show L z = (y : F) from hz]
      exact R.orthogonalProjection_mem_subspace_eq_self y
    exact congrArg Subtype.val hp
  have hB : B.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    exact ⟨y, G.orthogonalProjection_mem_subspace_eq_self y⟩
  have hcompl : IsCompl A.ker B.ker := by
    rw [show B.ker = Gᗮ by
      change G.orthogonalProjection.ker = Gᗮ
      exact G.ker_orthogonalProjection]
    exact G.isCompl_orthogonal_of_hasOrthogonalProjection
  exact ⟨R.orthogonalProjection.hasStrictFDerivAt.comp x hf,
    G.orthogonalProjection.hasStrictFDerivAt, hA, hB, hcompl⟩

#print axioms projected_complemented_strictDerivative_data
end SardProjectedImplicitFunctionDataProbe
