import ConstructionTargets.SardLocalRankNormalForm
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open scoped Topology

namespace SardComplementedDerivativeSplitProbe

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Orthogonal projections split an arbitrary finite-dimensional derivative into
surjective left and right coordinate derivatives with complementary kernels. -/
theorem exists_complemented_derivative_split (L : E →L[ℝ] F) :
    let R := LinearMap.range L.toLinearMap
    let A : E →L[ℝ] R := R.orthogonalProjection.comp L
    let G := A.ker
    let B : E →L[ℝ] G := G.orthogonalProjection
    A.range = ⊤ ∧ B.range = ⊤ ∧ IsCompl A.ker B.ker := by
  dsimp only
  let R := LinearMap.range L.toLinearMap
  let A : E →L[ℝ] R := R.orthogonalProjection.comp L
  let G := A.ker
  let B : E →L[ℝ] G := G.orthogonalProjection
  have hA : A.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    rcases y.property with ⟨x, hx⟩
    refine ⟨x, Subtype.ext ?_⟩
    have hproj : R.orthogonalProjection (L x) = y := by
      rw [show L x = (y : F) from hx]
      exact R.orthogonalProjection_mem_subspace_eq_self y
    exact congrArg Subtype.val hproj
  have hB : B.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    refine ⟨y, ?_⟩
    exact G.orthogonalProjection_mem_subspace_eq_self y
  refine ⟨hA, hB, ?_⟩
  have hker : B.ker = Gᗮ := by
    change G.orthogonalProjection.ker = Gᗮ
    exact G.ker_orthogonalProjection
  rw [hker]
  exact G.isCompl_orthogonal_of_hasOrthogonalProjection

#print axioms exists_complemented_derivative_split

end SardComplementedDerivativeSplitProbe
