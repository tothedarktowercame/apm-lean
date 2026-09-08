import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open scoped NNReal

namespace SardTargetOrthogonalCoordinateEquivProbe

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Target coordinates given by a subspace and its orthogonal complement. -/
def targetOrthogonalCoordinates (R : Submodule ℝ F) :
    F ≃L[ℝ] R × Rᗮ :=
  R.orthogonalDecomposition.toContinuousLinearEquiv.trans
    (WithLp.prodContinuousLinearEquiv 2 ℝ R Rᗮ)

@[simp] theorem targetOrthogonalCoordinates_apply (R : Submodule ℝ F) (y : F) :
    targetOrthogonalCoordinates R y =
      (R.orthogonalProjection y, Rᗮ.orthogonalProjection y) := by
  simp [targetOrthogonalCoordinates]
  rfl

#print axioms targetOrthogonalCoordinates_apply

end
end SardTargetOrthogonalCoordinateEquivProbe
