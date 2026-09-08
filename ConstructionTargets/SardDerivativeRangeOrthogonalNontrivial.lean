import ConstructionTargets.SardTargetOrthogonalCoordinateEquiv

namespace SardDerivativeRangeOrthogonalNontrivialProbe

/-- A proper subspace of a finite-dimensional real inner-product space has a
nontrivial orthogonal complement. -/
theorem nontrivial_orthogonal_of_ne_top
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (R : Submodule ℝ F) (hR : R ≠ ⊤) :
    Nontrivial Rᗮ := by
  rw [Submodule.nontrivial_iff_ne_bot]
  intro horth
  exact hR (Submodule.orthogonal_eq_bot_iff.mp horth)

#print axioms nontrivial_orthogonal_of_ne_top

end SardDerivativeRangeOrthogonalNontrivialProbe
