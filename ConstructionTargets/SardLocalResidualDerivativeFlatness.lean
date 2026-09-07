import ConstructionTargets.SardProjectedKernelFlatness

namespace SardLocalResidualDerivativeFlatnessProbe

variable {E F R S : Type*}
  [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F]
  [AddCommGroup R] [Module ℝ R]
  [AddCommGroup S] [Module ℝ S]

/-- On a locus where the fixed projected derivative block is surjective and
the full derivative has no larger rank, every residual target coordinate has
zero derivative in every tangent direction to the projected fibre. -/
theorem residualDerivative_vanishes_on_projectedFibres
    (D : E → (E →ₗ[ℝ] F)) (P : F →ₗ[ℝ] R) (Q : F →ₗ[ℝ] S) (U : Set E)
    (hsurj : ∀ y ∈ U, (P.comp (D y)).range = ⊤)
    (hrank : ∀ y ∈ U,
      Module.finrank ℝ (LinearMap.range (D y)) ≤ Module.finrank ℝ R) :
    ∀ y ∈ U, ∀ v ∈ LinearMap.ker (P.comp (D y)), (Q.comp (D y)) v = 0 := by
  intro y hy v hv
  have hv' : D y v = 0 :=
    SardProjectedKernelFlatnessProbe.apply_eq_zero_of_mem_projected_ker
      (D y) P (hsurj y hy) (hrank y hy) hv
  change Q (D y v) = 0
  rw [hv']
  exact map_zero Q

#print axioms residualDerivative_vanishes_on_projectedFibres
end SardLocalResidualDerivativeFlatnessProbe
