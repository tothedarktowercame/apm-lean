import ConstructionTargets.CappedCylinderHemisphereIntegral

/-! # Final assembly adapter for the frozen t03J06 calculation -/

open MeasureTheory
open scoped Interval
noncomputable section

namespace ConstructionTargets.T03J06FinalAdapter

open ConstructionTargets.CappedCylinderSurfaceIntegral
open ConstructionTargets.CappedCylinderHemisphereIntegral
open ConstructionTargets.HemisphereInverseSqrtDiskIntegral

/-- The scalar surface integral in exactly the cylinder-plus-cap shape used by
the frozen problem. -/
def bulletIntegral (cylinderPullback : ℝ → ℝ → ℝ)
    (hemispherePullback : ℝ × ℝ → ℝ) : ℝ :=
  (∫ theta in (0 : ℝ)..2 * Real.pi,
    ∫ z in (-1 : ℝ)..1, cylinderPullback theta z) +
  ∫ p in unitDisk, hemispherePullback p

/-- The two proved pointwise pullback formulas imply the final `7π` value;
neither component value is supplied as a hypothesis. -/
theorem bulletIntegral_eq_seven_pi
    (cylinderPullback : ℝ → ℝ → ℝ)
    (hemispherePullback : ℝ × ℝ → ℝ)
    (hcylinder : ∀ theta z,
      cylinderPullback theta z = cylinderIntegrand theta z)
    (hhemisphere : ∀ p,
      hemispherePullback p = hemisphereIntegrand p) :
    bulletIntegral cylinderPullback hemispherePullback = 7 * Real.pi := by
  rw [bulletIntegral,
    cylinder_surface_integral_of_pointwise cylinderPullback hcylinder,
    hemisphere_surface_integral_of_pointwise hemispherePullback hhemisphere]
  ring

/-- Full logical assembly matching the frozen conjunction.  The local facts
are deliberately abstract propositions so that the standalone frozen helper
declarations can be passed without duplicating their analytic definitions.
The surface-integral conclusion itself is derived here from the actual
pointwise pullback formulas. -/
theorem full_conjunction_of_frozen_helpers
    (Smooth ExtValue ExtNonzero Nonexact : Prop)
    (hSmooth : Smooth) (hExtValue : ExtValue)
    (hExtNonzero : ExtNonzero) (hNonexact : Nonexact)
    (cylinderPullback : ℝ → ℝ → ℝ)
    (hemispherePullback : ℝ × ℝ → ℝ)
    (hcylinder : ∀ theta z,
      cylinderPullback theta z = cylinderIntegrand theta z)
    (hhemisphere : ∀ p,
      hemispherePullback p = hemisphereIntegrand p) :
    Smooth ∧ ExtValue ∧ ExtNonzero ∧ Nonexact ∧
      bulletIntegral cylinderPullback hemispherePullback = 7 * Real.pi := by
  exact ⟨hSmooth, hExtValue, hExtNonzero, hNonexact,
    bulletIntegral_eq_seven_pi cylinderPullback hemispherePullback
      hcylinder hhemisphere⟩

#print axioms bulletIntegral_eq_seven_pi
#print axioms full_conjunction_of_frozen_helpers

end ConstructionTargets.T03J06FinalAdapter
