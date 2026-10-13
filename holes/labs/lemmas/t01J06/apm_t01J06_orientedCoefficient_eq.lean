import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import ConstructionTargets.IntrinsicSphereSecondMoments

open MeasureTheory
open scoped Manifold ENNReal
noncomputable section

abbrev apm_t01J06_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t01J06_E3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t01J06_S1 := Metric.sphere (0 : apm_t01J06_E2) 1
abbrev apm_t01J06_S2 := Metric.sphere (0 : apm_t01J06_E3) 1
abbrev apm_t01J06_E5 := apm_t01J06_E3 × apm_t01J06_E2
def apm_t01J06_sphereTangent (q : apm_t01J06_S2) : Submodule ℝ apm_t01J06_E3 :=
  (Submodule.span ℝ ({(q : apm_t01J06_E3)} : Set apm_t01J06_E3)).orthogonal
def apm_t01J06_circleTangent (p : apm_t01J06_S1) : Submodule ℝ apm_t01J06_E2 :=
  (Submodule.span ℝ ({(p : apm_t01J06_E2)} : Set apm_t01J06_E2)).orthogonal
abbrev apm_t01J06_AmbientForm2 := apm_t01J06_E3 → apm_t01J06_E3 [⋀^Fin 2]→L[ℝ] ℝ
abbrev apm_t01J06_SphereForm2 := ∀ q : apm_t01J06_S2,
  apm_t01J06_sphereTangent q [⋀^Fin 2]→L[ℝ] ℝ
abbrev apm_t01J06_ProductForm2 := ∀ qp : apm_t01J06_S2 × apm_t01J06_S1,
  (apm_t01J06_sphereTangent qp.1 × apm_t01J06_circleTangent qp.2) [⋀^Fin 2]→L[ℝ] ℝ
abbrev apm_t01J06_AmbientProductForm2 :=
  apm_t01J06_E5 → apm_t01J06_E5 [⋀^Fin 2]→L[ℝ] ℝ
def apm_t01J06_isOmega (omega : apm_t01J06_AmbientForm2) : Prop :=
  ∀ x v, omega x v = (x 2 + 3) * (v 0 0 * v 1 1 - v 0 1 * v 1 0)
def apm_t01J06_isInclusionPullback (omega : apm_t01J06_AmbientForm2)
    (alpha : apm_t01J06_SphereForm2) : Prop :=
  ∀ q v, alpha q v = omega q (fun k ↦ (v k : apm_t01J06_E3))
def apm_t01J06_isJPullback (p : apm_t01J06_S1) (zeta : apm_t01J06_ProductForm2)
    (alpha : apm_t01J06_SphereForm2) : Prop :=
  ∀ q v, zeta (q,p) (fun k ↦ (v k, 0)) = alpha q v
def apm_t01J06_productRestriction (Z : apm_t01J06_AmbientProductForm2) :
    apm_t01J06_ProductForm2 := fun qp ↦
  (Z ((qp.1 : apm_t01J06_E3), (qp.2 : apm_t01J06_E2))).compContinuousLinearMap
    (ContinuousLinearMap.prodMap (apm_t01J06_sphereTangent qp.1).subtypeL
      (apm_t01J06_circleTangent qp.2).subtypeL)
def apm_t01J06_IsClosedProductExtension (p : apm_t01J06_S1)
    (alpha : apm_t01J06_SphereForm2) : Prop :=
  ∃ (W : Set apm_t01J06_E5) (Z : apm_t01J06_AmbientProductForm2),
    IsOpen W ∧ (∀ qp : apm_t01J06_S2 × apm_t01J06_S1,
      ((qp.1 : apm_t01J06_E3), (qp.2 : apm_t01J06_E2)) ∈ W) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) Z W ∧ (∀ x ∈ W, extDeriv Z x = 0) ∧
    apm_t01J06_isJPullback p (apm_t01J06_productRestriction Z) alpha
def apm_t01J06_tangentProjection (q : apm_t01J06_S2) (i : Fin 3) :
    apm_t01J06_sphereTangent q :=
  (apm_t01J06_sphereTangent q).orthogonalProjection (EuclideanSpace.single i 1)
def apm_t01J06_orientedCoefficient (alpha : apm_t01J06_SphereForm2)
    (q : apm_t01J06_S2) : ℝ :=
  q.1 0 * alpha q ![apm_t01J06_tangentProjection q 1, apm_t01J06_tangentProjection q 2] -
  q.1 1 * alpha q ![apm_t01J06_tangentProjection q 0, apm_t01J06_tangentProjection q 2] +
  q.1 2 * alpha q ![apm_t01J06_tangentProjection q 0, apm_t01J06_tangentProjection q 1]
def apm_t01J06_sphereIntegral (alpha : apm_t01J06_SphereForm2) : ℝ :=
  ∫ q, apm_t01J06_orientedCoefficient alpha q ∂μH[2]

/-- Local projection-coordinate algebra. -/
-- BEGIN SEAT AREA
theorem apm_t01J06_orientedCoefficient_eq
    (omega : apm_t01J06_AmbientForm2) (homega : apm_t01J06_isOmega omega)
    (alpha : apm_t01J06_SphereForm2)
    (halpha : apm_t01J06_isInclusionPullback omega alpha) (q : apm_t01J06_S2) :
    apm_t01J06_orientedCoefficient alpha q = (q.1 2 + 3) * q.1 2 := by
  sorry
-- END SEAT AREA

/-- LIBRARY: the two normalized Hausdorff moments needed here. -/
theorem apm_t01J06_sphere_moments :
    Integrable (fun q : apm_t01J06_S2 ↦ q.1 2 ^ 2) μH[2] ∧
    Integrable (fun q : apm_t01J06_S2 ↦ q.1 2) μH[2] ∧
    (∫ q : apm_t01J06_S2, q.1 2 ^ 2 ∂μH[2]) = 4 * Real.pi / 3 ∧
    (∫ q : apm_t01J06_S2, q.1 2 ∂μH[2]) = 0 := by
  sorry

/-- LIBRARY: the specialized Stokes/contractibility obstruction. -/
theorem apm_t01J06_closed_extension_integral_zero
    (eta : apm_t01J06_AmbientForm2) (alpha : apm_t01J06_SphereForm2)
    (hs : ContDiff ℝ (⊤ : ℕ∞) eta) (hc : extDeriv eta = 0)
    (hp : apm_t01J06_isInclusionPullback eta alpha) :
    apm_t01J06_sphereIntegral alpha = 0 := by
  sorry

/-- LIBRARY: radial retraction to the sphere, followed by first projection. -/
theorem apm_t01J06_exists_closed_product_extension
    (omega : apm_t01J06_AmbientForm2) (homega : apm_t01J06_isOmega omega)
    (alpha : apm_t01J06_SphereForm2)
    (halpha : apm_t01J06_isInclusionPullback omega alpha)
    (p : apm_t01J06_S1) : apm_t01J06_IsClosedProductExtension p alpha := by
  sorry

theorem apm_t01j06
    (omega : apm_t01J06_AmbientForm2) (homega : apm_t01J06_isOmega omega)
    (alpha : apm_t01J06_SphereForm2)
    (halpha : apm_t01J06_isInclusionPullback omega alpha) :
    apm_t01J06_sphereIntegral alpha = 4 * Real.pi / 3 ∧
    ¬ (∃ eta : apm_t01J06_AmbientForm2, ContDiff ℝ (⊤ : ℕ∞) eta ∧
        extDeriv eta = 0 ∧ apm_t01J06_isInclusionPullback eta alpha) ∧
    ∀ p : apm_t01J06_S1, apm_t01J06_IsClosedProductExtension p alpha := by
  have hm := apm_t01J06_sphere_moments
  have hi : apm_t01J06_sphereIntegral alpha = 4 * Real.pi / 3 := by
    rw [apm_t01J06_sphereIntegral]
    simp_rw [apm_t01J06_orientedCoefficient_eq omega homega alpha halpha]
    rw [show (fun q : apm_t01J06_S2 ↦ (q.1 2 + 3) * q.1 2) =
      (fun q ↦ q.1 2 ^ 2 + 3 * q.1 2) by funext q; ring]
    rw [integral_add hm.1 (hm.2.1.const_mul 3), integral_const_mul, hm.2.2.1, hm.2.2.2]
    ring
  refine ⟨hi, ?_, fun p ↦ apm_t01J06_exists_closed_product_extension omega homega alpha halpha p⟩
  rintro ⟨eta, hs, hc, hp⟩
  have hz := apm_t01J06_closed_extension_integral_zero eta alpha hs hc hp
  have hpi : 0 < 4 * Real.pi / 3 := by positivity
  linarith

#print axioms apm_t01j06
