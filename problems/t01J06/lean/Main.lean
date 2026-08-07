import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# APM t01J06: a two-form on the sphere and closed extensions

## Statement repairs

None.

## Encoding questions

The forms use genuine alternating maps on the tangent spaces. The sphere
integral is the integral of the coefficient relative to the outward area form
against two-dimensional Hausdorff measure. A 2-form on the 2-sphere is closed
for dimensional reasons. The closed product extension is given explicitly as
the pullback along the projection `S² × S¹ → S²`.
-/

open MeasureTheory
open scoped Manifold ENNReal

noncomputable section

abbrev apm_t01J06_E2 := EuclideanSpace ℝ (Fin 2)
abbrev apm_t01J06_E3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t01J06_S1 := Metric.sphere (0 : apm_t01J06_E2) 1
abbrev apm_t01J06_S2 := Metric.sphere (0 : apm_t01J06_E3) 1

def apm_t01J06_sphereTangent (q : apm_t01J06_S2) : Submodule ℝ apm_t01J06_E3 :=
  (Submodule.span ℝ ({(q : apm_t01J06_E3)} : Set apm_t01J06_E3)).orthogonal

def apm_t01J06_circleTangent (p : apm_t01J06_S1) : Submodule ℝ apm_t01J06_E2 :=
  (Submodule.span ℝ ({(p : apm_t01J06_E2)} : Set apm_t01J06_E2)).orthogonal

abbrev apm_t01J06_AmbientForm2 :=
  apm_t01J06_E3 → apm_t01J06_E3 [⋀^Fin 2]→L[ℝ] ℝ

abbrev apm_t01J06_SphereForm2 :=
  ∀ q : apm_t01J06_S2,
    apm_t01J06_sphereTangent q [⋀^Fin 2]→L[ℝ] ℝ

abbrev apm_t01J06_ProductForm2 :=
  ∀ qp : apm_t01J06_S2 × apm_t01J06_S1,
    (apm_t01J06_sphereTangent qp.1 × apm_t01J06_circleTangent qp.2)
      [⋀^Fin 2]→L[ℝ] ℝ

def apm_t01J06_isOmega (omega : apm_t01J06_AmbientForm2) : Prop :=
  ∀ (x : apm_t01J06_E3) (v : Fin 2 → apm_t01J06_E3),
    omega x v = (x 2 + 3) * (v 0 0 * v 1 1 - v 0 1 * v 1 0)

def apm_t01J06_isInclusionPullback
    (omega : apm_t01J06_AmbientForm2)
    (alpha : apm_t01J06_SphereForm2) : Prop :=
  ∀ (q : apm_t01J06_S2)
      (v : Fin 2 → apm_t01J06_sphereTangent q),
    alpha q v = omega q (fun k ↦ (v k : apm_t01J06_E3))

def apm_t01J06_isJPullback
    (p : apm_t01J06_S1)
    (zeta : apm_t01J06_ProductForm2)
    (alpha : apm_t01J06_SphereForm2) : Prop :=
  ∀ (q : apm_t01J06_S2)
      (v : Fin 2 → apm_t01J06_sphereTangent q),
    zeta (q, p) (fun k ↦ (v k, 0)) = alpha q v

def apm_t01J06_tangentProjection (q : apm_t01J06_S2) (i : Fin 3) :
    apm_t01J06_sphereTangent q :=
  (apm_t01J06_sphereTangent q).orthogonalProjection
    (EuclideanSpace.single i 1)

def apm_t01J06_orientedCoefficient
    (alpha : apm_t01J06_SphereForm2) (q : apm_t01J06_S2) : ℝ :=
  (q : apm_t01J06_E3) 0 * alpha q ![apm_t01J06_tangentProjection q 1,
      apm_t01J06_tangentProjection q 2] -
  (q : apm_t01J06_E3) 1 * alpha q ![apm_t01J06_tangentProjection q 0,
      apm_t01J06_tangentProjection q 2] +
  (q : apm_t01J06_E3) 2 * alpha q ![apm_t01J06_tangentProjection q 0,
      apm_t01J06_tangentProjection q 1]

def apm_t01J06_sphereIntegral
    (alpha : apm_t01J06_SphereForm2) : ℝ :=
  ∫ q : apm_t01J06_S2, apm_t01J06_orientedCoefficient alpha q ∂μH[2]

def apm_t01J06_projectionPullback
    (alpha : apm_t01J06_SphereForm2) : apm_t01J06_ProductForm2 :=
  fun qp ↦ (alpha qp.1).compContinuousLinearMap
    (ContinuousLinearMap.fst ℝ (apm_t01J06_sphereTangent qp.1)
      (apm_t01J06_circleTangent qp.2))

lemma apm_t01J06_projectionPullback_isJPullback
    (alpha : apm_t01J06_SphereForm2) (p : apm_t01J06_S1) :
    apm_t01J06_isJPullback p (apm_t01J06_projectionPullback alpha) alpha := by
  intro q v
  rfl

theorem apm_t01j06
    (omega : apm_t01J06_AmbientForm2)
    (homega : apm_t01J06_isOmega omega)
    (alpha : apm_t01J06_SphereForm2)
    (halpha : apm_t01J06_isInclusionPullback omega alpha) :
    apm_t01J06_sphereIntegral alpha = 4 * Real.pi / 3 ∧
    ¬ (∃ eta : apm_t01J06_AmbientForm2,
        ContDiff ℝ (⊤ : ℕ∞) eta ∧
        extDeriv eta = 0 ∧
        apm_t01J06_isInclusionPullback eta alpha) ∧
    ∀ p : apm_t01J06_S1,
      ∃ zeta : apm_t01J06_ProductForm2,
        zeta = apm_t01J06_projectionPullback alpha ∧
        apm_t01J06_isJPullback p zeta alpha := by
  /-
  CLOSER HOP 1 boundary. The product-extension clause is now completely
  discharged at the definition level by
  `apm_t01J06_projectionPullback_isJPullback`: composing the alternating form
  with the first projection sends `(v, 0)` back to `v`.

  The first clause requires identifying the custom
  `apm_t01J06_orientedCoefficient` of the restricted ambient form and
  integrating it against `μH[2]` on the metric sphere. The intended Stokes
  argument reduces it to the volume of the unit 3-ball, but Mathlib has no
  integration theory for top-degree manifold differential forms and no
  manifold Stokes theorem connecting `extDeriv` to this Hausdorff-measure
  coefficient integral. Direct evaluation instead requires substantial
  orthogonal-projection coordinate algebra plus sphere moment integrals.

  The nonextension clause depends on the same absent bridge: a closed ambient
  extension would have zero integral over the sphere by Stokes, contradicting
  the computed nonzero period. `DifferentialForm.Basic` provides
  `extDeriv_pullback`, but not the global integral theorem required to turn
  closedness into vanishing of this frozen integral.

  Searches covered `LEMMA-INDEX.md`, every `ConstructionTargets/` module,
  closed form/integration siblings (`t92J09`, `t94J07`, `t94A10`, `t02A05`),
  Mathlib's differential-form, Hausdorff-measure, sphere-integral, divergence,
  and Stokes-related sources, and git history. The siblings independently
  record the same missing manifold-form integration interface. Thus the
  product pullback is closed, while the period and obstruction remain open.
  -/
  sorry
