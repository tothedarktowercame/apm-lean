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

lemma apm_t01J06_exists_projectionPullback
    (alpha : apm_t01J06_SphereForm2) (p : apm_t01J06_S1) :
    ∃ zeta : apm_t01J06_ProductForm2,
      zeta = apm_t01J06_projectionPullback alpha ∧
      apm_t01J06_isJPullback p zeta alpha := by
  exact ⟨apm_t01J06_projectionPullback alpha, rfl,
    apm_t01J06_projectionPullback_isJPullback alpha p⟩

/-- Restriction along the sphere inclusion determines the sphere form
pointwise. This isolates the remaining integral computation from any choice
of `alpha`. -/
lemma apm_t01J06_inclusionPullback_unique
    (omega : apm_t01J06_AmbientForm2)
    (alpha beta : apm_t01J06_SphereForm2)
    (halpha : apm_t01J06_isInclusionPullback omega alpha)
    (hbeta : apm_t01J06_isInclusionPullback omega beta) : alpha = beta := by
  funext q
  ext v
  exact (halpha q v).trans (hbeta q v).symm

/-- The coefficient specification determines the ambient form pointwise. -/
lemma apm_t01J06_isOmega_unique
    (omega eta : apm_t01J06_AmbientForm2)
    (homega : apm_t01J06_isOmega omega)
    (heta : apm_t01J06_isOmega eta) : omega = eta := by
  funext x
  ext v
  exact (homega x v).trans (heta x v).symm

/-- After restriction to the sphere, the supplied form has the same explicit
coordinate formula on tangent vectors. This removes `omega` and `alpha` as
unknowns from the remaining oriented-coefficient calculation. -/
lemma apm_t01J06_inclusionPullback_apply
    (omega : apm_t01J06_AmbientForm2)
    (homega : apm_t01J06_isOmega omega)
    (alpha : apm_t01J06_SphereForm2)
    (halpha : apm_t01J06_isInclusionPullback omega alpha)
    (q : apm_t01J06_S2)
    (v : Fin 2 → apm_t01J06_sphereTangent q) :
    alpha q v = ((q : apm_t01J06_E3) 2 + 3) *
      ((v 0 : apm_t01J06_E3) 0 * (v 1 : apm_t01J06_E3) 1 -
       (v 0 : apm_t01J06_E3) 1 * (v 1 : apm_t01J06_E3) 0) := by
  exact (halpha q v).trans (homega q (fun k ↦ (v k : apm_t01J06_E3)))

/-- The target period is strictly positive, so a future Stokes vanishing
result yields an immediate contradiction. -/
lemma apm_t01J06_target_period_pos : 0 < 4 * Real.pi / 3 := by positivity

/-- Why this unblocks `apm_t01j06`: this is the missing projection-coordinate
simplification together with the two-dimensional Hausdorff sphere-moment
calculation. It supplies the theorem's numerical period conjunct directly. -/
theorem apm_t01J06_bridge_sphereIntegral
    (omega : apm_t01J06_AmbientForm2)
    (homega : apm_t01J06_isOmega omega)
    (alpha : apm_t01J06_SphereForm2)
    (halpha : apm_t01J06_isInclusionPullback omega alpha) :
    apm_t01J06_sphereIntegral alpha = 4 * Real.pi / 3 := by
  sorry

/-- Why this unblocks `apm_t01j06`: this is Stokes' theorem specialized to
the frozen Hausdorff-measure encoding of the oriented unit-sphere integral.
A smooth closed ambient extension therefore forces the restricted period to
vanish, contradicting `apm_t01J06_bridge_sphereIntegral`. -/
theorem apm_t01J06_bridge_closed_extension_integral_zero
    (eta : apm_t01J06_AmbientForm2)
    (alpha : apm_t01J06_SphereForm2)
    (heta_smooth : ContDiff ℝ (⊤ : ℕ∞) eta)
    (heta_closed : extDeriv eta = 0)
    (heta_pullback : apm_t01J06_isInclusionPullback eta alpha) :
    apm_t01J06_sphereIntegral alpha = 0 := by
  sorry

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
  CLOSER HOP 2 boundary. The product-extension clause is now completely
  packaged, including its existential quantifier, by
  `apm_t01J06_exists_projectionPullback`: composing the alternating form with
  the first projection sends `(v, 0)` back to `v`. The new lemma
  `apm_t01J06_inclusionPullback_unique` also proves that restriction of a fixed
  ambient form determines `alpha` pointwise, so no freedom in the supplied
  sphere form can simplify or invalidate the period claim.

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

  Going beyond the prior Stokes-only route, I inspected Mathlib's box-integral
  divergence theorem and sphere path/measure APIs, plus the hop-2 direct-flux
  investigation in sibling `t02A05`. The divergence theorem is formulated for
  box integrals and does not identify this subtype Hausdorff integral; the
  sibling likewise stops at the missing radial-coordinate and sphere-moment
  formulas. Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`, the other
  closed-form siblings (`t92J09`, `t94J07`, `t94A10`), differential forms,
  Hausdorff measure, sphere integration, and git history still yield no
  bridge. Thus restriction uniqueness and the full product existential are
  closed, while the numerical period and Stokes obstruction remain open.

  CLOSER HOP 3: the remaining local form algebra is narrowed further.
  `apm_t01J06_isOmega_unique` proves the displayed coefficient condition
  determines the ambient alternating form pointwise, and
  `apm_t01J06_inclusionPullback_apply` substitutes that condition through the
  sphere inclusion to give the exact coordinate formula for `alpha` on all
  tangent vectors. Hence neither abstract form is an unknown in the remaining
  oriented-coefficient calculation. `apm_t01J06_target_period_pos` also
  compiles the nonvanishing fact needed after any future Stokes theorem.
  `LEMMA-INDEX.md` pointed to sibling `t92J09`'s `integral_form_on_sphere`, but
  inspection showed that helper computes ordinary unit-ball volume in an old
  canary, while its current main theorem is still sorry and uses a different
  parametrized integral; it cannot identify this Hausdorff subtype integral.
  Renewed searches of construction modules, sphere moments, orthogonal
  projection, differential-form integration, sibling artifacts, and git
  history found no further bridge. Projection-coordinate simplification plus
  Hausdorff sphere moments, and the global Stokes obstruction, remain open;
  the frozen statement is unchanged.
  -/
  sorry
