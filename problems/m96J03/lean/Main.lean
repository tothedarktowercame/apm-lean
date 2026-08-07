import Mathlib

/-!
# APM m96J03

## Statement repairs

The condition `f(x)=0` when `‖x‖>0` is corrected to `‖x‖>1`.
As printed, the two clauses overlap throughout `0 < ‖x‖ ≤ 1`; the correction
makes `f` the unit-ball indicator used by the supplied solution.

## Encoding questions

The distributional Laplacian is stated in its exact weak form. Surface measure
is `(n-1)`-dimensional Hausdorff measure restricted to the unit sphere, and the
outward normal there is the point `x` itself.
-/

open MeasureTheory
open scoped MeasureTheory

noncomputable section

abbrev apm_m96j03_E (n : ℕ) := EuclideanSpace ℝ (Fin n)

def apm_m96j03_ballIndicator {n : ℕ} (x : apm_m96j03_E n) : ℝ :=
  if ‖x‖ ≤ 1 then 1 else 0

def apm_m96j03_laplacian {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (x : apm_m96j03_E n) : ℝ :=
  ∑ i : Fin n,
    fderiv ℝ
      (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)

def apm_m96j03_IsTestFunction {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ

/-- The volume term in the weak Laplacian identity is exactly the integral
over the closed unit ball. -/
lemma apm_m96j03_integral_ballIndicator {n : ℕ}
    (g : apm_m96j03_E n → ℝ) :
    (∫ x, apm_m96j03_ballIndicator x * g x) =
      ∫ x in Metric.closedBall 0 1, g x := by
  rw [← MeasureTheory.integral_indicator measurableSet_closedBall]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  simp only [Set.indicator, apm_m96j03_ballIndicator, Metric.mem_closedBall,
    dist_zero_right]
  split_ifs <;> simp

/-- The flux identity in dimension zero is degenerate: the coordinate sum is
empty and the unit sphere in the zero-dimensional Euclidean space is empty. -/
lemma apm_m96j03_zero_dim (φ : apm_m96j03_E 0 → ℝ) :
    (∫ x : apm_m96j03_E 0,
        apm_m96j03_ballIndicator x * apm_m96j03_laplacian φ x) =
      ∫ x : apm_m96j03_E 0 in Metric.sphere 0 1,
        fderiv ℝ φ x x ∂μH[(0 - 1 : ℕ)] := by
  have hsphere : Metric.sphere (0 : apm_m96j03_E 0) 1 = ∅ := by
    ext x
    have hx : x = 0 := Subsingleton.elim x 0
    simp [hx]
  rw [hsphere]
  simp [apm_m96j03_laplacian]

theorem apm_m96j03
    (n : ℕ) (φ : apm_m96j03_E n → ℝ)
    (hφ : apm_m96j03_IsTestFunction φ) :
    (∫ x : apm_m96j03_E n,
        apm_m96j03_ballIndicator x * apm_m96j03_laplacian φ x) =
      ∫ x : apm_m96j03_E n in Metric.sphere 0 1,
        fderiv ℝ φ x x ∂μH[(n - 1 : ℕ)] := by
  rw [apm_m96j03_integral_ballIndicator]
  /-
  PARTIAL (closer hop 1, Gauss--Green theorem for a Euclidean ball).
  `apm_m96j03_zero_dim` now proves the complete degenerate `n = 0` identity:
  `Fin 0` makes the Laplacian sum empty, while the radius-one sphere in the
  subsingleton Euclidean space is empty.  Thus the remaining geometric bridge
  may be restricted to positive dimension.

  The helper
  `apm_m96j03_integral_ballIndicator` above proves the initial measurable-set
  reduction, so the remaining target is exactly

  `∫_ball Δφ = ∫_sphere Dφ(x)[x] dμH[n-1]`.

  Mathlib's `MeasureTheory.Integral.DivergenceTheorem` provides a Bochner
  divergence theorem only for rectangular boxes, with boundary terms written
  as integrals over coordinate faces.  It does not provide a smooth-domain,
  finite-perimeter, or ball-specialized Gauss--Green theorem, and the box
  result cannot be specialized to a sphere without a new approximation and
  boundary-convergence argument.

  A second route through polar coordinates was investigated.  Mathlib's
  `MeasureTheory.integral_fun_norm_addHaar` and
  `Measure.toSphere` give polar decomposition for radial integrands, and
  `ConstructionTargets.RadialIntegrationR3` specializes that identity in
  dimension three.  Here `apm_m96j03_laplacian φ` is not radial.  The polar
  route would therefore require proving that the spherical average of `Δφ`
  is the radial derivative of the averaged normal derivative, justifying two
  differentiations under the sphere integral, applying the one-dimensional
  fundamental theorem, and finally identifying the normalization of
  `volume.toSphere` with the frozen restricted Hausdorff measure
  `μH[n-1]` in every dimension.  No such identification/flux theorem was
  found in Mathlib or the corpus.

  `LEMMA-INDEX.md` exposed only radial-integration helpers.  The fully closed
  artifact scan found sphere and Hausdorff-measure developments but no flux
  identity.  Partial sibling `m99A02` stops at the analogous polar-coordinate
  and punctured-domain integration-by-parts boundary; `t01A06` and `t03J06`
  confirm that general surface/differential-form integration is not packaged
  for their encodings.  The remaining `ConstructionTargets/` modules and
  `YoungL2.lean` contain no relevant Gauss--Green result.  The statement
  appears mathematically correct.  A renewed search also inspected Mathlib's
  box divergence theorem, `HaarToSphere`, `VolumeOfBalls`, the specialized
  `ConstructionTargets.RadialIntegrationR3`, partial flux artifact `t02A05`,
  and git history.  None identifies `volume.toSphere` with the frozen
  restricted Hausdorff measure or supplies the nonradial sphere-flux identity.
  For positive dimension, proving the theorem still requires this missing
  geometric-measure interface.
  -/
  sorry
