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

/-- The frozen coordinate Laplacian vanishes on constant functions. -/
lemma apm_m96j03_laplacian_const {n : ℕ} (c : ℝ) (x : apm_m96j03_E n) :
    apm_m96j03_laplacian (fun _ ↦ c) x = 0 := by
  simp [apm_m96j03_laplacian]

/-- Under the smoothness available in the theorem, each frozen coordinate
term is exactly the corresponding diagonal value of the second iterated
Fréchet derivative. -/
lemma apm_m96j03_coordinate_second_derivative {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (x : apm_m96j03_E n) (i : Fin n) :
    fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) =
      iteratedFDeriv ℝ 2 φ x
        ![EuclideanSpace.single i 1, EuclideanSpace.single i 1] := by
  have h2 : ContDiff ℝ (2 : WithTop ℕ∞) φ :=
    hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (h2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  rw [fderiv_clm_apply (hd x) (by fun_prop)]
  simp [iteratedFDeriv_two_apply]

/-- The unit-ball indicator is measurable; this is needed before any
Gauss--Green approximation or dominated-convergence argument. -/
lemma apm_m96j03_measurable_ballIndicator {n : ℕ} :
    Measurable (apm_m96j03_ballIndicator : apm_m96j03_E n → ℝ) := by
  unfold apm_m96j03_ballIndicator
  have hmeas : Measurable fun x : apm_m96j03_E n ↦
      Set.indicator (Metric.closedBall 0 1) (fun _ ↦ (1 : ℝ)) x :=
    measurable_const.indicator measurableSet_closedBall
  convert hmeas using 1
  funext x
  simp [Set.indicator, Metric.mem_closedBall, dist_zero_right]

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

/-- Why this unblocks `apm_m96j03`: after
`apm_m96j03_integral_ballIndicator`, this is exactly the remaining
positive-dimensional goal.  It states the Euclidean unit-ball Gauss--Green
formula directly with the frozen restricted Hausdorff surface measure, so no
potentially misnormalized intermediate `Measure.toSphere` identification is
hidden in the bridge. -/
theorem apm_m96J03_bridge_1
    {n : ℕ} (hn : 0 < n) (φ : apm_m96j03_E n → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    (∫ x : apm_m96j03_E n in Metric.closedBall 0 1,
        apm_m96j03_laplacian φ x) =
      ∫ x : apm_m96j03_E n in Metric.sphere 0 1,
        fderiv ℝ φ x x ∂μH[(n - 1 : ℕ)] := by
  sorry

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

  Closer hop 2 compiles two prerequisites for an approximation route.
  `apm_m96j03_measurable_ballIndicator` identifies the frozen piecewise
  function with the measurable indicator of the closed ball, and
  `apm_m96j03_laplacian_const` verifies that the frozen coordinate Laplacian
  vanishes on constants in every dimension.

  I also investigated transporting the frozen coordinate sum directly to
  `InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis`. The two
  expressions are not definitionally equal: the frozen term differentiates
  each scalar evaluation `y ↦ fderiv φ y eᵢ`, whereas the intrinsic theorem
  differentiates the bundled map `fderiv φ`. A transport proof must apply
  `fderiv_clm_apply` under the `ContDiff` hypothesis before the geometric
  theorem can even be used. This analytic compatibility is a new, narrower
  sub-boundary beyond the measure-normalization issue recorded by hop 1.

  Closer hop 3 closes that analytic sub-boundary at its essential point.
  `apm_m96j03_coordinate_second_derivative` uses `ContDiff.fderiv_right` and
  `fderiv_clm_apply` to prove that every frozen coordinate term is exactly the
  corresponding diagonal evaluation of `iteratedFDeriv ℝ 2 φ`. Thus no
  differentiation-of-an-evaluation gap remains before summing coordinates.

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
  appears mathematically correct. Searches across both hops also inspected Mathlib's
  box divergence theorem, `HaarToSphere`, `VolumeOfBalls`, the specialized
  `ConstructionTargets.RadialIntegrationR3`, partial flux artifact `t02A05`,
  and git history.  None identifies `volume.toSphere` with the frozen
  restricted Hausdorff measure or supplies the nonradial sphere-flux identity.
  For positive dimension, proving the theorem still requires this missing
  geometric-measure interface.

  The final hop renewed searches in the Laplacian, iterated Fréchet
  derivative, `HaarToSphere`, Hausdorff-measure, and divergence-theorem
  sources, as well as the full lemma index and related flux artifacts. The
  calculus sources supplied the new coordinate compatibility lemma. No source
  supplied the ball Gauss--Green theorem or identified the frozen restricted
  Hausdorff surface measure with `volume.toSphere`; the theorem-level bridge
  remains open and the frozen statement is unchanged.
  -/
  sorry
