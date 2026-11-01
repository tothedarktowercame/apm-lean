import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import ConstructionTargets.IntrinsicSphereSecondMoments
import ConstructionTargets.EuclideanHausdorffSphereMass

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
  ∫ q, apm_t01J06_orientedCoefficient alpha q ∂μHE[2]

/-- Local projection-coordinate algebra. -/
theorem apm_t01J06_orientedCoefficient_eq
    (omega : apm_t01J06_AmbientForm2) (homega : apm_t01J06_isOmega omega)
    (alpha : apm_t01J06_SphereForm2)
    (halpha : apm_t01J06_isInclusionPullback omega alpha) (q : apm_t01J06_S2) :
    apm_t01J06_orientedCoefficient alpha q = (q.1 2 + 3) * q.1 2 := by
  have hq : ‖(q : apm_t01J06_E3)‖ = 1 := by
    have h := q.property
    simpa [Metric.mem_sphere, dist_eq_norm] using h
  have hproj (i j : Fin 3) :
      (apm_t01J06_tangentProjection q i : apm_t01J06_E3) j =
        (EuclideanSpace.single i 1 : apm_t01J06_E3) j - q.1 i * q.1 j := by
    change (((Submodule.span ℝ ({(q : apm_t01J06_E3)} : Set apm_t01J06_E3)).orthogonal
      ).orthogonalProjection (EuclideanSpace.single i 1) : apm_t01J06_E3) j = _
    change (((ℝ ∙ (q : apm_t01J06_E3))ᗮ.starProjection
      (EuclideanSpace.single i 1 : apm_t01J06_E3)) j) = _
    rw [Submodule.starProjection_orthogonal_val,
      Submodule.starProjection_singleton ℝ]
    rw [hq]
    simp only [one_pow, Nat.cast_one, div_one, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul]
    have hi : inner ℝ (q : apm_t01J06_E3)
        (EuclideanSpace.single i 1) = q.1 i := by
      simpa using EuclideanSpace.inner_single_right i (1 : ℝ)
        (q : apm_t01J06_E3)
    rw [hi]
    norm_num
  unfold apm_t01J06_orientedCoefficient
  rw [halpha, halpha, halpha, homega, homega, homega]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp_rw [hproj]
  simp
  have hnormsq : q.1 0 ^ 2 + q.1 1 ^ 2 + q.1 2 ^ 2 = 1 := by
    have h : ‖(q : apm_t01J06_E3)‖ ^ 2 = 1 := by rw [hq]; norm_num
    simpa only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, add_assoc,
      Real.norm_eq_abs, sq_abs] using h
  ring_nf at hnormsq ⊢

/-- Seat: the two moments for `μHE[2]`. `μHE[2]` is a positive multiple of `μH[2]`
(`Measure.euclideanHausdorffMeasure_def`). `IntrinsicSphereSecondMoments.square_moment` (with `d = 2`)
gives one third of the mass, `odd_integral` gives zero for the coordinate, and the mass is
`apm_t02a05_euclideanHausdorff_unitSphere_mass`. Integrability: bounded continuous on a compact space
of finite measure. If instances clash, see `apm_t02a05_radialFlux_integral_aux_inst` in
`problems/t02A05/lean/Main.lean`. -/
-- BEGIN SEAT AREA
theorem apm_t01J06_sphere_moments :
    Integrable (fun q : apm_t01J06_S2 ↦ q.1 2 ^ 2) μHE[2] ∧
    Integrable (fun q : apm_t01J06_S2 ↦ q.1 2) μHE[2] ∧
    (∫ q : apm_t01J06_S2, q.1 2 ^ 2 ∂μHE[2]) = 4 * Real.pi / 3 ∧
    (∫ q : apm_t01J06_S2, q.1 2 ∂μHE[2]) = 0 := by
  sorry
-- END SEAT AREA

/-- Unit vector `e i`. -/
abbrev apm_t01J06_e (i : Fin 3) : apm_t01J06_E3 := EuclideanSpace.single i 1

/-- Directional derivative in the coordinate `i`. -/
def apm_t01J06_partial (i : Fin 3) (f : apm_t01J06_E3 → ℝ) (x : apm_t01J06_E3) : ℝ :=
  fderiv ℝ f x (apm_t01J06_e i)

/-- The rotation field about the axis `k`, evaluated at `q`: the cross product `e k × q`. -/
def apm_t01J06_rotField (k : Fin 3) (q : apm_t01J06_E3) : apm_t01J06_E3 :=
  match k with
  | 0 => WithLp.toLp 2 ![0, -q 2, q 1]
  | 1 => WithLp.toLp 2 ![q 2, 0, -q 0]
  | 2 => WithLp.toLp 2 ![-q 1, q 0, 0]

/-- Seat: the sphere coefficient of a restricted form is the flux of its components. Same projection
expansion as `apm_t01J06_orientedCoefficient_eq`; the extra terms cancel by antisymmetry
(`AlternatingMap.map_swap`, `ContinuousAlternatingMap`). -/
theorem apm_t01J06_orientedCoefficient_flux
    (eta : apm_t01J06_AmbientForm2) (alpha : apm_t01J06_SphereForm2)
    (hp : apm_t01J06_isInclusionPullback eta alpha) (q : apm_t01J06_S2) :
    apm_t01J06_orientedCoefficient alpha q =
      q.1 0 * eta q ![apm_t01J06_e 1, apm_t01J06_e 2] -
      q.1 1 * eta q ![apm_t01J06_e 0, apm_t01J06_e 2] +
      q.1 2 * eta q ![apm_t01J06_e 0, apm_t01J06_e 1] := by
  sorry

/-- Seat: closedness in components. Evaluate `extDeriv_apply` on `![e 0, e 1, e 2]`, and use
`Fin.sum_univ_three` with the `Fin.removeNth` values. -/
theorem apm_t01J06_closed_divergence_free
    (eta : apm_t01J06_AmbientForm2) (hs : ContDiff ℝ (⊤ : ℕ∞) eta) (hc : extDeriv eta = 0)
    (x : apm_t01J06_E3) :
    apm_t01J06_partial 0 (fun y ↦ eta y ![apm_t01J06_e 1, apm_t01J06_e 2]) x -
      apm_t01J06_partial 1 (fun y ↦ eta y ![apm_t01J06_e 0, apm_t01J06_e 2]) x +
      apm_t01J06_partial 2 (fun y ↦ eta y ![apm_t01J06_e 0, apm_t01J06_e 1]) x = 0 := by
  sorry

/-- Seat: a divergence-free field is a curl. Take `A x = ∫ t in 0..1, t • (F (t x) × x)`. Differentiate
under the integral (`hasFDerivAt_integral_of_dominated_of_fderiv_le` or
`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`); then
`curl (t • F (t x) × x) = d/dt (t² F (t x))` using `div F = 0`, and the FTC gives `F x`. -/
theorem apm_t01J06_divergenceFree_isCurl (F : Fin 3 → apm_t01J06_E3 → ℝ)
    (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (hdiv : ∀ x, apm_t01J06_partial 0 (F 0) x + apm_t01J06_partial 1 (F 1) x +
      apm_t01J06_partial 2 (F 2) x = 0) :
    ∃ A : Fin 3 → apm_t01J06_E3 → ℝ, (∀ i, ContDiff ℝ 1 (A i)) ∧ ∀ x,
      F 0 x = apm_t01J06_partial 1 (A 2) x - apm_t01J06_partial 2 (A 1) x ∧
      F 1 x = apm_t01J06_partial 2 (A 0) x - apm_t01J06_partial 0 (A 2) x ∧
      F 2 x = apm_t01J06_partial 0 (A 1) x - apm_t01J06_partial 1 (A 0) x := by
  sorry

/-- Seat: rotation invariance. `t ↦ ∫ q, f (R t q)` is constant by
`IntrinsicSphereSecondMoments.integral_isometry` (with `R t` the rotation about axis `k`) and `μHE[2]`
a multiple of `μH[2]`. Its derivative at `0`, under the integral on the compact sphere, is the left side. -/
theorem apm_t01J06_rotation_derivative_integral (k : Fin 3) (f : apm_t01J06_E3 → ℝ)
    (hf : ContDiff ℝ 1 f) :
    (∫ q : apm_t01J06_S2, fderiv ℝ f q.1 (apm_t01J06_rotField k q.1) ∂μHE[2]) = 0 := by
  sorry

/-- Seat: the flux of a curl through the sphere vanishes. Pointwise,
`q · curl A = ∑ k, fderiv (A k) q (rotField k q)` (expand `fderiv` in the basis `e`, `Fin.sum_univ_three`). -/
theorem apm_t01J06_curl_flux_zero (A : Fin 3 → apm_t01J06_E3 → ℝ) (hA : ∀ i, ContDiff ℝ 1 (A i)) :
    (∫ q : apm_t01J06_S2,
      (q.1 0 * (apm_t01J06_partial 1 (A 2) q.1 - apm_t01J06_partial 2 (A 1) q.1) +
       q.1 1 * (apm_t01J06_partial 2 (A 0) q.1 - apm_t01J06_partial 0 (A 2) q.1) +
       q.1 2 * (apm_t01J06_partial 0 (A 1) q.1 - apm_t01J06_partial 1 (A 0) q.1)) ∂μHE[2]) = 0 := by
  sorry

/-- Seat: assembly of the Stokes obstruction. Take `F 0 = eta(e 1, e 2)`, `F 1 = -eta(e 0, e 2)`,
`F 2 = eta(e 0, e 1)`; they are smooth, `apm_t01J06_closed_divergence_free` gives `div F = 0`,
`apm_t01J06_divergenceFree_isCurl` gives `A`, `apm_t01J06_orientedCoefficient_flux` rewrites the integrand,
and `apm_t01J06_curl_flux_zero` finishes. -/
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
