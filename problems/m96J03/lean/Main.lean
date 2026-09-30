import Mathlib

/-!
# APM m96J03

## Statement repairs

The condition `f(x)=0` when `‖x‖>0` is corrected to `‖x‖>1`.
As printed, the two clauses overlap throughout `0 < ‖x‖ ≤ 1`; the correction
makes `f` the unit-ball indicator used by the supplied solution.

## Encoding questions

The distributional Laplacian is stated in its exact weak form: for every test
function φ, ∫ f Δφ = ∫_{S^{n-1}} ∂φ/∂ν dσ, i.e. Δf = −(∂/∂ν)(δ_{S^{n-1}}).
The outward normal at ω on the unit sphere is ω itself.

Surface measure σ is `volume.toSphere` (Mathlib's polar-coordinates measure:
σ(s) = n · vol{r ω : 0 < r < 1, ω ∈ s}, total mass n·vol(B) = |S^{n-1}|).
Until 2026-09-30 this was raw `μH[n-1]` on `Metric.sphere 0 1`. Mathlib's μH
is unnormalised (sum of diam^d), so for n = 3 it gives the unit sphere mass 16
rather than 4π, and the identity was false for n ≥ 3 (solve-loop strategy
note, 2026-09-30).
-/

open MeasureTheory
open scoped MeasureTheory Pointwise

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

/-- The zero-dimensional endpoint of the ball Green identity.  This also
checks that the chosen sphere measure and the frozen coordinate Laplacian
have compatible degenerate conventions. -/
lemma apm_m96j03_ball_green_zero
    (φ : apm_m96j03_E 0 → ℝ) :
    (∫ x : apm_m96j03_E 0,
        apm_m96j03_ballIndicator x * apm_m96j03_laplacian φ x) =
      ∫ ω : Metric.sphere (0 : apm_m96j03_E 0) 1,
        fderiv ℝ φ ω ω ∂(volume.toSphere) := by
  have hsphere : IsEmpty (Metric.sphere (0 : apm_m96j03_E 0) 1) := by
    constructor
    intro ω
    have hzero : (ω : apm_m96j03_E 0) = 0 := Subsingleton.elim _ _
    have hone : ‖(ω : apm_m96j03_E 0)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using ω.property
    simp [hzero] at hone
  letI : IsEmpty (Metric.sphere (0 : apm_m96j03_E 0) 1) := hsphere
  have hmeasure : (volume : Measure (apm_m96j03_E 0)).toSphere = 0 :=
    (Measure.toSphere_eq_zero_iff
      (volume : Measure (apm_m96j03_E 0))).mpr inferInstance
  rw [hmeasure]
  simp [apm_m96j03_laplacian]

/-- Polar-coordinate change of variables on punctured Euclidean space.  This
is the measure-theoretic layer needed before restricting the radial variable
to the unit ball. -/
lemma apm_m96j03_integral_polar_punctured {n : ℕ}
    (hn : 0 < n) (g : apm_m96j03_E n → ℝ) :
    (∫ x : ({0}ᶜ : Set (apm_m96j03_E n)), g x.1
        ∂((volume : Measure (apm_m96j03_E n)).comap Subtype.val)) =
      ∫ p : Metric.sphere (0 : apm_m96j03_E n) 1 × Set.Ioi (0 : ℝ),
        g (p.2.1 • p.1.1)
          ∂((volume : Measure (apm_m96j03_E n)).toSphere.prod
            (Measure.volumeIoiPow (n - 1))) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  letI : Nontrivial (apm_m96j03_E n) := inferInstance
  have h := MeasurePreserving.integral_comp
    (Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (apm_m96j03_E n)))
      (homeomorphUnitSphereProd (apm_m96j03_E n)).measurableEmbedding
      (g ∘ Subtype.val ∘ (homeomorphUnitSphereProd (apm_m96j03_E n)).symm)
  simpa only [Function.comp_apply, Homeomorph.symm_apply_apply,
    homeomorphUnitSphereProd_symm_apply_coe, finrank_euclideanSpace,
    Fintype.card_fin] using h

/-- Polar coordinates restricted to the open unit ball.  The origin can be
removed because Haar measure has no atoms, and the radial condition becomes
exactly `r < 1`. -/
lemma apm_m96j03_integral_ball_polar {n : ℕ}
    (hn : 0 < n) (g : apm_m96j03_E n → ℝ) :
    (∫ x in Metric.ball (0 : apm_m96j03_E n) 1, g x) =
      ∫ p : Metric.sphere (0 : apm_m96j03_E n) 1 × Set.Ioi (0 : ℝ),
        if p.2.1 < 1 then g (p.2.1 • p.1.1) else 0
          ∂((volume : Measure (apm_m96j03_E n)).toSphere.prod
            (Measure.volumeIoiPow (n - 1))) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  letI : Nontrivial (apm_m96j03_E n) := inferInstance
  have hpolar := apm_m96j03_integral_polar_punctured hn
    (Set.indicator (Metric.ball (0 : apm_m96j03_E n) 1) g)
  rw [integral_subtype_comap (measurableSet_singleton (0 : apm_m96j03_E n)).compl
    (Set.indicator (Metric.ball (0 : apm_m96j03_E n) 1) g),
    restrict_compl_singleton] at hpolar
  rw [← MeasureTheory.integral_indicator measurableSet_ball]
  refine hpolar.trans ?_
  apply integral_congr_ae
  filter_upwards with p
  simp only [Set.indicator, Metric.mem_ball, dist_zero_right]
  have hω : ‖(p.1.1 : apm_m96j03_E n)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using p.1.2
  have hr : 0 < p.2.1 := p.2.2
  rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos hr]

/-- For positive Euclidean dimension, replacing the closed unit ball by the
open unit ball does not change any Bochner integral. -/
lemma apm_m96j03_integral_closedBall_eq_ball {n : ℕ}
    (hn : 0 < n) (g : apm_m96j03_E n → ℝ) :
    (∫ x in Metric.closedBall (0 : apm_m96j03_E n) 1, g x) =
      ∫ x in Metric.ball (0 : apm_m96j03_E n) 1, g x := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  letI : Nontrivial (apm_m96j03_E n) := inferInstance
  have hae : Metric.closedBall (0 : apm_m96j03_E n) 1 =ᵐ[volume]
      Metric.ball 0 1 := by
    rw [ae_eq_set]
    constructor
    · rw [Metric.closedBall_diff_ball]
      exact Measure.addHaar_sphere
        (volume : Measure (apm_m96j03_E n)) 0 1
    · rw [(Set.diff_eq_empty).2 Metric.ball_subset_closedBall]
      simp
  rw [Measure.restrict_congr_set hae]

lemma apm_m96j03_integral_closedBall_polar {n : ℕ}
    (hn : 0 < n) (g : apm_m96j03_E n → ℝ) :
    (∫ x in Metric.closedBall (0 : apm_m96j03_E n) 1, g x) =
      ∫ p : Metric.sphere (0 : apm_m96j03_E n) 1 × Set.Ioi (0 : ℝ),
        if p.2.1 < 1 then g (p.2.1 • p.1.1) else 0
          ∂((volume : Measure (apm_m96j03_E n)).toSphere.prod
            (Measure.volumeIoiPow (n - 1))) := by
  rw [apm_m96j03_integral_closedBall_eq_ball hn]
  exact apm_m96j03_integral_ball_polar hn g

/-- Differentiating a smooth function along a radial line gives its Fréchet
derivative in the radial direction. -/
lemma apm_m96j03_hasDerivAt_radial {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (ω : apm_m96j03_E n) (r : ℝ) :
    HasDerivAt (fun s : ℝ ↦ φ (s • ω)) (fderiv ℝ φ (r • ω) ω) r := by
  have hline : HasDerivAt (fun s : ℝ ↦ s • ω) ω r :=
    by simpa using (hasDerivAt_id r).smul_const ω
  have houter : HasFDerivAt φ (fderiv ℝ φ (r • ω)) (r • ω) :=
    (hφ.differentiable (by simp) (r • ω)).hasFDerivAt
  simpa [Function.comp_def] using
    (houter.comp r hline.hasFDerivAt).hasDerivAt

/-- The diagonal second Fréchet derivative in an arbitrary direction, in
the concrete form used by radial differentiation. -/
lemma apm_m96j03_direction_second_derivative {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (x v : apm_m96j03_E n) :
    fderiv ℝ (fun y ↦ fderiv ℝ φ y v) x v =
      iteratedFDeriv ℝ 2 φ x ![v, v] := by
  have h2 : ContDiff ℝ (2 : WithTop ℕ∞) φ :=
    hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (h2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  rw [fderiv_clm_apply (hd x) (by fun_prop)]
  simp [iteratedFDeriv_two_apply]

/-- The second derivative along a radial line is the Hessian evaluated twice
in the radial direction. -/
lemma apm_m96j03_hasDerivAt_radial_fderiv {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (ω : apm_m96j03_E n) (r : ℝ) :
    HasDerivAt (fun s : ℝ ↦ fderiv ℝ φ (s • ω) ω)
      (iteratedFDeriv ℝ 2 φ (r • ω) ![ω, ω]) r := by
  have h2 : ContDiff ℝ (2 : WithTop ℕ∞) φ :=
    hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (h2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hψ : Differentiable ℝ (fun y ↦ fderiv ℝ φ y ω) := by
    fun_prop
  have hline : HasDerivAt (fun s : ℝ ↦ s • ω) ω r := by
    simpa using (hasDerivAt_id r).smul_const ω
  have hcomp :=
    ((hψ (r • ω)).hasFDerivAt.comp r hline.hasFDerivAt).hasDerivAt
  have hcomp' : HasDerivAt
      (fun s : ℝ ↦ fderiv ℝ φ (s • ω) ω)
      (fderiv ℝ (fun y ↦ fderiv ℝ φ y ω) (r • ω) ω) r := by
    simpa [Function.comp_def] using hcomp
  rw [apm_m96j03_direction_second_derivative φ hφ (r • ω) ω] at hcomp'
  exact hcomp'

/-- For a smooth function, the frozen coordinate definition of the
Laplacian is literally the trace of its second Fréchet derivative in the
standard Euclidean basis. -/
lemma apm_m96j03_laplacian_eq_trace_iteratedFDeriv {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (x : apm_m96j03_E n) :
    apm_m96j03_laplacian φ x =
      ∑ i : Fin n, iteratedFDeriv ℝ 2 φ x
        ![EuclideanSpace.single i 1, EuclideanSpace.single i 1] := by
  unfold apm_m96j03_laplacian
  apply Finset.sum_congr rfl
  intro i _
  exact apm_m96j03_coordinate_second_derivative φ hφ x i

/-- The frozen Laplacian of a test function is continuous.  In particular,
its restriction to every compact ball is integrable. -/
lemma apm_m96j03_continuous_laplacian {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    Continuous (apm_m96j03_laplacian φ) := by
  unfold apm_m96j03_laplacian
  apply continuous_finset_sum
  intro i _
  have h2 : ContDiff ℝ (2 : WithTop ℕ∞) φ :=
    hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hd : ContDiff ℝ 1 (fderiv ℝ φ) :=
    h2.fderiv_right (m := 1) (by norm_num)
  fun_prop

/-- The volume integrand in the ball Green identity is integrable on every
closed ball. -/
lemma apm_m96j03_laplacian_integrableOn_closedBall {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (R : ℝ) :
    IntegrableOn (apm_m96j03_laplacian φ)
      (Metric.closedBall (0 : apm_m96j03_E n) R) := by
  exact (apm_m96j03_continuous_laplacian φ hφ).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : apm_m96j03_E n) R)

/-- Smoothness is retained by the coordinate Laplacian.  This is the
regularity needed when the radial flux identity is differentiated repeatedly
or integrated parameterwise over the sphere. -/
lemma apm_m96j03_contDiff_laplacian {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (apm_m96j03_laplacian φ) := by
  unfold apm_m96j03_laplacian
  apply ContDiff.sum
  intro i _
  have hd₁ : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) :=
    hφ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have heval₁ : ContDiff ℝ (⊤ : ℕ∞)
      (fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
    fun_prop
  have hd₂ : ContDiff ℝ (⊤ : ℕ∞)
      (fderiv ℝ (fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1))) :=
    heval₁.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  fun_prop

/-- A linear isometry equivalence induces a measurable equivalence of the
unit sphere. -/
noncomputable def apm_m96j03_sphereIsometry {n : ℕ}
    (U : apm_m96j03_E n ≃ₗᵢ[ℝ] apm_m96j03_E n) :
    Metric.sphere (0 : apm_m96j03_E n) 1 ≃ᵐ
      Metric.sphere (0 : apm_m96j03_E n) 1 :=
  (Homeomorph.subtype U.toHomeomorph (fun x ↦ by
    simp only [Metric.mem_sphere, dist_zero_right]
    change ‖x‖ = 1 ↔ ‖U x‖ = 1
    rw [U.norm_map])).toMeasurableEquiv

@[simp]
lemma apm_m96j03_sphereIsometry_coe {n : ℕ}
    (U : apm_m96j03_E n ≃ₗᵢ[ℝ] apm_m96j03_E n)
    (ω : Metric.sphere (0 : apm_m96j03_E n) 1) :
    ((apm_m96j03_sphereIsometry U ω :
      Metric.sphere (0 : apm_m96j03_E n) 1) : apm_m96j03_E n) = U ω :=
  rfl

/-- A concrete nonidentity check for the induced sphere equivalence. -/
lemma apm_m96j03_sphereIsometry_neg_apply {n : ℕ}
    (ω : Metric.sphere (0 : apm_m96j03_E n) 1) :
    ((apm_m96j03_sphereIsometry (LinearIsometryEquiv.neg ℝ) ω :
      Metric.sphere (0 : apm_m96j03_E n) 1) : apm_m96j03_E n) = -ω := by
  rfl

@[simp]
lemma apm_m96j03_sphereIsometry_symm_coe {n : ℕ}
    (U : apm_m96j03_E n ≃ₗᵢ[ℝ] apm_m96j03_E n)
    (ω : Metric.sphere (0 : apm_m96j03_E n) 1) :
    (((apm_m96j03_sphereIsometry U).symm ω :
      Metric.sphere (0 : apm_m96j03_E n) 1) : apm_m96j03_E n) = U.symm ω :=
  rfl

/-- Orthogonal maps pull a truncated cone back to the truncated cone over the
inverse image on the unit sphere. -/
lemma apm_m96j03_sphereIsometry_preimage_cone {n : ℕ}
    (U : apm_m96j03_E n ≃ₗᵢ[ℝ] apm_m96j03_E n)
    (s : Set (Metric.sphere (0 : apm_m96j03_E n) 1)) :
    U ⁻¹' (Set.Ioo (0 : ℝ) 1 •
      ((fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦
        (ω : apm_m96j03_E n)) '' s)) =
      Set.Ioo (0 : ℝ) 1 •
        ((fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦
          (ω : apm_m96j03_E n)) ''
            ((apm_m96j03_sphereIsometry U) ⁻¹' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, y, ⟨ω, hω, rfl⟩, hxy⟩
    let ω' : Metric.sphere (0 : apm_m96j03_E n) 1 :=
      (apm_m96j03_sphereIsometry U).symm ω
    refine ⟨r, hr, (ω' : apm_m96j03_E n), ⟨ω', ?_, rfl⟩, ?_⟩
    · change apm_m96j03_sphereIsometry U ω' ∈ s
      simpa [ω'] using hω
    · apply U.injective
      simpa [ω'] using hxy
  · rintro ⟨r, hr, y, ⟨ω, hω, rfl⟩, hxy⟩
    refine ⟨r, hr, ((apm_m96j03_sphereIsometry U ω :
      Metric.sphere (0 : apm_m96j03_E n) 1) : apm_m96j03_E n),
      ⟨apm_m96j03_sphereIsometry U ω, hω, rfl⟩, ?_⟩
    simpa using congrArg U hxy

/-- The polar surface measure is invariant under every Euclidean linear
isometry. -/
lemma apm_m96j03_sphereIsometry_measurePreserving {n : ℕ}
    (U : apm_m96j03_E n ≃ₗᵢ[ℝ] apm_m96j03_E n) :
    MeasurePreserving (apm_m96j03_sphereIsometry U)
      (volume : Measure (apm_m96j03_E n)).toSphere
      (volume : Measure (apm_m96j03_E n)).toSphere := by
  refine ⟨(apm_m96j03_sphereIsometry U).measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (apm_m96j03_sphereIsometry U).measurable hs,
    Measure.toSphere_apply' _ hs,
    Measure.toSphere_apply' _
      ((apm_m96j03_sphereIsometry U).measurable hs)]
  congr 1
  rw [← apm_m96j03_sphereIsometry_preimage_cone U s]
  exact (LinearIsometryEquiv.measurePreserving U).measure_preimage_emb
    U.toHomeomorph.measurableEmbedding _

/-- Integral change of variables for the orthogonal action on the polar
surface measure. -/
lemma apm_m96j03_integral_sphereIsometry {n : ℕ}
    (U : apm_m96j03_E n ≃ₗᵢ[ℝ] apm_m96j03_E n)
    (g : Metric.sphere (0 : apm_m96j03_E n) 1 → ℝ) :
    (∫ ω, g (apm_m96j03_sphereIsometry U ω)
        ∂(volume : Measure (apm_m96j03_E n)).toSphere) =
      ∫ ω, g ω ∂(volume : Measure (apm_m96j03_E n)).toSphere := by
  exact (apm_m96j03_sphereIsometry_measurePreserving U).integral_comp
    (apm_m96j03_sphereIsometry U).measurableEmbedding g

/-- Every antipodally odd real function has zero integral on the unit sphere
for `volume.toSphere`. -/
lemma apm_m96j03_integral_sphere_eq_zero_of_odd {n : ℕ}
    (g : Metric.sphere (0 : apm_m96j03_E n) 1 → ℝ)
    (hodd : ∀ ω, g (apm_m96j03_sphereIsometry
      (LinearIsometryEquiv.neg ℝ) ω) = -g ω) :
    (∫ ω, g ω ∂(volume : Measure (apm_m96j03_E n)).toSphere) = 0 := by
  have hinv := apm_m96j03_integral_sphereIsometry
    (LinearIsometryEquiv.neg ℝ :
      apm_m96j03_E n ≃ₗᵢ[ℝ] apm_m96j03_E n) g
  simp_rw [hodd] at hinv
  rw [integral_neg] at hinv
  linarith

/-- The first moment of the polar surface measure vanishes in every
direction. -/
lemma apm_m96j03_integral_sphere_inner_eq_zero {n : ℕ}
    (v : apm_m96j03_E n) :
    (∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        inner ℝ v (ω : apm_m96j03_E n)
        ∂(volume : Measure (apm_m96j03_E n)).toSphere) = 0 := by
  apply apm_m96j03_integral_sphere_eq_zero_of_odd
  intro ω
  simp

/-- The Euclidean isometry which changes the sign of one standard
coordinate and fixes all the others. -/
noncomputable def apm_m96j03_coordinateSignFlip {n : ℕ} (i : Fin n) :
    apm_m96j03_E n ≃ₗᵢ[ℝ] apm_m96j03_E n :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun j : Fin n ↦
    if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

@[simp]
lemma apm_m96j03_coordinateSignFlip_apply {n : ℕ} (i j : Fin n)
    (x : apm_m96j03_E n) :
    apm_m96j03_coordinateSignFlip i x j = if j = i then -x j else x j := by
  by_cases hji : j = i <;>
    simp [apm_m96j03_coordinateSignFlip,
      LinearIsometryEquiv.piLpCongrRight_apply, hji]

/-- A concrete nontriviality check for the coordinate sign flip. -/
lemma apm_m96j03_coordinateSignFlip_single {n : ℕ} (i : Fin n) :
    apm_m96j03_coordinateSignFlip i (EuclideanSpace.single i 1) =
      -(EuclideanSpace.single i 1) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji, EuclideanSpace.single_apply]

/-- Distinct standard coordinates have zero mixed second moment on the unit
sphere. -/
lemma apm_m96j03_integral_sphere_coordinate_mul_eq_zero {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) :
    (∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        (ω : apm_m96j03_E n) i * (ω : apm_m96j03_E n) j
        ∂(volume : Measure (apm_m96j03_E n)).toSphere) = 0 := by
  have hinv := apm_m96j03_integral_sphereIsometry
    (apm_m96j03_coordinateSignFlip i)
    (fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦
      (ω : apm_m96j03_E n) i * (ω : apm_m96j03_E n) j)
  simp only [apm_m96j03_sphereIsometry_coe,
    apm_m96j03_coordinateSignFlip_apply] at hinv
  simp [hij, Ne.symm hij, integral_neg] at hinv
  linarith

/-- The Euclidean isometry which exchanges two standard coordinates. -/
noncomputable def apm_m96j03_coordinateSwap {n : ℕ} (i j : Fin n) :
    apm_m96j03_E n ≃ₗᵢ[ℝ] apm_m96j03_E n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)

@[simp]
lemma apm_m96j03_coordinateSwap_apply {n : ℕ} (i j k : Fin n)
    (x : apm_m96j03_E n) :
    apm_m96j03_coordinateSwap i j x k = x (Equiv.swap i j k) := by
  simp [apm_m96j03_coordinateSwap,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

/-- A concrete check that the swap sends the `i`th standard vector to the
`j`th one. -/
lemma apm_m96j03_coordinateSwap_single {n : ℕ} (i j : Fin n) :
    apm_m96j03_coordinateSwap i j (EuclideanSpace.single i 1) =
      EuclideanSpace.single j 1 := by
  simpa [apm_m96j03_coordinateSwap] using
    (LinearIsometryEquiv.piLpCongrLeft_single (p := 2) (E := ℝ)
      (Equiv.swap i j) i (1 : ℝ))

/-- All standard coordinates have the same diagonal second moment.  This is
a normalization check for the sphere measure; the Green identity itself uses
the stronger infinitesimal-rotation argument. -/
lemma apm_m96j03_integral_sphere_coordinate_sq_eq {n : ℕ} (i j : Fin n) :
    (∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        ((ω : apm_m96j03_E n) i) ^ 2
        ∂(volume : Measure (apm_m96j03_E n)).toSphere) =
      ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        ((ω : apm_m96j03_E n) j) ^ 2
        ∂(volume : Measure (apm_m96j03_E n)).toSphere := by
  have hinv := apm_m96j03_integral_sphereIsometry
    (apm_m96j03_coordinateSwap i j)
    (fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦
      ((ω : apm_m96j03_E n) i) ^ 2)
  simpa using hinv.symm

/-- The unit vector at half-angle `t / 2` in the oriented `(i,j)` coordinate
plane.  Two reflections in the lines at angles `0` and `t / 2` generate the
desired rotation by `t`. -/
noncomputable def apm_m96j03_rotationDirection {n : ℕ}
    (i j : Fin n) (t : ℝ) : apm_m96j03_E n :=
  Real.cos (t / 2) • EuclideanSpace.single i 1 +
    Real.sin (t / 2) • EuclideanSpace.single j 1

@[simp]
lemma apm_m96j03_rotationDirection_apply {n : ℕ}
    (i j k : Fin n) (t : ℝ) :
    apm_m96j03_rotationDirection i j t k =
      Real.cos (t / 2) * (if k = i then 1 else 0) +
        Real.sin (t / 2) * (if k = j then 1 else 0) := by
  simp [apm_m96j03_rotationDirection, PiLp.single_apply]

/-- Concrete non-vacuity check for the rotating direction. -/
@[simp]
lemma apm_m96j03_rotationDirection_zero {n : ℕ} (i j : Fin n) :
    apm_m96j03_rotationDirection i j 0 = EuclideanSpace.single i 1 := by
  simp [apm_m96j03_rotationDirection]

lemma apm_m96j03_rotationDirection_norm {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (t : ℝ) :
    ‖apm_m96j03_rotationDirection i j t‖ = 1 := by
  have hsingle : inner ℝ (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single j (1 : ℝ)) = 0 := by
    exact (EuclideanSpace.orthonormal_single (𝕜 := ℝ)).inner_eq_zero hij
  have horth : inner ℝ
      (Real.cos (t / 2) • EuclideanSpace.single i (1 : ℝ))
      (Real.sin (t / 2) • EuclideanSpace.single j (1 : ℝ)) = 0 := by
    simp [inner_smul_left, inner_smul_right, hsingle]
  have hsquare := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  simp only [norm_smul, PiLp.norm_single, norm_one, mul_one,
    Real.norm_eq_abs] at hsquare
  have habs (x : ℝ) : |x| * |x| = x ^ 2 := by
    rw [← abs_mul]
    simp [pow_two]
  rw [habs, habs] at hsquare
  change ‖apm_m96j03_rotationDirection i j t‖ *
      ‖apm_m96j03_rotationDirection i j t‖ = _ at hsquare
  nlinarith [Real.sin_sq_add_cos_sq (t / 2),
    norm_nonneg (apm_m96j03_rotationDirection i j t)]

/-- Rotation in the `(i,j)` coordinate plane, realized as the composition of
reflections in the line through `e_i` and the line at half-angle `t / 2`. -/
noncomputable def apm_m96j03_coordinateRotation {n : ℕ}
    (i j : Fin n) (t : ℝ) :
    apm_m96j03_E n ≃ₗᵢ[ℝ] apm_m96j03_E n :=
  ( ℝ ∙ EuclideanSpace.single i (1 : ℝ)).reflection |>.trans
    (ℝ ∙ apm_m96j03_rotationDirection i j t).reflection

/-- At parameter zero the two reflecting lines coincide, so their
composition is the identity. -/
@[simp]
lemma apm_m96j03_coordinateRotation_zero {n : ℕ} (i j : Fin n) :
    apm_m96j03_coordinateRotation i j 0 =
      LinearIsometryEquiv.refl ℝ (apm_m96j03_E n) := by
  simp [apm_m96j03_coordinateRotation]

/-- Expansion of the two-reflection rotation into rank-one projection
formulas.  This is the algebraic starting point for its coordinate and
parameter-derivative formulas. -/
lemma apm_m96j03_coordinateRotation_apply {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (t : ℝ) (x : apm_m96j03_E n) :
    apm_m96j03_coordinateRotation i j t x =
      2 • (inner ℝ (apm_m96j03_rotationDirection i j t)
          (2 • (inner ℝ (EuclideanSpace.single i (1 : ℝ)) x •
            EuclideanSpace.single i 1) - x) •
        apm_m96j03_rotationDirection i j t) -
      (2 • (inner ℝ (EuclideanSpace.single i (1 : ℝ)) x •
        EuclideanSpace.single i 1) - x) := by
  rw [apm_m96j03_coordinateRotation]
  simp only [LinearIsometryEquiv.trans_apply,
    Submodule.reflection_singleton_apply]
  rw [apm_m96j03_rotationDirection_norm i j hij t]
  simp [PiLp.norm_single]

set_option maxHeartbeats 800000 in
/-- The half-angle unit direction has velocity `e_j / 2` at zero. -/
lemma apm_m96j03_rotationDirection_hasDerivAt_zero {n : ℕ}
    (i j : Fin n) :
    HasDerivAt (fun t : ℝ ↦ apm_m96j03_rotationDirection i j t)
      ((1 / 2 : ℝ) • EuclideanSpace.single j 1) 0 := by
  unfold apm_m96j03_rotationDirection
  have hc : HasDerivAt (fun t : ℝ ↦ Real.cos (t / 2)) 0 0 := by
    convert (Real.hasDerivAt_cos ((0 : ℝ) / 2)).comp 0
      ((hasDerivAt_id (0 : ℝ)).div_const (2 : ℝ)) using 1 <;> norm_num
  have hs : HasDerivAt (fun t : ℝ ↦ Real.sin (t / 2)) (1 / 2) 0 := by
    convert (Real.hasDerivAt_sin ((0 : ℝ) / 2)).comp 0
      ((hasDerivAt_id (0 : ℝ)).div_const (2 : ℝ)) using 1 <;> norm_num
  simpa only [zero_smul, zero_add] using
    (hc.smul_const (EuclideanSpace.single i (1 : ℝ))).add
      (hs.smul_const (EuclideanSpace.single j (1 : ℝ)))

/-- Parameter derivative of the rotating unit direction at an arbitrary
angle. -/
lemma apm_m96j03_rotationDirection_hasDerivAt {n : ℕ}
    (i j : Fin n) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ apm_m96j03_rotationDirection i j s)
      ((-(Real.sin (t / 2)) / 2) • EuclideanSpace.single i 1 +
        (Real.cos (t / 2) / 2) • EuclideanSpace.single j 1) t := by
  unfold apm_m96j03_rotationDirection
  have hc : HasDerivAt (fun s : ℝ ↦ Real.cos (s / 2))
      (-(Real.sin (t / 2)) / 2) t := by
    convert (Real.hasDerivAt_cos (t / 2)).comp t
      ((hasDerivAt_id t).div_const (2 : ℝ)) using 1 <;> ring
  have hs : HasDerivAt (fun s : ℝ ↦ Real.sin (s / 2))
      (Real.cos (t / 2) / 2) t := by
    convert (Real.hasDerivAt_sin (t / 2)).comp t
      ((hasDerivAt_id t).div_const (2 : ℝ)) using 1 <;> ring
  exact
    (hc.smul_const (EuclideanSpace.single i (1 : ℝ))).add
      (hs.smul_const (EuclideanSpace.single j (1 : ℝ)))

/-- The rotating half-angle direction has constant speed `1/2`. -/
lemma apm_m96j03_rotationDirection_deriv_norm {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (t : ℝ) :
    ‖((-(Real.sin (t / 2)) / 2) • EuclideanSpace.single i (1 : ℝ) +
        (Real.cos (t / 2) / 2) • EuclideanSpace.single j 1 :
        apm_m96j03_E n)‖ = 1 / 2 := by
  have hsingle : inner ℝ (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single j (1 : ℝ)) = 0 :=
    (EuclideanSpace.orthonormal_single (𝕜 := ℝ)).inner_eq_zero hij
  have horth : inner ℝ
      ((-(Real.sin (t / 2)) / 2) • EuclideanSpace.single i (1 : ℝ))
      ((Real.cos (t / 2) / 2) • EuclideanSpace.single j (1 : ℝ)) = 0 := by
    simp [inner_smul_left, inner_smul_right, hsingle]
  have hsquare := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  simp only [norm_smul, PiLp.norm_single, norm_one, mul_one,
    Real.norm_eq_abs] at hsquare
  have habs (x : ℝ) : |x| * |x| = x ^ 2 := by
    rw [← abs_mul]
    simp [pow_two]
  rw [habs, habs] at hsquare
  change ‖((-(Real.sin (t / 2)) / 2) • EuclideanSpace.single i (1 : ℝ) +
      (Real.cos (t / 2) / 2) • EuclideanSpace.single j 1 :
      apm_m96j03_E n)‖ * ‖_‖ = _ at hsquare
  have htrig := Real.sin_sq_add_cos_sq (t / 2)
  have hnonneg := norm_nonneg
    (((-(Real.sin (t / 2)) / 2) • EuclideanSpace.single i (1 : ℝ) +
      (Real.cos (t / 2) / 2) • EuclideanSpace.single j 1) :
      apm_m96j03_E n)
  norm_num at hsquare ⊢
  nlinarith

/-- The fixed first-reflection vector occurring in the rank-one rotation
formula has the same norm as the original vector. -/
lemma apm_m96j03_firstReflection_norm {n : ℕ}
    (i : Fin n) (x : apm_m96j03_E n) :
    ‖2 • (inner ℝ (EuclideanSpace.single i (1 : ℝ)) x •
        EuclideanSpace.single i 1) - x‖ = ‖x‖ := by
  have hreflect :=
    (ℝ ∙ EuclideanSpace.single i (1 : ℝ)).reflection.norm_map x
  rw [Submodule.reflection_singleton_apply] at hreflect
  simpa [PiLp.norm_single] using hreflect

/-- Uniform norm bound for the velocity of the coordinate rotation. -/
lemma apm_m96j03_coordinateRotation_velocity_norm_le {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (x : apm_m96j03_E n) (t : ℝ) :
    ‖2 •
        (inner ℝ
            ((-(Real.sin (t / 2)) / 2) • EuclideanSpace.single i 1 +
              (Real.cos (t / 2) / 2) • EuclideanSpace.single j 1)
            (2 • (inner ℝ (EuclideanSpace.single i (1 : ℝ)) x •
              EuclideanSpace.single i 1) - x) •
            apm_m96j03_rotationDirection i j t +
          inner ℝ (apm_m96j03_rotationDirection i j t)
            (2 • (inner ℝ (EuclideanSpace.single i (1 : ℝ)) x •
              EuclideanSpace.single i 1) - x) •
            ((-(Real.sin (t / 2)) / 2) • EuclideanSpace.single i 1 +
              (Real.cos (t / 2) / 2) • EuclideanSpace.single j 1))‖
      ≤ 2 * ‖x‖ := by
  let u : apm_m96j03_E n := apm_m96j03_rotationDirection i j t
  let du : apm_m96j03_E n :=
    (-(Real.sin (t / 2)) / 2) • EuclideanSpace.single i 1 +
      (Real.cos (t / 2) / 2) • EuclideanSpace.single j 1
  let v : apm_m96j03_E n :=
    2 • (inner ℝ (EuclideanSpace.single i (1 : ℝ)) x •
      EuclideanSpace.single i 1) - x
  have hu : ‖u‖ = 1 := apm_m96j03_rotationDirection_norm i j hij t
  have hdu : ‖du‖ = 1 / 2 :=
    apm_m96j03_rotationDirection_deriv_norm i j hij t
  have hv : ‖v‖ = ‖x‖ := apm_m96j03_firstReflection_norm i x
  change ‖2 • (inner ℝ du v • u + inner ℝ u v • du)‖ ≤ 2 * ‖x‖
  calc
    ‖2 • (inner ℝ du v • u + inner ℝ u v • du)‖ =
        ‖(2 : ℝ) • (inner ℝ du v • u + inner ℝ u v • du)‖ := by
          congr 1
          module
    _ = 2 * ‖inner ℝ du v • u + inner ℝ u v • du‖ := by
      rw [norm_smul]
      norm_num
    _ ≤ 2 * (‖inner ℝ du v • u‖ + ‖inner ℝ u v • du‖) := by
      gcongr
      exact norm_add_le _ _
    _ = 2 * (|inner ℝ du v| * ‖u‖ + |inner ℝ u v| * ‖du‖) := by
      simp [norm_smul, Real.norm_eq_abs]
    _ ≤ 2 * ((‖du‖ * ‖v‖) * ‖u‖ + (‖u‖ * ‖v‖) * ‖du‖) := by
      gcongr
      · exact abs_real_inner_le_norm du v
      · exact abs_real_inner_le_norm u v
    _ = 2 * ‖x‖ := by rw [hu, hdu, hv]; ring

/-- Product-rule derivative of the two-reflection rotation at an arbitrary
parameter. -/
lemma apm_m96j03_coordinateRotation_hasDerivAt_raw {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (x : apm_m96j03_E n) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ apm_m96j03_coordinateRotation i j s x)
      (2 •
        (inner ℝ
            ((-(Real.sin (t / 2)) / 2) • EuclideanSpace.single i 1 +
              (Real.cos (t / 2) / 2) • EuclideanSpace.single j 1)
            (2 • (inner ℝ (EuclideanSpace.single i (1 : ℝ)) x •
              EuclideanSpace.single i 1) - x) •
            apm_m96j03_rotationDirection i j t +
          inner ℝ (apm_m96j03_rotationDirection i j t)
            (2 • (inner ℝ (EuclideanSpace.single i (1 : ℝ)) x •
              EuclideanSpace.single i 1) - x) •
            ((-(Real.sin (t / 2)) / 2) • EuclideanSpace.single i 1 +
              (Real.cos (t / 2) / 2) • EuclideanSpace.single j 1))) t := by
  let u : ℝ → apm_m96j03_E n := fun s ↦
    apm_m96j03_rotationDirection i j s
  let du : apm_m96j03_E n :=
    (-(Real.sin (t / 2)) / 2) • EuclideanSpace.single i 1 +
      (Real.cos (t / 2) / 2) • EuclideanSpace.single j 1
  let v : apm_m96j03_E n :=
    2 • (inner ℝ (EuclideanSpace.single i (1 : ℝ)) x •
      EuclideanSpace.single i 1) - x
  have hu : HasDerivAt u du t :=
    apm_m96j03_rotationDirection_hasDerivAt i j t
  have hi : HasDerivAt (fun s ↦ inner ℝ (u s) v) (inner ℝ du v) t := by
    have h := (((innerSL ℝ) v).hasFDerivAt.comp t hu.hasFDerivAt).hasDerivAt
    simpa [real_inner_comm] using h
  have hraw := ((hi.smul hu).const_smul (2 : ℝ)).sub
    (hasDerivAt_const (x := t) v)
  convert hraw using 1
  · funext s
    rw [apm_m96j03_coordinateRotation_apply i j hij s x]
    simp [u, v]
    module
  · simp [u, du, v]
    module

/-- Velocity field of the coordinate-plane rotation. -/
noncomputable def apm_m96j03_coordinateRotationVelocity {n : ℕ}
    (i j : Fin n) (t : ℝ) (x : apm_m96j03_E n) : apm_m96j03_E n :=
  2 •
    (inner ℝ
        ((-(Real.sin (t / 2)) / 2) • EuclideanSpace.single i 1 +
          (Real.cos (t / 2) / 2) • EuclideanSpace.single j 1)
        (2 • (inner ℝ (EuclideanSpace.single i (1 : ℝ)) x •
          EuclideanSpace.single i 1) - x) •
        apm_m96j03_rotationDirection i j t +
      inner ℝ (apm_m96j03_rotationDirection i j t)
        (2 • (inner ℝ (EuclideanSpace.single i (1 : ℝ)) x •
          EuclideanSpace.single i 1) - x) •
        ((-(Real.sin (t / 2)) / 2) • EuclideanSpace.single i 1 +
          (Real.cos (t / 2) / 2) • EuclideanSpace.single j 1))

lemma apm_m96j03_coordinateRotation_hasDerivAt {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (x : apm_m96j03_E n) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ apm_m96j03_coordinateRotation i j s x)
      (apm_m96j03_coordinateRotationVelocity i j t x) t := by
  simpa [apm_m96j03_coordinateRotationVelocity] using
    apm_m96j03_coordinateRotation_hasDerivAt_raw i j hij x t

lemma apm_m96j03_comp_coordinateRotation_hasDerivAt {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (g : apm_m96j03_E n → ℝ)
    (x : apm_m96j03_E n) (t : ℝ)
    (hg : DifferentiableAt ℝ g (apm_m96j03_coordinateRotation i j t x)) :
    HasDerivAt (fun s : ℝ ↦ g (apm_m96j03_coordinateRotation i j s x))
      (fderiv ℝ g (apm_m96j03_coordinateRotation i j t x)
        (apm_m96j03_coordinateRotationVelocity i j t x)) t := by
  simpa [Function.comp_def] using
    (hg.hasFDerivAt.comp t
      (apm_m96j03_coordinateRotation_hasDerivAt i j hij x t).hasFDerivAt).hasDerivAt

/-- Product-rule form of the infinitesimal generator of the two-reflection
rotation. -/
lemma apm_m96j03_coordinateRotation_hasDerivAt_zero_raw {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (x : apm_m96j03_E n) :
    HasDerivAt (fun t : ℝ ↦ apm_m96j03_coordinateRotation i j t x)
      (2 •
        (inner ℝ (EuclideanSpace.single i (1 : ℝ))
            (2 • (inner ℝ (EuclideanSpace.single i (1 : ℝ)) x •
              EuclideanSpace.single i 1) - x) •
            ((1 / 2 : ℝ) • EuclideanSpace.single j 1) +
          inner ℝ ((1 / 2 : ℝ) • EuclideanSpace.single j 1)
            (2 • (inner ℝ (EuclideanSpace.single i (1 : ℝ)) x •
              EuclideanSpace.single i 1) - x) •
            EuclideanSpace.single i 1)) 0 := by
  let u : ℝ → apm_m96j03_E n := fun t ↦
    apm_m96j03_rotationDirection i j t
  let v : apm_m96j03_E n :=
    2 • (inner ℝ (EuclideanSpace.single i (1 : ℝ)) x •
      EuclideanSpace.single i 1) - x
  have hu : HasDerivAt u
      ((1 / 2 : ℝ) • EuclideanSpace.single j 1) 0 :=
    apm_m96j03_rotationDirection_hasDerivAt_zero i j
  have hi : HasDerivAt (fun t ↦ inner ℝ (u t) v)
      (inner ℝ ((1 / 2 : ℝ) • EuclideanSpace.single j 1) v) 0 := by
    have h := (((innerSL ℝ) v).hasFDerivAt.comp 0 hu.hasFDerivAt).hasDerivAt
    simpa [real_inner_comm] using h
  have hprod := hi.smul hu
  have hraw := (hprod.const_smul (2 : ℝ)).sub
    (hasDerivAt_const (x := (0 : ℝ)) v)
  convert hraw using 1
  · funext t
    rw [apm_m96j03_coordinateRotation_apply i j hij t x]
    simp [u, v]
    module
  · simp [u, v]
    module

/-- The infinitesimal velocity of the coordinate-plane rotation.  With the
chosen order of the two reflections its generator sends `x` to
`x i * e_j - x j * e_i`. -/
lemma apm_m96j03_coordinateRotation_hasDerivAt_zero {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (x : apm_m96j03_E n) :
    HasDerivAt (fun t : ℝ ↦ apm_m96j03_coordinateRotation i j t x)
      (x i • EuclideanSpace.single j 1 -
        x j • EuclideanSpace.single i 1) 0 := by
  convert apm_m96j03_coordinateRotation_hasDerivAt_zero_raw i j hij x using 1
  have hei (y : apm_m96j03_E n) :
      inner ℝ (EuclideanSpace.single i (1 : ℝ)) y = y i := by
    simpa using EuclideanSpace.inner_single_left i (1 : ℝ) y
  have hej (y : apm_m96j03_E n) :
      inner ℝ (EuclideanSpace.single j (1 : ℝ)) y = y j := by
    simpa using EuclideanSpace.inner_single_left j (1 : ℝ) y
  simp_rw [hei]
  simp only [inner_smul_left]
  simp_rw [hej]
  simp [two_smul, PiLp.single_apply, hij, Ne.symm hij]
  module

/-- Concrete non-vacuity check and sign convention for the packaged rotation
velocity. -/
@[simp]
lemma apm_m96j03_coordinateRotationVelocity_zero {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (x : apm_m96j03_E n) :
    apm_m96j03_coordinateRotationVelocity i j 0 x =
      x i • EuclideanSpace.single j 1 -
        x j • EuclideanSpace.single i 1 := by
  exact (apm_m96j03_coordinateRotation_hasDerivAt i j hij x 0).unique
    (apm_m96j03_coordinateRotation_hasDerivAt_zero i j hij x)

lemma apm_m96j03_coordinateRotationVelocity_norm_le {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (x : apm_m96j03_E n) (t : ℝ) :
    ‖apm_m96j03_coordinateRotationVelocity i j t x‖ ≤ 2 * ‖x‖ := by
  simpa [apm_m96j03_coordinateRotationVelocity] using
    apm_m96j03_coordinateRotation_velocity_norm_le i j hij x t

/-- Chain rule for a smooth scalar function along the coordinate rotation. -/
lemma apm_m96j03_comp_coordinateRotation_hasDerivAt_zero {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (g : apm_m96j03_E n → ℝ)
    (x : apm_m96j03_E n) (hg : DifferentiableAt ℝ g x) :
    HasDerivAt (fun t : ℝ ↦ g (apm_m96j03_coordinateRotation i j t x))
      (fderiv ℝ g x
        (x i • EuclideanSpace.single j 1 -
          x j • EuclideanSpace.single i 1)) 0 := by
  have hrot := apm_m96j03_coordinateRotation_hasDerivAt_zero i j hij x
  have hg0 : HasFDerivAt g (fderiv ℝ g x)
      (apm_m96j03_coordinateRotation i j 0 x) := by
    simpa using hg.hasFDerivAt
  have hcomp := (hg0.comp 0 hrot.hasFDerivAt).hasDerivAt
  simpa using hcomp

/-- The operator norm of the derivative of a smooth scalar function is
uniformly bounded on the compact unit sphere. -/
lemma apm_m96j03_exists_fderiv_norm_bound_on_sphere {n : ℕ}
    (g : apm_m96j03_E n → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Metric.sphere (0 : apm_m96j03_E n) 1,
      ‖fderiv ℝ g x‖ ≤ C := by
  have hcont : Continuous (fun x : apm_m96j03_E n ↦ ‖fderiv ℝ g x‖) :=
    (hg.continuous_fderiv (by simp)).norm
  have hbdd : BddAbove
      ((fun x : apm_m96j03_E n ↦ ‖fderiv ℝ g x‖) ''
        Metric.sphere (0 : apm_m96j03_E n) 1) :=
    (isCompact_sphere (0 : apm_m96j03_E n) 1).bddAbove_image
      hcont.continuousOn
  rcases (bddAbove_iff_exists_ge (0 : ℝ)).1 hbdd with ⟨C, _, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  exact (hC _ ⟨x, hx, rfl⟩).trans (le_max_left _ _)

/-- Differentiation under a finite-measure integral with a constant global
majorant for the parameter derivative. -/
lemma apm_m96j03_hasDerivAt_integral_of_uniform_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F F' : ℝ → α → ℝ) (B : ℝ)
    (hF_meas : ∀ t, AEStronglyMeasurable (F t) μ)
    (hF_int : Integrable (F 0) μ)
    (hF'_meas : AEStronglyMeasurable (F' 0) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ t, ‖F' t a‖ ≤ B)
    (h_diff : ∀ᵐ a ∂μ, ∀ t, HasDerivAt (fun s ↦ F s a) (F' t a) t) :
    HasDerivAt (fun t ↦ ∫ a, F t a ∂μ) (∫ a, F' 0 a ∂μ) 0 := by
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ : α ↦ B)
    (s := Set.univ) (x₀ := (0 : ℝ)) Filter.univ_mem ?_ hF_int hF'_meas ?_
      (integrable_const B) ?_).2
  · exact Filter.Eventually.of_forall hF_meas
  · filter_upwards [h_bound] with a ha t _
    exact ha t
  · filter_upwards [h_diff] with a ha t _
    exact ha t

set_option maxHeartbeats 800000 in
lemma apm_m96j03_hasDerivAt_integral_comp_rotation {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (g : apm_m96j03_E n → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    HasDerivAt
      (fun t ↦ ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        g (apm_m96j03_coordinateRotation i j t ω) ∂volume.toSphere)
      (∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        fderiv ℝ g ω
          (ω.1 i • EuclideanSpace.single j 1 -
            ω.1 j • EuclideanSpace.single i 1) ∂volume.toSphere) 0 := by
  obtain ⟨C, hC0, hC⟩ :=
    apm_m96j03_exists_fderiv_norm_bound_on_sphere g hg
  let F : ℝ → Metric.sphere (0 : apm_m96j03_E n) 1 → ℝ := fun t ω ↦
    g (apm_m96j03_coordinateRotation i j t ω)
  let F' : ℝ → Metric.sphere (0 : apm_m96j03_E n) 1 → ℝ := fun t ω ↦
    fderiv ℝ g (apm_m96j03_coordinateRotation i j t ω)
      (apm_m96j03_coordinateRotationVelocity i j t ω)
  have hFmeas : ∀ t, AEStronglyMeasurable (F t) volume.toSphere := by
    intro t
    exact (hg.continuous.comp
      ((apm_m96j03_coordinateRotation i j t).continuous.comp
        continuous_subtype_val)).aestronglyMeasurable
  have hFint : Integrable (F 0) volume.toSphere := by
    have hc : Continuous (F 0) := by
      dsimp [F]
      fun_prop
    simpa only [integrableOn_univ] using
      (hc.continuousOn.integrableOn_compact isCompact_univ)
  have hF'meas : AEStronglyMeasurable (F' 0) volume.toSphere := by
    have hv : Continuous
        (fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦
          ω.1 i • EuclideanSpace.single j (1 : ℝ) -
            ω.1 j • EuclideanSpace.single i 1) := by fun_prop
    have hp : Continuous
        (fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦
          ((ω : apm_m96j03_E n),
            ω.1 i • EuclideanSpace.single j (1 : ℝ) -
              ω.1 j • EuclideanSpace.single i 1)) :=
      continuous_subtype_val.prodMk hv
    have hc := (hg.continuous_fderiv_apply (by simp)).comp hp
    have heq : F' 0 = fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦
        fderiv ℝ g ω
          (ω.1 i • EuclideanSpace.single j 1 -
            ω.1 j • EuclideanSpace.single i 1) := by
      funext ω
      simp only [F']
      simp [apm_m96j03_coordinateRotationVelocity_zero i j hij]
    rw [heq]
    simpa [Function.comp_def] using hc.aestronglyMeasurable
  have hbound : ∀ᵐ ω ∂volume.toSphere, ∀ t, ‖F' t ω‖ ≤ 2 * C := by
    refine Filter.Eventually.of_forall fun ω t ↦ ?_
    have hnormω : ‖(ω : apm_m96j03_E n)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using ω.property
    have hrotmem : apm_m96j03_coordinateRotation i j t (ω : apm_m96j03_E n) ∈
        Metric.sphere (0 : apm_m96j03_E n) 1 := by
      simp [Metric.mem_sphere, dist_zero_right, hnormω]
    calc
      ‖F' t ω‖ ≤
          ‖fderiv ℝ g (apm_m96j03_coordinateRotation i j t ω)‖ *
            ‖apm_m96j03_coordinateRotationVelocity i j t ω‖ := by
              exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * 2 := by
        gcongr
        · exact hC _ hrotmem
        · exact (apm_m96j03_coordinateRotationVelocity_norm_le
            i j hij (ω : apm_m96j03_E n) t).trans_eq (by rw [hnormω]; ring)
      _ = 2 * C := by ring
  have hdiff : ∀ᵐ ω ∂volume.toSphere, ∀ t,
      HasDerivAt (fun s ↦ F s ω) (F' t ω) t := by
    refine Filter.Eventually.of_forall fun ω t ↦ ?_
    exact apm_m96j03_comp_coordinateRotation_hasDerivAt i j hij g ω t
      (hg.differentiable (by simp)).differentiableAt
  have hmain := apm_m96j03_hasDerivAt_integral_of_uniform_bound
    volume.toSphere F F' (2 * C) hFmeas hFint hF'meas hbound hdiff
  convert hmain using 1
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun ω ↦ ?_
  simp only [F']
  simp [apm_m96j03_coordinateRotationVelocity_zero i j hij]

/-- Infinitesimal invariance of sphere measure under a coordinate-plane
rotation. -/
lemma apm_m96j03_integral_infinitesimal_rotation {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (g : apm_m96j03_E n → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    (∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
      fderiv ℝ g ω
        (ω.1 i • EuclideanSpace.single j 1 -
          ω.1 j • EuclideanSpace.single i 1) ∂volume.toSphere) = 0 := by
  let H : ℝ → ℝ := fun t ↦
    ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
      g (apm_m96j03_coordinateRotation i j t ω) ∂volume.toSphere
  have hder := apm_m96j03_hasDerivAt_integral_comp_rotation i j hij g hg
  have hconst : H = fun _ : ℝ ↦
      ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1, g ω ∂volume.toSphere := by
    funext t
    simpa [H] using apm_m96j03_integral_sphereIsometry
      (apm_m96j03_coordinateRotation i j t)
      (fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦ g ω)
  have hz : HasDerivAt H 0 0 := by
    rw [hconst]
    exact hasDerivAt_const (x := (0 : ℝ)) _
  exact hder.unique hz

/-- Pointwise product rule for multiplying a smooth function by one standard
coordinate. -/
lemma apm_m96j03_fderiv_coordinate_mul {n : ℕ}
    (j : Fin n) (g : apm_m96j03_E n → ℝ)
    (hg : Differentiable ℝ g) (x v : apm_m96j03_E n) :
    fderiv ℝ (fun y : apm_m96j03_E n ↦ y j * g y) x v =
      v j * g x + x j * fderiv ℝ g x v := by
  rw [fderiv_fun_mul (by fun_prop) hg.differentiableAt]
  have hcoord : fderiv ℝ (fun y : apm_m96j03_E n ↦ y j) x v = v j := by
    have h := ((EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt
      (x := x)).fderiv
    have hv := congrArg (fun L : apm_m96j03_E n →L[ℝ] ℝ ↦ L v) h
    simpa using hv
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rw [hcoord]
  ring

/-- Pairwise spherical integration-by-parts identity obtained from an
infinitesimal rotation. -/
lemma apm_m96j03_integral_rotation_pair {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (g : apm_m96j03_E n → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    (∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
      (ω.1 i) * g ω + (ω.1 j) *
        fderiv ℝ g ω
          (ω.1 i • EuclideanSpace.single j 1 -
            ω.1 j • EuclideanSpace.single i 1) ∂volume.toSphere) = 0 := by
  have hq : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : apm_m96j03_E n ↦ x j * g x) := by fun_prop
  have hrot := apm_m96j03_integral_infinitesimal_rotation i j hij
    (fun x : apm_m96j03_E n ↦ x j * g x) hq
  convert hrot using 1
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun ω ↦ ?_
  symm
  change fderiv ℝ (fun x : apm_m96j03_E n ↦ x j * g x) ω
      (ω.1 i • EuclideanSpace.single j 1 -
        ω.1 j • EuclideanSpace.single i 1) = _
  rw [apm_m96j03_fderiv_coordinate_mul j g
    (hg.differentiable (by simp))]
  simp [PiLp.single_apply, hij, Ne.symm hij]

/-- Reconstruction of a Euclidean vector from its standard coordinates. -/
lemma apm_m96j03_sum_coordinate_single {n : ℕ} (x : apm_m96j03_E n) :
    ∑ j : Fin n, x j • EuclideanSpace.single j (1 : ℝ) = x := by
  classical
  ext k
  simp [Pi.single_apply]

lemma apm_m96j03_sum_coordinate_single_erase {n : ℕ}
    (i : Fin n) (x : apm_m96j03_E n) :
    ∑ j ∈ Finset.univ.erase i,
        x j • EuclideanSpace.single j (1 : ℝ) =
      x - x i • EuclideanSpace.single i 1 := by
  classical
  have h := apm_m96j03_sum_coordinate_single x
  have herase := Finset.sum_erase_add Finset.univ
    (fun j : Fin n ↦ x j • EuclideanSpace.single j (1 : ℝ))
    (Finset.mem_univ i)
  rw [h] at herase
  exact eq_sub_of_add_eq herase

lemma apm_m96j03_sum_coordinate_sq_erase_sphere {n : ℕ}
    (i : Fin n) (ω : Metric.sphere (0 : apm_m96j03_E n) 1) :
    ∑ j ∈ Finset.univ.erase i, (ω.1 j) ^ 2 = 1 - (ω.1 i) ^ 2 := by
  classical
  have hnorm : ‖(ω : apm_m96j03_E n)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using ω.property
  have hsq := EuclideanSpace.real_norm_sq_eq (ω : apm_m96j03_E n)
  rw [hnorm, one_pow] at hsq
  have herase := Finset.sum_erase_add Finset.univ
    (fun j : Fin n ↦ (ω.1 j) ^ 2) (Finset.mem_univ i)
  rw [← hsq] at herase
  linarith

/-- The sum of the infinitesimal rotations in all coordinate planes through
`i` is the negative tangential projection of the `i`th basis vector. -/
lemma apm_m96j03_sum_rotation_generators {n : ℕ}
    (i : Fin n) (ω : Metric.sphere (0 : apm_m96j03_E n) 1) :
    ∑ j ∈ Finset.univ.erase i,
        (ω.1 j) •
          (ω.1 i • EuclideanSpace.single j (1 : ℝ) -
            ω.1 j • EuclideanSpace.single i 1) =
      ω.1 i • (ω : apm_m96j03_E n) -
        EuclideanSpace.single i 1 := by
  classical
  calc
    _ = ω.1 i • (∑ j ∈ Finset.univ.erase i,
          ω.1 j • EuclideanSpace.single j (1 : ℝ)) -
        (∑ j ∈ Finset.univ.erase i, (ω.1 j) ^ 2) •
          EuclideanSpace.single i 1 := by
      simp_rw [smul_sub]
      rw [Finset.smul_sum, Finset.sum_smul, Finset.sum_sub_distrib]
      apply congrArg₂ (· - ·)
      · apply Finset.sum_congr rfl
        intro j hj
        module
      · apply Finset.sum_congr rfl
        intro j hj
        module
    _ = _ := by
      rw [apm_m96j03_sum_coordinate_single_erase,
        apm_m96j03_sum_coordinate_sq_erase_sphere]
      module

lemma apm_m96j03_sum_rotation_pair_integrands {n : ℕ}
    (i : Fin n) (g : apm_m96j03_E n → ℝ)
    (ω : Metric.sphere (0 : apm_m96j03_E n) 1) :
    ∑ j ∈ Finset.univ.erase i,
        ((ω.1 i) * g ω + (ω.1 j) *
          fderiv ℝ g ω
            (ω.1 i • EuclideanSpace.single j 1 -
              ω.1 j • EuclideanSpace.single i 1)) =
      ((n : ℝ) - 1) * (ω.1 i * g ω) +
        fderiv ℝ g ω
          (ω.1 i • (ω : apm_m96j03_E n) -
            EuclideanSpace.single i 1) := by
  classical
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr ⟨i⟩
  calc
    _ = (∑ j ∈ Finset.univ.erase i, (ω.1 i) * g ω) +
        ∑ j ∈ Finset.univ.erase i,
          fderiv ℝ g ω
            ((ω.1 j) • (ω.1 i • EuclideanSpace.single j 1 -
              ω.1 j • EuclideanSpace.single i 1)) := by
      rw [Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul]
      rfl
    _ = _ := by
      rw [← map_sum, apm_m96j03_sum_rotation_generators]
      simp [Finset.card_erase_of_mem, Nat.cast_sub hn, Nat.cast_one]

/-- Integration by parts on the unit sphere, obtained by summing the
infinitesimal rotations through one fixed coordinate axis. -/
lemma apm_m96j03_sphere_integration_by_parts {n : ℕ}
    (i : Fin n) (g : apm_m96j03_E n → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    (∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        fderiv ℝ g ω
          (EuclideanSpace.single i 1 -
            ω.1 i • (ω : apm_m96j03_E n)) ∂volume.toSphere) =
      ((n : ℝ) - 1) *
        ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
          ω.1 i * g ω ∂volume.toSphere := by
  classical
  let A := fun j : Fin n ↦
    fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦
      (ω.1 i) * g ω + (ω.1 j) *
        fderiv ℝ g ω
          (ω.1 i • EuclideanSpace.single j 1 -
            ω.1 j • EuclideanSpace.single i 1)
  have hAcont : ∀ j, Continuous (A j) := by
    intro j
    have hv : Continuous
        (fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦
          ω.1 i • EuclideanSpace.single j (1 : ℝ) -
            ω.1 j • EuclideanSpace.single i 1) := by fun_prop
    have hd : Continuous
        (fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦
          fderiv ℝ g ω
            (ω.1 i • EuclideanSpace.single j (1 : ℝ) -
              ω.1 j • EuclideanSpace.single i 1)) :=
      (hg.continuous_fderiv_apply (by simp)).comp
        (continuous_subtype_val.prodMk hv)
    dsimp [A]
    fun_prop
  have hAint : ∀ j ∈ Finset.univ.erase i,
      Integrable (A j) volume.toSphere := by
    intro j hj
    simpa only [integrableOn_univ] using
      (hAcont j).continuousOn.integrableOn_compact isCompact_univ
  have hsumzero :
      (∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        ∑ j ∈ Finset.univ.erase i, A j ω ∂volume.toSphere) = 0 := by
    rw [integral_finset_sum _ hAint]
    apply Finset.sum_eq_zero
    intro j hj
    exact apm_m96j03_integral_rotation_pair i j
      (Finset.ne_of_mem_erase hj).symm g hg
  have hpoint : ∀ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
      (∑ j ∈ Finset.univ.erase i, A j ω) =
        ((n : ℝ) - 1) * (ω.1 i * g ω) +
          fderiv ℝ g ω
            (ω.1 i • (ω : apm_m96j03_E n) -
              EuclideanSpace.single i 1) := by
    intro ω
    exact apm_m96j03_sum_rotation_pair_integrands i g ω
  have hzero :
      (∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        (((n : ℝ) - 1) * (ω.1 i * g ω) +
          fderiv ℝ g ω
            (ω.1 i • (ω : apm_m96j03_E n) -
              EuclideanSpace.single i 1)) ∂volume.toSphere) = 0 := by
    rw [← hsumzero]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ω ↦ (hpoint ω).symm
  have hcoord : Integrable
      (fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦ ω.1 i * g ω)
      volume.toSphere := by
    simpa only [integrableOn_univ] using
      (by fun_prop : Continuous
        (fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦ ω.1 i * g ω)).continuousOn.integrableOn_compact
          isCompact_univ
  have hderiv : Integrable
      (fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦
        fderiv ℝ g ω
          (ω.1 i • (ω : apm_m96j03_E n) -
            EuclideanSpace.single i 1)) volume.toSphere := by
    have hv : Continuous
        (fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦
          ω.1 i • (ω : apm_m96j03_E n) -
            EuclideanSpace.single i 1) := by fun_prop
    have hc := (hg.continuous_fderiv_apply (by simp)).comp
      (continuous_subtype_val.prodMk hv)
    simpa only [integrableOn_univ] using
      hc.continuousOn.integrableOn_compact isCompact_univ
  rw [integral_add (hcoord.const_mul _) hderiv, integral_const_mul] at hzero
  have hneg :
      (∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        fderiv ℝ g ω
          (EuclideanSpace.single i 1 -
            ω.1 i • (ω : apm_m96j03_E n)) ∂volume.toSphere) =
      - ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        fderiv ℝ g ω
          (ω.1 i • (ω : apm_m96j03_E n) -
            EuclideanSpace.single i 1) ∂volume.toSphere := by
    rw [← integral_neg]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun ω ↦ ?_
    dsimp only
    rw [show EuclideanSpace.single i (1 : ℝ) -
          ω.1 i • (ω : apm_m96j03_E n) =
        -(ω.1 i • (ω : apm_m96j03_E n) -
          EuclideanSpace.single i 1) by module, map_neg]
  rw [hneg]
  linarith

/-- Mixed second derivative of a first derivative pulled back along radial
scaling. -/
lemma apm_m96j03_fderiv_radial_fderiv_basis {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (r : ℝ) (i : Fin n) (x v : apm_m96j03_E n) :
    fderiv ℝ
        (fun y : apm_m96j03_E n ↦
          fderiv ℝ φ (r • y) (EuclideanSpace.single i 1)) x v =
      r * iteratedFDeriv ℝ 2 φ (r • x)
        ![v, EuclideanSpace.single i 1] := by
  have h2 : ContDiff ℝ (2 : WithTop ℕ∞) φ :=
    hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (h2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hψ : Differentiable ℝ
      (fun y ↦ fderiv ℝ φ y (EuclideanSpace.single i 1)) := by
    fun_prop
  have hscale : HasFDerivAt
      (fun y : apm_m96j03_E n ↦ r • y)
      (r • ContinuousLinearMap.id ℝ (apm_m96j03_E n)) x :=
    (hasFDerivAt_id x).const_smul r
  have hcomp := ((hψ (r • x)).hasFDerivAt.comp x hscale)
  have hf := hcomp.fderiv
  have happ := congrArg
    (fun L : apm_m96j03_E n →L[ℝ] ℝ ↦ L v) hf
  change fderiv ℝ
      (fun y : apm_m96j03_E n ↦
        fderiv ℝ φ (r • y) (EuclideanSpace.single i 1)) x v =
    fderiv ℝ (fun y ↦ fderiv ℝ φ y (EuclideanSpace.single i 1))
      (r • x) ((r • ContinuousLinearMap.id ℝ (apm_m96j03_E n)) v) at happ
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] at happ
  rw [fderiv_clm_apply (hd (r • x)) (by fun_prop)] at happ
  rw [iteratedFDeriv_two_apply]
  simpa [smul_eq_mul, mul_comm] using happ

lemma apm_m96j03_sum_coordinate_fderiv {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (x ω : apm_m96j03_E n) :
    ∑ i : Fin n, ω i *
        fderiv ℝ φ x (EuclideanSpace.single i 1) =
      fderiv ℝ φ x ω := by
  classical
  simp_rw [← smul_eq_mul, ← map_smul]
  rw [← map_sum, apm_m96j03_sum_coordinate_single]

lemma apm_m96j03_sum_coordinate_hessian {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (x ω : apm_m96j03_E n) :
    ∑ i : Fin n, ω i *
        iteratedFDeriv ℝ 2 φ x
          ![ω, EuclideanSpace.single i 1] =
      iteratedFDeriv ℝ 2 φ x ![ω, ω] := by
  classical
  simp_rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp_rw [← smul_eq_mul, ← map_smul]
  rw [← map_sum, apm_m96j03_sum_coordinate_single]

lemma apm_m96j03_contDiff_radial_fderiv_basis {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (r : ℝ) (i : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun y : apm_m96j03_E n ↦
        fderiv ℝ φ (r • y) (EuclideanSpace.single i 1)) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : apm_m96j03_E n × apm_m96j03_E n ↦
        fderiv ℝ φ p.1 p.2) :=
    hφ.contDiff_fderiv_apply (by simp)
  have hp : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : apm_m96j03_E n ↦
        (r • y, EuclideanSpace.single i (1 : ℝ))) := by fun_prop
  exact hd.comp hp

/-- The coordinatewise spherical integration-by-parts equation already
rewritten as a mixed Hessian identity. -/
lemma apm_m96j03_sphere_ibp_radial_basis {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (r : ℝ) (i : Fin n) :
    (∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        r * iteratedFDeriv ℝ 2 φ (r • (ω : apm_m96j03_E n))
          ![EuclideanSpace.single i 1 -
              ω.1 i • (ω : apm_m96j03_E n),
            EuclideanSpace.single i 1] ∂volume.toSphere) =
      ((n : ℝ) - 1) *
        ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
          ω.1 i * fderiv ℝ φ (r • (ω : apm_m96j03_E n))
            (EuclideanSpace.single i 1) ∂volume.toSphere := by
  let g : apm_m96j03_E n → ℝ := fun y ↦
    fderiv ℝ φ (r • y) (EuclideanSpace.single i 1)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
    apm_m96j03_contDiff_radial_fderiv_basis φ hφ r i
  have h := apm_m96j03_sphere_integration_by_parts i g hg
  convert h using 1
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun ω ↦ ?_
  dsimp [g]
  exact (apm_m96j03_fderiv_radial_fderiv_basis φ hφ r i ω
    (EuclideanSpace.single i 1 -
      ω.1 i • (ω : apm_m96j03_E n))).symm

lemma apm_m96j03_sum_tangential_hessian {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (x ω : apm_m96j03_E n) :
    ∑ i : Fin n,
        iteratedFDeriv ℝ 2 φ x
          ![EuclideanSpace.single i 1 -
              ω i • ω,
            EuclideanSpace.single i 1] =
      (∑ i : Fin n, iteratedFDeriv ℝ 2 φ x
        ![EuclideanSpace.single i 1, EuclideanSpace.single i 1]) -
        iteratedFDeriv ℝ 2 φ x ![ω, ω] := by
  classical
  simp_rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp_rw [map_sub, ContinuousLinearMap.sub_apply, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp_rw [← smul_eq_mul, ← map_smul]
  rw [← map_sum, apm_m96j03_sum_coordinate_single]

/-- The sphere-averaged Hessian trace decomposes into its radial second
derivative and the first-order radial term. -/
lemma apm_m96j03_sphere_hessian_trace_identity {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (r : ℝ) :
    r * (∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
      apm_m96j03_laplacian φ (r • (ω : apm_m96j03_E n))
        ∂volume.toSphere) =
      r * (∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        iteratedFDeriv ℝ 2 φ (r • (ω : apm_m96j03_E n))
          ![(ω : apm_m96j03_E n), (ω : apm_m96j03_E n)]
          ∂volume.toSphere) +
      ((n : ℝ) - 1) *
        ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
          fderiv ℝ φ (r • (ω : apm_m96j03_E n))
            (ω : apm_m96j03_E n) ∂volume.toSphere := by
  classical
  let L := fun i : Fin n ↦
    fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦
      r * iteratedFDeriv ℝ 2 φ (r • (ω : apm_m96j03_E n))
        ![EuclideanSpace.single i 1 -
            ω.1 i • (ω : apm_m96j03_E n),
          EuclideanSpace.single i 1]
  let R := fun i : Fin n ↦
    fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦
      ω.1 i * fderiv ℝ φ (r • (ω : apm_m96j03_E n))
        (EuclideanSpace.single i 1)
  have hLcont : ∀ i, Continuous (L i) := by
    intro i
    let g : apm_m96j03_E n → ℝ := fun y ↦
      fderiv ℝ φ (r • y) (EuclideanSpace.single i 1)
    have hg := apm_m96j03_contDiff_radial_fderiv_basis φ hφ r i
    have hv : Continuous
        (fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦
          EuclideanSpace.single i (1 : ℝ) -
            ω.1 i • (ω : apm_m96j03_E n)) := by fun_prop
    have hc : Continuous
        (fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦
          fderiv ℝ g ω
            (EuclideanSpace.single i 1 -
              ω.1 i • (ω : apm_m96j03_E n))) :=
      (hg.continuous_fderiv_apply (by simp)).comp
        (continuous_subtype_val.prodMk hv)
    apply Continuous.congr hc
    intro ω
    dsimp [L, g]
    exact apm_m96j03_fderiv_radial_fderiv_basis φ hφ r i ω _
  have hRcont : ∀ i, Continuous (R i) := by
    intro i
    dsimp [R]
    have hD := hφ.continuous_fderiv_apply (by simp)
    fun_prop
  have hLint : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Integrable (L i) volume.toSphere := by
    intro i hi
    simpa only [integrableOn_univ] using
      (hLcont i).continuousOn.integrableOn_compact isCompact_univ
  have hRint : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Integrable (R i) volume.toSphere := by
    intro i hi
    simpa only [integrableOn_univ] using
      (hRcont i).continuousOn.integrableOn_compact isCompact_univ
  have hsum :
      (∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        ∑ i : Fin n, L i ω ∂volume.toSphere) =
      ((n : ℝ) - 1) *
        ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
          ∑ i : Fin n, R i ω ∂volume.toSphere := by
    rw [integral_finset_sum Finset.univ hLint,
      integral_finset_sum Finset.univ hRint, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact apm_m96j03_sphere_ibp_radial_basis φ hφ r i
  rw [show (∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        ∑ i : Fin n, L i ω ∂volume.toSphere) =
      r * ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        (apm_m96j03_laplacian φ (r • (ω : apm_m96j03_E n)) -
          iteratedFDeriv ℝ 2 φ (r • (ω : apm_m96j03_E n))
            ![(ω : apm_m96j03_E n), (ω : apm_m96j03_E n)])
          ∂volume.toSphere by
      rw [← integral_const_mul]
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun ω ↦ ?_
      dsimp [L]
      rw [← Finset.mul_sum, apm_m96j03_sum_tangential_hessian,
        ← apm_m96j03_laplacian_eq_trace_iteratedFDeriv φ hφ]
      ,
    show (∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        ∑ i : Fin n, R i ω ∂volume.toSphere) =
      ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        fderiv ℝ φ (r • (ω : apm_m96j03_E n))
          (ω : apm_m96j03_E n) ∂volume.toSphere by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun ω ↦ ?_
      dsimp [R]
      exact apm_m96j03_sum_coordinate_fderiv φ _ _] at hsum
  by_cases hr : r = 0
  · subst r
    simpa using hsum
  · have hlap : Integrable
        (fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦
          apm_m96j03_laplacian φ (r • (ω : apm_m96j03_E n)))
        volume.toSphere := by
      have hs : Continuous
          (fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦
            r • (ω : apm_m96j03_E n)) := by fun_prop
      have hc := (apm_m96j03_continuous_laplacian φ hφ).comp
        hs
      simpa only [integrableOn_univ] using
        hc.continuousOn.integrableOn_compact isCompact_univ
    have hsumL : Integrable
        (fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦
          ∑ i : Fin n, L i ω) volume.toSphere :=
      integrable_finset_sum _ hLint
    have hrad : Integrable
        (fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦
          iteratedFDeriv ℝ 2 φ (r • (ω : apm_m96j03_E n))
            ![(ω : apm_m96j03_E n), (ω : apm_m96j03_E n)])
        volume.toSphere := by
      have hz := hlap.sub (hsumL.const_mul r⁻¹)
      apply hz.congr
      refine Filter.Eventually.of_forall fun ω ↦ ?_
      dsimp [L]
      rw [← Finset.mul_sum, apm_m96j03_sum_tangential_hessian,
        ← apm_m96j03_laplacian_eq_trace_iteratedFDeriv φ hφ]
      field_simp
      ring
    rw [integral_sub hlap hrad] at hsum
    linarith

/-- Uniform scalar bound for the radial Hessian evaluation.  This uses a
compact product support rather than the operator norm topology. -/
lemma apm_m96j03_exists_radial_hessian_bound {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (hφ : apm_m96j03_IsTestFunction φ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x : apm_m96j03_E n)
        (ω : Metric.sphere (0 : apm_m96j03_E n) 1),
        |iteratedFDeriv ℝ 2 φ x
          ![(ω : apm_m96j03_E n), (ω : apm_m96j03_E n)]| ≤ C := by
  let Q := fun p : apm_m96j03_E n ×
      Metric.sphere (0 : apm_m96j03_E n) 1 ↦
    fderiv ℝ (fderiv ℝ φ) p.1 (p.2 : apm_m96j03_E n)
      (p.2 : apm_m96j03_E n)
  have h2 : ContDiff ℝ (2 : WithTop ℕ∞) φ :=
    hφ.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hD : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (h2.fderiv_right (m := 1) (by norm_num)).continuous_fderiv
      (by norm_num)
  have hQ : Continuous Q := by
    dsimp [Q]
    exact ((hD.comp continuous_fst).clm_apply
      (continuous_subtype_val.comp continuous_snd)).clm_apply
        (continuous_subtype_val.comp continuous_snd)
  have hsD : HasCompactSupport (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.2.fderiv ℝ).fderiv ℝ
  have hsQ : HasCompactSupport Q := by
    apply (hsD.isCompact.prod isCompact_univ).of_isClosed_subset
      isClosed_closure
    apply closure_minimal
    · intro p hp
      refine ⟨?_, Set.mem_univ _⟩
      by_contra hx
      have hz : fderiv ℝ (fderiv ℝ φ) p.1 = 0 := by
        by_contra hnz
        exact hx (subset_closure hnz)
      exact hp (by simp [Q, hz])
    · exact (hsD.isCompact.prod isCompact_univ).isClosed
  have hbdd : BddAbove ((fun p ↦ |Q p|) '' tsupport Q) :=
    hsQ.isCompact.bddAbove_image hQ.abs.continuousOn
  rcases (bddAbove_iff_exists_ge (0 : ℝ)).1 hbdd with ⟨C, _, hC⟩
  refine ⟨max C 0, le_max_right _ _, fun x ω ↦ ?_⟩
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases hp : (x, ω) ∈ tsupport Q
  · exact (hC _ ⟨(x, ω), hp, rfl⟩).trans (le_max_left _ _)
  · have hz : Q (x, ω) = 0 := by
      by_contra hnz
      exact hp (subset_closure hnz)
    change |Q (x, ω)| ≤ _
    rw [hz, abs_zero]
    exact le_max_right _ _

lemma apm_m96j03_hasDerivAt_integral_of_uniform_bound_at
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F F' : ℝ → α → ℝ) (B x₀ : ℝ)
    (hF_meas : ∀ t, AEStronglyMeasurable (F t) μ)
    (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable (F' x₀) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ t, ‖F' t a‖ ≤ B)
    (h_diff : ∀ᵐ a ∂μ, ∀ t, HasDerivAt (fun s ↦ F s a) (F' t a) t) :
    HasDerivAt (fun t ↦ ∫ a, F t a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ := by
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ : α ↦ B)
    (s := Set.univ) (x₀ := x₀) Filter.univ_mem ?_ hF_int hF'_meas ?_
      (integrable_const B) ?_).2
  · exact Filter.Eventually.of_forall hF_meas
  · filter_upwards [h_bound] with a ha t _
    exact ha t
  · filter_upwards [h_diff] with a ha t _
    exact ha t

lemma apm_m96j03_hasDerivAt_radial_average {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (hφ : apm_m96j03_IsTestFunction φ)
    (r : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦
        ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
          fderiv ℝ φ (s • (ω : apm_m96j03_E n))
            (ω : apm_m96j03_E n) ∂volume.toSphere)
      (∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        iteratedFDeriv ℝ 2 φ (r • (ω : apm_m96j03_E n))
          ![(ω : apm_m96j03_E n), (ω : apm_m96j03_E n)]
          ∂volume.toSphere) r := by
  obtain ⟨C, hC0, hC⟩ := apm_m96j03_exists_radial_hessian_bound φ hφ
  let F := fun t : ℝ ↦
    fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦
      fderiv ℝ φ (t • (ω : apm_m96j03_E n))
        (ω : apm_m96j03_E n)
  let F' := fun t : ℝ ↦
    fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦
      iteratedFDeriv ℝ 2 φ (t • (ω : apm_m96j03_E n))
        ![(ω : apm_m96j03_E n), (ω : apm_m96j03_E n)]
  have hFmeas : ∀ t, AEStronglyMeasurable (F t) volume.toSphere := by
    intro t
    have hc : Continuous (F t) := by
      dsimp [F]
      have hd := hφ.1.continuous_fderiv_apply (by simp)
      fun_prop
    exact hc.aestronglyMeasurable
  have hFint : Integrable (F r) volume.toSphere := by
    have hc : Continuous (F r) := by
      dsimp [F]
      have hd := hφ.1.continuous_fderiv_apply (by simp)
      fun_prop
    simpa only [integrableOn_univ] using
      hc.continuousOn.integrableOn_compact isCompact_univ
  have hF'meas : AEStronglyMeasurable (F' r) volume.toSphere := by
    have h2 : ContDiff ℝ (2 : WithTop ℕ∞) φ :=
      hφ.1.of_le (WithTop.coe_le_coe.mpr le_top)
    have hD : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
      (h2.fderiv_right (m := 1) (by norm_num)).continuous_fderiv
        (by norm_num)
    have hc : Continuous (F' r) := by
      dsimp [F']
      simp_rw [iteratedFDeriv_two_apply]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact (((hD.comp ((continuous_const.smul continuous_subtype_val))).clm_apply
        continuous_subtype_val).clm_apply continuous_subtype_val)
    exact hc.aestronglyMeasurable
  have hbound : ∀ᵐ ω ∂volume.toSphere, ∀ t, ‖F' t ω‖ ≤ C := by
    refine Filter.Eventually.of_forall fun ω t ↦ ?_
    simpa [Real.norm_eq_abs, F'] using
      hC (t • (ω : apm_m96j03_E n)) ω
  have hdiff : ∀ᵐ ω ∂volume.toSphere, ∀ t,
      HasDerivAt (fun s ↦ F s ω) (F' t ω) t := by
    refine Filter.Eventually.of_forall fun ω t ↦ ?_
    simpa [F, F'] using apm_m96j03_hasDerivAt_radial_fderiv φ hφ.1
      (ω : apm_m96j03_E n) t
  exact apm_m96j03_hasDerivAt_integral_of_uniform_bound_at
    volume.toSphere F F' C r hFmeas hFint hF'meas hbound hdiff

lemma apm_m96j03_hasDerivAt_radial_flux {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (hφ : apm_m96j03_IsTestFunction φ)
    (hn : 0 < n) (r : ℝ) (hr : 0 < r) :
    HasDerivAt
      (fun s : ℝ ↦ s ^ (n - 1) *
        ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
          fderiv ℝ φ (s • (ω : apm_m96j03_E n))
            (ω : apm_m96j03_E n) ∂volume.toSphere)
      (r ^ (n - 1) *
        ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
          apm_m96j03_laplacian φ (r • (ω : apm_m96j03_E n))
            ∂volume.toSphere) r := by
  let A := fun s : ℝ ↦
    ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
      fderiv ℝ φ (s • (ω : apm_m96j03_E n))
        (ω : apm_m96j03_E n) ∂volume.toSphere
  let H := ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
    iteratedFDeriv ℝ 2 φ (r • (ω : apm_m96j03_E n))
      ![(ω : apm_m96j03_E n), (ω : apm_m96j03_E n)]
      ∂volume.toSphere
  let L := ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
    apm_m96j03_laplacian φ (r • (ω : apm_m96j03_E n))
      ∂volume.toSphere
  have hA : HasDerivAt A H r := by
    exact apm_m96j03_hasDerivAt_radial_average φ hφ r
  have hp := (hasDerivAt_id r).pow (n - 1)
  have hprod := hp.mul hA
  change HasDerivAt (fun s ↦ s ^ (n - 1) * A s)
    (r ^ (n - 1) * L) r
  refine hprod.congr_deriv ?_
  simp only [id_eq, Pi.pow_apply, one_mul, mul_one]
  have htrace : r * L = r * H + ((n : ℝ) - 1) * A r := by
    exact apm_m96j03_sphere_hessian_trace_identity φ hφ.1 r
  by_cases hn1 : n = 1
  · subst n
    norm_num at htrace ⊢
    rcases htrace with htrace | hzero
    · exact htrace.symm
    · exact (ne_of_gt hr hzero).elim
  · have hn2 : 2 ≤ n := by omega
    have hrne : r ≠ 0 := ne_of_gt hr
    rw [show n - 1 - 1 = n - 2 by omega]
    have hpow : r ^ (n - 1) = r ^ (n - 2) * r := by
      rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn]
      simp
    rw [hcast, hpow]
    have ht : ((n : ℝ) - 1) * A r + r * H = r * L := by
      linarith [htrace]
    calc
      ((n : ℝ) - 1) * r ^ (n - 2) * A r +
          (r ^ (n - 2) * r) * H =
        r ^ (n - 2) * (((n : ℝ) - 1) * A r + r * H) := by ring
      _ = r ^ (n - 2) * (r * L) := by rw [ht]
      _ = (r ^ (n - 2) * r) * L := by ring

lemma apm_m96j03_radial_flux_zero {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (hn : 0 < n) :
    (0 : ℝ) ^ (n - 1) *
      (∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        fderiv ℝ φ ((0 : ℝ) • (ω : apm_m96j03_E n))
          (ω : apm_m96j03_E n) ∂volume.toSphere) = 0 := by
  by_cases hn1 : n = 1
  · subst n
    simp only [Nat.reduceSub, pow_zero, one_mul, zero_smul]
    apply apm_m96j03_integral_sphere_eq_zero_of_odd
    intro ω
    change fderiv ℝ φ 0
        ((apm_m96j03_sphereIsometry (LinearIsometryEquiv.neg ℝ) ω :
          Metric.sphere (0 : apm_m96j03_E 1) 1) : apm_m96j03_E 1) =
      -fderiv ℝ φ 0 (ω : apm_m96j03_E 1)
    rw [apm_m96j03_sphereIsometry_neg_apply, map_neg]
  · have hexp : 0 < n - 1 := Nat.sub_pos_of_lt (by omega)
    rw [zero_pow hexp.ne', zero_mul]

lemma apm_m96j03_continuous_radial_flux {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (hφ : apm_m96j03_IsTestFunction φ) :
    Continuous (fun r : ℝ ↦ r ^ (n - 1) *
      ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        fderiv ℝ φ (r • (ω : apm_m96j03_E n))
          (ω : apm_m96j03_E n) ∂volume.toSphere) := by
  have hA : Continuous (fun r : ℝ ↦
      ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        fderiv ℝ φ (r • (ω : apm_m96j03_E n))
          (ω : apm_m96j03_E n) ∂volume.toSphere) :=
    continuous_iff_continuousAt.mpr fun r ↦
      (apm_m96j03_hasDerivAt_radial_average φ hφ r).continuousAt
  fun_prop

lemma apm_m96j03_intervalIntegral_eq_of_deriv_off_zero
    (F f : ℝ → ℝ)
    (hF : ContinuousOn F (Set.Icc (0 : ℝ) 1))
    (hderiv : ∀ r, 0 < r → r < 1 → HasDerivAt F (f r) r)
    (hint : IntervalIntegrable f volume 0 1)
    (hzero : F 0 = 0) :
    (∫ r in (0 : ℝ)..1, f r) = F 1 := by
  have h := integral_eq_of_hasDerivAt_off_countable_of_le F f
    (show (0 : ℝ) ≤ 1 by norm_num) (Set.countable_singleton 0) hF
    (fun r hr ↦ hderiv r hr.1.1 hr.1.2) hint
  simpa [hzero] using h

lemma apm_m96j03_continuous_radial_laplacian_average {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    Continuous (fun r : ℝ ↦
      ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        apm_m96j03_laplacian φ
          (r • (ω : apm_m96j03_E n)) ∂volume.toSphere) := by
  let f := fun r : ℝ ↦
    fun ω : Metric.sphere (0 : apm_m96j03_E n) 1 ↦
      apm_m96j03_laplacian φ (r • (ω : apm_m96j03_E n))
  have hf : Continuous f.uncurry := by
    dsimp [f, Function.uncurry]
    have hl := apm_m96j03_continuous_laplacian φ hφ
    fun_prop
  have h := continuous_parametric_integral_of_continuous
    (μ := volume.toSphere) hf (s := Set.univ) isCompact_univ
  simpa [f] using h

lemma apm_m96j03_intervalIntegrable_radial_flux_deriv {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    IntervalIntegrable
      (fun r : ℝ ↦ r ^ (n - 1) *
        ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
          apm_m96j03_laplacian φ
            (r • (ω : apm_m96j03_E n)) ∂volume.toSphere)
      volume 0 1 := by
  apply Continuous.intervalIntegrable
  exact (continuous_pow _).mul
    (apm_m96j03_continuous_radial_laplacian_average φ hφ)

lemma apm_m96j03_intervalIntegral_radial_laplacian {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (hφ : apm_m96j03_IsTestFunction φ)
    (hn : 0 < n) :
    (∫ r in (0 : ℝ)..1, r ^ (n - 1) *
      ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        apm_m96j03_laplacian φ
          (r • (ω : apm_m96j03_E n)) ∂volume.toSphere) =
      ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        fderiv ℝ φ ω ω ∂volume.toSphere := by
  let F := fun r : ℝ ↦ r ^ (n - 1) *
    ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
      fderiv ℝ φ (r • (ω : apm_m96j03_E n))
        (ω : apm_m96j03_E n) ∂volume.toSphere
  let f := fun r : ℝ ↦ r ^ (n - 1) *
    ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
      apm_m96j03_laplacian φ
        (r • (ω : apm_m96j03_E n)) ∂volume.toSphere
  have h := apm_m96j03_intervalIntegral_eq_of_deriv_off_zero F f
    (apm_m96j03_continuous_radial_flux φ hφ).continuousOn
    (fun r hr0 hr1 ↦ apm_m96j03_hasDerivAt_radial_flux φ hφ hn r hr0)
    (apm_m96j03_intervalIntegrable_radial_flux_deriv φ hφ.1)
    (apm_m96j03_radial_flux_zero φ hn)
  simpa [F, f] using h

lemma apm_m96j03_integral_volumeIoiPow_cutoff
    (k : ℕ) (A : ℝ → ℝ) (hA : Continuous A) :
    (∫ r : Set.Ioi (0 : ℝ), (if r.1 < 1 then A r.1 else 0)
      ∂Measure.volumeIoiPow k) =
      ∫ r in (0 : ℝ)..1, r ^ k * A r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul,
    integral_subtype_comap measurableSet_Ioi
      (fun r : ℝ ↦ Real.toNNReal (r ^ k) •
        (if r < 1 then A r else 0)),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  · rw [← setIntegral_congr_set Ioo_ae_eq_Ioc]
    have hind :
        (fun x : ℝ ↦ Real.toNNReal (x ^ k) •
          (if x < 1 then A x else 0)) =
        Set.indicator (Set.Iio (1 : ℝ))
          (fun x ↦ Real.toNNReal (x ^ k) • A x) := by
      funext x
      by_cases hx : x < 1 <;> simp [Set.indicator, hx]
    rw [hind]
    rw [setIntegral_indicator measurableSet_Iio]
    change (∫ x : ℝ in Set.Ioo 0 1,
      Real.toNNReal (x ^ k) • A x ∂volume) = _
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    change ((Real.toNNReal (r ^ k) : NNReal) : ℝ) * A r = r ^ k * A r
    rw [Real.coe_toNNReal _ (pow_nonneg hr.1.le _)]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

lemma apm_m96j03_integrable_polar_laplacian {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hn : 0 < n) :
    Integrable
      (fun p : Metric.sphere (0 : apm_m96j03_E n) 1 × Set.Ioi (0 : ℝ) ↦
        if p.2.1 < 1 then
          apm_m96j03_laplacian φ (p.2.1 • (p.1.1 : apm_m96j03_E n))
        else 0)
      ((volume : Measure (apm_m96j03_E n)).toSphere.prod
        (Measure.volumeIoiPow (n - 1))) := by
  let g : apm_m96j03_E n → ℝ :=
    Set.indicator (Metric.ball (0 : apm_m96j03_E n) 1)
      (apm_m96j03_laplacian φ)
  have hg : Integrable g (volume : Measure (apm_m96j03_E n)) := by
    rw [integrable_indicator_iff measurableSet_ball]
    exact (apm_m96j03_laplacian_integrableOn_closedBall φ hφ 1).mono_set
      Metric.ball_subset_closedBall
  let U := homeomorphUnitSphereProd (apm_m96j03_E n)
  let μ₀ := (volume : Measure (apm_m96j03_E n)).comap
    (Subtype.val : ({0}ᶜ : Set (apm_m96j03_E n)) → apm_m96j03_E n)
  have hsub : Integrable
      (fun x : ({0}ᶜ : Set (apm_m96j03_E n)) ↦ g x.1) μ₀ := by
    have hemb : MeasurableEmbedding
        (Subtype.val : ({0}ᶜ : Set (apm_m96j03_E n)) → apm_m96j03_E n) :=
      MeasurableEmbedding.subtype_coe
        (measurableSet_singleton (0 : apm_m96j03_E n)).compl
    change Integrable (g ∘ (Subtype.val :
      ({0}ᶜ : Set (apm_m96j03_E n)) → apm_m96j03_E n)) μ₀
    rw [← hemb.integrable_map_iff, hemb.map_comap]
    simpa using hg.mono_measure Measure.restrict_le_self
  have htransport :=
    (Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (apm_m96j03_E n))).integrable_comp_emb
      U.measurableEmbedding
      (g := fun p ↦ g (U.symm p).1)
  have hp : Integrable (fun p ↦ g (U.symm p).1)
      ((volume : Measure (apm_m96j03_E n)).toSphere.prod
        (Measure.volumeIoiPow (n - 1))) := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using
      htransport.mp (by
        convert hsub using 1
        funext x
        exact congrArg g (congrArg Subtype.val (U.symm_apply_apply x)))
  convert hp using 1
  funext p
  simp only [g, U, Set.indicator, Metric.mem_ball, dist_zero_right,
    homeomorphUnitSphereProd_symm_apply_coe]
  have hω : ‖(p.1.1 : apm_m96j03_E n)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using p.1.2
  have hr : 0 < p.2.1 := p.2.2
  rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos hr]

lemma apm_m96j03_ball_green_pos {n : ℕ}
    (φ : apm_m96j03_E n → ℝ) (hφ : apm_m96j03_IsTestFunction φ)
    (hn : 0 < n) :
    (∫ x in Metric.closedBall (0 : apm_m96j03_E n) 1,
        apm_m96j03_laplacian φ x) =
      ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        fderiv ℝ φ ω ω ∂volume.toSphere := by
  let A : ℝ → ℝ := fun r ↦
    ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
      apm_m96j03_laplacian φ
        (r • (ω : apm_m96j03_E n)) ∂volume.toSphere
  rw [apm_m96j03_integral_closedBall_polar hn]
  rw [integral_prod_symm _
    (apm_m96j03_integrable_polar_laplacian φ hφ.1 hn)]
  change (∫ r : Set.Ioi (0 : ℝ),
    (∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
      if r.1 < 1 then
        apm_m96j03_laplacian φ
          (r.1 • (ω : apm_m96j03_E n))
      else 0 ∂volume.toSphere) ∂Measure.volumeIoiPow (n - 1)) = _
  have hinner :
      (fun r : Set.Ioi (0 : ℝ) ↦
        ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
          if r.1 < 1 then
            apm_m96j03_laplacian φ
              (r.1 • (ω : apm_m96j03_E n))
          else 0 ∂volume.toSphere) =
      fun r ↦ if r.1 < 1 then A r.1 else 0 := by
    funext r
    by_cases hr : r.1 < 1 <;> simp [hr, A]
  rw [hinner, apm_m96j03_integral_volumeIoiPow_cutoff
    (n - 1) A (apm_m96j03_continuous_radial_laplacian_average φ hφ.1)]
  exact apm_m96j03_intervalIntegral_radial_laplacian φ hφ hn

theorem apm_m96j03
    (n : ℕ) (φ : apm_m96j03_E n → ℝ)
    (hφ : apm_m96j03_IsTestFunction φ) :
    (∫ x : apm_m96j03_E n,
        apm_m96j03_ballIndicator x * apm_m96j03_laplacian φ x) =
      ∫ ω : Metric.sphere (0 : apm_m96j03_E n) 1,
        fderiv ℝ φ ω ω ∂(volume.toSphere) := by
  rcases n with _ | n
  · exact apm_m96j03_ball_green_zero φ
  · rw [apm_m96j03_integral_ballIndicator]
    exact apm_m96j03_ball_green_pos φ hφ (Nat.succ_pos n)
