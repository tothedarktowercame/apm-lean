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
lemma apm_t01J06_sphere_moments_aux_inst :
    ConstructionTargets.LinearGraphMeasure.domainMeasurable 3 =
      (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin 3))) := by
  unfold ConstructionTargets.LinearGraphMeasure.domainMeasurable
  exact BorelSpace.measurable_eq.symm

theorem apm_t01J06_sphere_moments :
    Integrable (fun q : apm_t01J06_S2 ↦ q.1 2 ^ 2) μHE[2] ∧
    Integrable (fun q : apm_t01J06_S2 ↦ q.1 2) μHE[2] ∧
    (∫ q : apm_t01J06_S2, q.1 2 ^ 2 ∂μHE[2]) = 4 * Real.pi / 3 ∧
    (∫ q : apm_t01J06_S2, q.1 2 ∂μHE[2]) = 0 := by
  have hinst := apm_t01J06_sphere_moments_aux_inst
  have hsraw : Integrable (fun q : apm_t01J06_S2 ↦ q.1 2 ^ 2) μH[2] := by
    convert ConstructionTargets.IntrinsicSphereFinite.continuous_integrable
      2 (by decide) (fun q : ConstructionTargets.IntrinsicSphereFinite.Sphere 2 ↦ q.1 2 ^ 2)
        (by fun_prop) using 1
    all_goals first | exact hinst | exact hinst.symm | exact proof_irrel_heq _ _
  have hlraw : Integrable (fun q : apm_t01J06_S2 ↦ q.1 2) μH[2] := by
    convert ConstructionTargets.IntrinsicSphereFinite.continuous_integrable
      2 (by decide) (fun q : ConstructionTargets.IntrinsicSphereFinite.Sphere 2 ↦ q.1 2)
        (by fun_prop) using 1
    all_goals first | exact hinst | exact hinst.symm | exact proof_irrel_heq _ _
  have hs : Integrable (fun q : apm_t01J06_S2 ↦ q.1 2 ^ 2) μHE[2] := by
    rw [MeasureTheory.Measure.euclideanHausdorffMeasure_def]
    exact hsraw.smul_measure_nnreal
  have hl : Integrable (fun q : apm_t01J06_S2 ↦ q.1 2) μHE[2] := by
    rw [MeasureTheory.Measure.euclideanHausdorffMeasure_def]
    exact hlraw.smul_measure_nnreal
  have hmass := apm_t02a05_euclideanHausdorff_unitSphere_mass
  have hmraw :
      (apm_t02a05_cM : ℝ) *
        ConstructionTargets.IntrinsicSphereSecondMoments.mass 2 = 4 * Real.pi := by
    rw [MeasureTheory.Measure.euclideanHausdorffMeasure_def, Measure.smul_apply,
      ENNReal.toReal_smul] at hmass
    change (apm_t02a05_cM : ℝ) *
      (Measure.hausdorffMeasure 2
        (Set.univ : Set (ConstructionTargets.IntrinsicSphereFinite.Sphere 2))).toReal =
        4 * Real.pi at hmass
    simpa [ConstructionTargets.IntrinsicSphereSecondMoments.mass,
      MeasureTheory.Measure.hausdorffMeasure_apply] using hmass
  have hsquare : (∫ q : apm_t01J06_S2, q.1 2 ^ 2 ∂μHE[2]) = 4 * Real.pi / 3 := by
    rw [MeasureTheory.Measure.euclideanHausdorffMeasure_def, integral_smul_nnreal_measure]
    have hm := ConstructionTargets.IntrinsicSphereSecondMoments.square_moment
      2 (by decide) (2 : Fin 3)
    have hm' : (∫ q : apm_t01J06_S2, q.1 2 ^ 2 ∂μH[2]) =
        ConstructionTargets.IntrinsicSphereSecondMoments.mass 2 / 3 := by
      convert hm using 3
      all_goals first | exact hinst | exact hinst.symm | norm_num
    change (apm_t02a05_cM : ℝ) *
      (∫ q : apm_t01J06_S2, q.1 2 ^ 2 ∂μH[2]) = 4 * Real.pi / 3
    rw [hm']
    calc
      _ = ((apm_t02a05_cM : ℝ) *
            ConstructionTargets.IntrinsicSphereSecondMoments.mass 2) / 3 := by ring
      _ = _ := by rw [hmraw]
  have hlinear : (∫ q : apm_t01J06_S2, q.1 2 ∂μHE[2]) = 0 := by
    rw [MeasureTheory.Measure.euclideanHausdorffMeasure_def, integral_smul_nnreal_measure]
    have ho := ConstructionTargets.IntrinsicSphereSecondMoments.odd_integral
      2 (2 : Fin 3) (fun q ↦ q.1 2) (by
        intro q
        change ConstructionTargets.IntrinsicSphereSecondMoments.reflection 2 2 q.1 2 = -q.1 2
        simp [ConstructionTargets.IntrinsicSphereSecondMoments.reflection_apply])
    have ho' : (∫ q : apm_t01J06_S2, q.1 2 ∂μH[2]) = 0 := by
      convert ho using 3
      all_goals first | exact hinst | exact hinst.symm
    change (apm_t02a05_cM : ℝ) *
      (∫ q : apm_t01J06_S2, q.1 2 ∂μH[2]) = 0
    rw [ho', mul_zero]
  exact ⟨hs, hl, hsquare, hlinear⟩

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
  have hq : ‖(q : apm_t01J06_E3)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using q.property
  have hproj (i j : Fin 3) :
      (apm_t01J06_tangentProjection q i : apm_t01J06_E3) j =
        (apm_t01J06_e i) j - q.1 i * q.1 j := by
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
  have hv (i j : Fin 3) :
      (fun k ↦ ((![apm_t01J06_tangentProjection q i,
        apm_t01J06_tangentProjection q j] k : apm_t01J06_sphereTangent q) :
          apm_t01J06_E3)) =
      ![apm_t01J06_e i - q.1 i • (q : apm_t01J06_E3),
        apm_t01J06_e j - q.1 j • (q : apm_t01J06_E3)] := by
    funext k
    fin_cases k <;> ext l <;> simp [hproj]
  have hswap (u v : apm_t01J06_E3) :
      eta q ![u, v] = - eta q ![v, u] := by
    change (eta q).toAlternatingMap ![u, v] =
      -(eta q).toAlternatingMap ![v, u]
    have h := (eta q).toAlternatingMap.map_swap (v := ![v, u])
      (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
    calc
      _ = (eta q).toAlternatingMap
          (![v, u] ∘ Equiv.swap (0 : Fin 2) (1 : Fin 2)) := by
            congr 1
            funext k
            fin_cases k <;> rfl
      _ = _ := h
  have hsmul (a : ℝ) (u v : apm_t01J06_E3) :
      eta q ![u, a • v] = a * eta q ![u, v] := by
    have h := (eta q).toAlternatingMap.toMultilinearMap.map_update_smul
      ![u, v] (1 : Fin 2) a v
    have hu : Function.update ![u, v] (1 : Fin 2) (a • v) = ![u, a • v] := by
      funext k
      fin_cases k <;> rfl
    have hv' : Function.update ![u, v] (1 : Fin 2) v = ![u, v] := by
      funext k
      fin_cases k <;> rfl
    rw [hu, hv'] at h
    simpa [smul_eq_mul] using h
  have hsmul_left (a : ℝ) (u v : apm_t01J06_E3) :
      eta q ![a • u, v] = a * eta q ![u, v] := by
    rw [hswap, hsmul, hswap]
    ring
  have hzero : eta q ![(q : apm_t01J06_E3), (q : apm_t01J06_E3)] = 0 := by
    have h := hswap (q : apm_t01J06_E3) (q : apm_t01J06_E3)
    linarith
  unfold apm_t01J06_orientedCoefficient
  rw [hp, hp, hp]
  rw [hv 1 2, hv 0 2, hv 0 1]
  simp
  rw [hswap (q.1 1 • (q : apm_t01J06_E3))
      (apm_t01J06_e 2 - q.1 2 • (q : apm_t01J06_E3)),
    hswap (q.1 0 • (q : apm_t01J06_E3))
      (apm_t01J06_e 2 - q.1 2 • (q : apm_t01J06_E3)),
    hswap (q.1 0 • (q : apm_t01J06_E3))
      (apm_t01J06_e 1 - q.1 1 • (q : apm_t01J06_E3))]
  simp
  simp only [hsmul]
  rw [hswap (apm_t01J06_e 1)
      (apm_t01J06_e 2 - q.1 2 • (q : apm_t01J06_E3)),
    hswap (apm_t01J06_e 0)
      (apm_t01J06_e 2 - q.1 2 • (q : apm_t01J06_E3)),
    hswap (apm_t01J06_e 0)
      (apm_t01J06_e 1 - q.1 1 • (q : apm_t01J06_E3))]
  simp
  simp only [hsmul, hsmul_left, hzero, mul_zero]
  rw [hswap (q : apm_t01J06_E3) (apm_t01J06_e 0),
    hswap (q : apm_t01J06_E3) (apm_t01J06_e 1),
    hswap (apm_t01J06_e 2) (apm_t01J06_e 1),
    hswap (apm_t01J06_e 2) (apm_t01J06_e 0),
    hswap (apm_t01J06_e 1) (apm_t01J06_e 0)]
  ring

/-- Seat: closedness in components. Evaluate `extDeriv_apply` on `![e 0, e 1, e 2]`, and use
`Fin.sum_univ_three` with the `Fin.removeNth` values. -/
theorem apm_t01J06_closed_divergence_free
    (eta : apm_t01J06_AmbientForm2) (hs : ContDiff ℝ (⊤ : ℕ∞) eta) (hc : extDeriv eta = 0)
    (x : apm_t01J06_E3) :
    apm_t01J06_partial 0 (fun y ↦ eta y ![apm_t01J06_e 1, apm_t01J06_e 2]) x -
      apm_t01J06_partial 1 (fun y ↦ eta y ![apm_t01J06_e 0, apm_t01J06_e 2]) x +
      apm_t01J06_partial 2 (fun y ↦ eta y ![apm_t01J06_e 0, apm_t01J06_e 1]) x = 0 := by
  have hd : DifferentiableAt ℝ eta x := (hs.differentiable (by simp)) x
  have hclosed : extDeriv eta x ![apm_t01J06_e 0, apm_t01J06_e 1,
      apm_t01J06_e 2] = 0 := by
    rw [hc]
    rfl
  rw [extDeriv_apply hd] at hclosed
  have hv1 : Fin.removeNth (1 : Fin 3)
      ![apm_t01J06_e 0, apm_t01J06_e 1, apm_t01J06_e 2] =
      ![apm_t01J06_e 0, apm_t01J06_e 2] := by
    ext i
    fin_cases i <;> rfl
  have hv2 : Fin.removeNth (2 : Fin 3)
      ![apm_t01J06_e 0, apm_t01J06_e 1, apm_t01J06_e 2] =
      ![apm_t01J06_e 0, apm_t01J06_e 1] := by
    ext i
    fin_cases i <;> rfl
  rw [Fin.sum_univ_three] at hclosed
  rw [hv1, hv2] at hclosed
  simpa [apm_t01J06_partial] using hclosed

/-- Seat: differentiation under the integral on the compact interval. `hasFDerivAt_integral_of_dominated_of_fderiv_le`
(or the interval version) with the bound from continuity of `fderiv g` on `[0,1] × closedBall x 1`; continuity of the
derivative is continuity of a parametric integral (`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous`
or `continuous_parametric_integral_of_continuous`). -/
-- BEGIN SEAT AREA
theorem apm_t01J06_parametric_integral (g : ℝ × apm_t01J06_E3 → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ 1 (fun x ↦ ∫ t in (0 : ℝ)..1, g (t, x)) ∧
    ∀ x v, fderiv ℝ (fun y ↦ ∫ t in (0 : ℝ)..1, g (t, y)) x v =
      ∫ t in (0 : ℝ)..1, fderiv ℝ (fun y ↦ g (t, y)) x v := by
  sorry
-- END SEAT AREA

/-- The integrand of the cone formula: `t • (F (t x) × x)`, component `k`. -/
def apm_t01J06_coneField (F : Fin 3 → apm_t01J06_E3 → ℝ) (k : Fin 3)
    (p : ℝ × apm_t01J06_E3) : ℝ :=
  p.1 * (F (k + 1) (p.1 • p.2) * p.2 (k + 2) - F (k + 2) (p.1 • p.2) * p.2 (k + 1))

/-- Seat: the pointwise cone identity. By the product and chain rules, the left side is
`2 t F i (t x) + t² (∂ (i + 1) F i x (i + 1) + ∂ (i + 2) F i x (i + 2)) - t² x i (∂ (i + 1) F (i + 1) + ∂ (i + 2) F (i + 2))`,
all derivatives at `t x`. `hdiv` turns the last bracket into `-∂ i F i`, giving `2 t F i + t² Σ x j ∂ j F i`, the
derivative in `t` of `t² F i (t x)`. Do `i` generally, or `fin_cases i`. -/
theorem apm_t01J06_cone_identity (F : Fin 3 → apm_t01J06_E3 → ℝ)
    (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (hdiv : ∀ x, apm_t01J06_partial 0 (F 0) x + apm_t01J06_partial 1 (F 1) x +
      apm_t01J06_partial 2 (F 2) x = 0) (i : Fin 3) (t : ℝ) (x : apm_t01J06_E3) :
    apm_t01J06_partial (i + 1) (fun y ↦ apm_t01J06_coneField F (i + 2) (t, y)) x -
      apm_t01J06_partial (i + 2) (fun y ↦ apm_t01J06_coneField F (i + 1) (t, y)) x =
    deriv (fun s : ℝ ↦ s ^ 2 * F i (s • x)) t := by
  sorry

/-- Seat: a divergence-free field is a curl. Take `A k x = ∫ t in 0..1, apm_t01J06_coneField F k (t, x)`.
`apm_t01J06_coneField` is smooth (`fun_prop`, coordinates are continuous linear). `apm_t01J06_parametric_integral`
gives `ContDiff` and moves `partial` inside; `integral_sub`, `apm_t01J06_cone_identity`, and the FTC
`intervalIntegral.integral_deriv_eq_sub'` give `1 ^ 2 * F i (1 • x) - 0`. -/
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
def apm_t01J06_rotation_derivative_integral_aux_rot (k : Fin 3) (t : ℝ)
    (x : apm_t01J06_E3) : apm_t01J06_E3 :=
  match k with
  | 0 => WithLp.toLp 2 ![x 0, Real.cos t * x 1 - Real.sin t * x 2,
      Real.sin t * x 1 + Real.cos t * x 2]
  | 1 => WithLp.toLp 2 ![Real.cos t * x 0 + Real.sin t * x 2, x 1,
      -Real.sin t * x 0 + Real.cos t * x 2]
  | 2 => WithLp.toLp 2 ![Real.cos t * x 0 - Real.sin t * x 1,
      Real.sin t * x 0 + Real.cos t * x 1, x 2]

lemma apm_t01J06_rotation_derivative_integral_aux_rot_zero (k : Fin 3)
    (x : apm_t01J06_E3) :
    apm_t01J06_rotation_derivative_integral_aux_rot k 0 x = x := by
  fin_cases k <;> ext i <;> fin_cases i <;>
    simp [apm_t01J06_rotation_derivative_integral_aux_rot]

lemma apm_t01J06_rotation_derivative_integral_aux_rot_add (k : Fin 3) (s t : ℝ)
    (x : apm_t01J06_E3) :
    apm_t01J06_rotation_derivative_integral_aux_rot k s
      (apm_t01J06_rotation_derivative_integral_aux_rot k t x) =
        apm_t01J06_rotation_derivative_integral_aux_rot k (s + t) x := by
  fin_cases k <;> ext i <;> fin_cases i <;>
    simp [apm_t01J06_rotation_derivative_integral_aux_rot, Real.sin_add, Real.cos_add] <;> ring

lemma apm_t01J06_rotation_derivative_integral_aux_rot_neg (k : Fin 3) (t : ℝ)
    (x : apm_t01J06_E3) :
    apm_t01J06_rotation_derivative_integral_aux_rot k (-t)
      (apm_t01J06_rotation_derivative_integral_aux_rot k t x) = x := by
  rw [apm_t01J06_rotation_derivative_integral_aux_rot_add]
  simp [apm_t01J06_rotation_derivative_integral_aux_rot_zero]

lemma apm_t01J06_rotation_derivative_integral_aux_norm (k : Fin 3) (t : ℝ)
    (x : apm_t01J06_E3) :
    ‖apm_t01J06_rotation_derivative_integral_aux_rot k t x‖ = ‖x‖ := by
  have h : ‖apm_t01J06_rotation_derivative_integral_aux_rot k t x‖ ^ 2 = ‖x‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    fin_cases k <;>
      simp [apm_t01J06_rotation_derivative_integral_aux_rot] <;>
      nlinarith [Real.sin_sq_add_cos_sq t]
  nlinarith [norm_nonneg x,
    norm_nonneg (apm_t01J06_rotation_derivative_integral_aux_rot k t x)]

lemma apm_t01J06_rotation_derivative_integral_aux_sub (k : Fin 3) (t : ℝ)
    (x y : apm_t01J06_E3) :
    apm_t01J06_rotation_derivative_integral_aux_rot k t (x - y) =
      apm_t01J06_rotation_derivative_integral_aux_rot k t x -
        apm_t01J06_rotation_derivative_integral_aux_rot k t y := by
  fin_cases k <;> ext i <;> fin_cases i <;>
    simp [apm_t01J06_rotation_derivative_integral_aux_rot] <;> ring

lemma apm_t01J06_rotation_derivative_integral_aux_isometry (k : Fin 3) (t : ℝ) :
    Isometry (apm_t01J06_rotation_derivative_integral_aux_rot k t) := by
  rw [isometry_iff_dist_eq]
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← apm_t01J06_rotation_derivative_integral_aux_sub,
    apm_t01J06_rotation_derivative_integral_aux_norm]

lemma apm_t01J06_rotation_derivative_integral_aux_hasDeriv (k : Fin 3)
    (x : apm_t01J06_E3) :
    HasDerivAt (fun t : ℝ ↦ apm_t01J06_rotation_derivative_integral_aux_rot k t x)
      (apm_t01J06_rotField k x) 0 := by
  fin_cases k
  · let a : apm_t01J06_E3 := WithLp.toLp 2 ![0, x 1, x 2]
    let b : apm_t01J06_E3 := WithLp.toLp 2 ![0, -x 2, x 1]
    let c : apm_t01J06_E3 := WithLp.toLp 2 ![x 0, 0, 0]
    have h := ((hasDerivAt_const (x := 0) c).add
      ((Real.hasDerivAt_cos 0).smul_const a)).add
        ((Real.hasDerivAt_sin 0).smul_const b)
    convert h using 1
    · funext t
      ext i
      fin_cases i <;> simp [a, b, c, apm_t01J06_rotation_derivative_integral_aux_rot] <;> ring
    · ext i
      fin_cases i <;> simp [a, b, c, apm_t01J06_rotField]
  · let a : apm_t01J06_E3 := WithLp.toLp 2 ![x 0, 0, x 2]
    let b : apm_t01J06_E3 := WithLp.toLp 2 ![x 2, 0, -x 0]
    let c : apm_t01J06_E3 := WithLp.toLp 2 ![0, x 1, 0]
    have h := ((hasDerivAt_const (x := 0) c).add
      ((Real.hasDerivAt_cos 0).smul_const a)).add
        ((Real.hasDerivAt_sin 0).smul_const b)
    convert h using 1
    · funext t
      ext i
      fin_cases i <;> simp [a, b, c, apm_t01J06_rotation_derivative_integral_aux_rot] <;> ring
    · ext i
      fin_cases i <;> simp [a, b, c, apm_t01J06_rotField]
  · let a : apm_t01J06_E3 := WithLp.toLp 2 ![x 0, x 1, 0]
    let b : apm_t01J06_E3 := WithLp.toLp 2 ![-x 1, x 0, 0]
    let c : apm_t01J06_E3 := WithLp.toLp 2 ![0, 0, x 2]
    have h := ((hasDerivAt_const (x := 0) c).add
      ((Real.hasDerivAt_cos 0).smul_const a)).add
        ((Real.hasDerivAt_sin 0).smul_const b)
    convert h using 1
    · funext t
      ext i
      fin_cases i <;> simp [a, b, c, apm_t01J06_rotation_derivative_integral_aux_rot] <;> ring
    · ext i
      fin_cases i <;> simp [a, b, c, apm_t01J06_rotField]

lemma apm_t01J06_rotation_derivative_integral_aux_key (k : Fin 3)
    (f : apm_t01J06_E3 → ℝ) (hf : ContDiff ℝ 1 f) :
    (∫ q : apm_t01J06_S2, fderiv ℝ f q.1 (apm_t01J06_rotField k q.1) ∂μHE[2]) = 0 := by
  sorry

theorem apm_t01J06_rotation_derivative_integral (k : Fin 3) (f : apm_t01J06_E3 → ℝ)
    (hf : ContDiff ℝ 1 f) :
    (∫ q : apm_t01J06_S2, fderiv ℝ f q.1 (apm_t01J06_rotField k q.1) ∂μHE[2]) = 0 := by
  exact apm_t01J06_rotation_derivative_integral_aux_key k f hf

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
def apm_t01J06_exists_closed_product_extension_aux_scalar
    (x : apm_t01J06_E3) : ℝ :=
  (x 2 / ‖x‖ + 3) * (x 2 / ‖x‖)

def apm_t01J06_exists_closed_product_extension_aux_volume :
    apm_t01J06_E3 [⋀^Fin 3]→L[ℝ] ℝ where
  toAlternatingMap := Matrix.detRowAlternating.compLinearMap
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ)).toLinearMap
  cont := by
    change Continuous (fun v : Fin 3 → apm_t01J06_E3 ↦ Matrix.det (fun i j ↦ v i j))
    fun_prop

def apm_t01J06_exists_closed_product_extension_aux_solidAngle
    (x : apm_t01J06_E3) : apm_t01J06_E3 [⋀^Fin 2]→L[ℝ] ℝ :=
  (‖x‖ ^ 3)⁻¹ •
    apm_t01J06_exists_closed_product_extension_aux_volume.curryLeft x

def apm_t01J06_exists_closed_product_extension_aux_eta :
    apm_t01J06_AmbientForm2 := fun x ↦
  apm_t01J06_exists_closed_product_extension_aux_scalar x •
    apm_t01J06_exists_closed_product_extension_aux_solidAngle x

def apm_t01J06_exists_closed_product_extension_aux_Z :
    apm_t01J06_AmbientProductForm2 := fun x ↦
  (apm_t01J06_exists_closed_product_extension_aux_eta x.1).compContinuousLinearMap
    (ContinuousLinearMap.fst ℝ apm_t01J06_E3 apm_t01J06_E2)

lemma apm_t01J06_exists_closed_product_extension_aux_smooth_closed :
    ContDiffOn ℝ (⊤ : ℕ∞) apm_t01J06_exists_closed_product_extension_aux_Z
      {x : apm_t01J06_E5 | x.1 ≠ 0} ∧
    ∀ x ∈ {x : apm_t01J06_E5 | x.1 ≠ 0},
      extDeriv apm_t01J06_exists_closed_product_extension_aux_Z x = 0 := by
  sorry

lemma apm_t01J06_exists_closed_product_extension_aux_restrict
    (omega : apm_t01J06_AmbientForm2) (homega : apm_t01J06_isOmega omega)
    (alpha : apm_t01J06_SphereForm2)
    (halpha : apm_t01J06_isInclusionPullback omega alpha)
    (p : apm_t01J06_S1) :
    apm_t01J06_isJPullback p
      (apm_t01J06_productRestriction
        apm_t01J06_exists_closed_product_extension_aux_Z) alpha := by
  sorry

theorem apm_t01J06_exists_closed_product_extension
    (omega : apm_t01J06_AmbientForm2) (homega : apm_t01J06_isOmega omega)
    (alpha : apm_t01J06_SphereForm2)
    (halpha : apm_t01J06_isInclusionPullback omega alpha)
    (p : apm_t01J06_S1) : apm_t01J06_IsClosedProductExtension p alpha := by
  refine ⟨{x : apm_t01J06_E5 | x.1 ≠ 0},
    apm_t01J06_exists_closed_product_extension_aux_Z, ?_, ?_,
    apm_t01J06_exists_closed_product_extension_aux_smooth_closed.1,
    apm_t01J06_exists_closed_product_extension_aux_smooth_closed.2, ?_⟩
  · exact isOpen_ne.preimage continuous_fst
  · intro qp
    change (qp.1 : apm_t01J06_E3) ≠ 0
    intro h
    have hnorm : ‖(qp.1 : apm_t01J06_E3)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using qp.1.property
    rw [h, norm_zero] at hnorm
    norm_num at hnorm
  · exact apm_t01J06_exists_closed_product_extension_aux_restrict
      omega homega alpha halpha p

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
