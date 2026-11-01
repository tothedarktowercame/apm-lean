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
theorem apm_t01J06_parametric_integral (g : ℝ × apm_t01J06_E3 → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ 1 (fun x ↦ ∫ t in (0 : ℝ)..1, g (t, x)) ∧
    ∀ x v, fderiv ℝ (fun y ↦ ∫ t in (0 : ℝ)..1, g (t, y)) x v =
      ∫ t in (0 : ℝ)..1, fderiv ℝ (fun y ↦ g (t, y)) x v := by
  let D : apm_t01J06_E3 → ℝ → apm_t01J06_E3 →L[ℝ] ℝ := fun x t ↦
    (fderiv ℝ g (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ apm_t01J06_E3)
  have hD_cont : Continuous (Function.uncurry D) := by
    dsimp [D]
    have hf : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)
    fun_prop
  have hD_eq (t : ℝ) (x : apm_t01J06_E3) :
      D x t = fderiv ℝ (fun y ↦ g (t, y)) x := by
    have ht : HasFDerivAt (fun y : apm_t01J06_E3 ↦ (t, y))
        (ContinuousLinearMap.inr ℝ ℝ apm_t01J06_E3) x :=
      hasFDerivAt_prodMk_right t x
    exact ((hg.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x ht).fderiv.symm
  have hderiv_cont : Continuous (fun x ↦ ∫ t in (0 : ℝ)..1, D x t) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hD_cont 0 1
  have h_has (x : apm_t01J06_E3) : HasFDerivAt
      (fun y ↦ ∫ t in (0 : ℝ)..1, g (t, y)) (∫ t in (0 : ℝ)..1, D x t) x := by
    let K : Set (apm_t01J06_E3 × ℝ) := Metric.closedBall x 1 ×ˢ Set.Icc 0 1
    have hK : IsCompact K := (isCompact_closedBall x 1).prod isCompact_Icc
    obtain ⟨M, hM⟩ := hK.bddAbove_image hD_cont.norm.continuousOn
    apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun y t ↦ g (t, y)) (F' := D) (bound := fun _ ↦ M)
      (Metric.closedBall_mem_nhds x zero_lt_one)
    · filter_upwards with y
      exact (hg.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · exact (hg.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1
    · exact (hD_cont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · filter_upwards with t ht
      intro y hy
      have ht0 : 0 ≤ t := by
        norm_num at ht
        exact ht.1.le
      have ht1 : t ≤ 1 := by
        norm_num at ht
        exact ht.2
      have hp : (y, t) ∈ K := ⟨hy, ht0, ht1⟩
      have hi : ‖D y t‖ ∈ (fun p ↦ ‖Function.uncurry D p‖) '' K :=
        ⟨(y, t), hp, rfl⟩
      exact hM hi
    · exact (continuous_const : Continuous (fun _ : ℝ ↦ M)).intervalIntegrable 0 1
    · apply Filter.Eventually.of_forall
      intro t ht y hy
      change HasFDerivAt (fun z ↦ g (t, z)) (D y t) y
      exact (hg.differentiable (by simp)).differentiableAt.hasFDerivAt.comp y
        (hasFDerivAt_prodMk_right t y)
  have hcd : ContDiff ℝ 1 (fun x ↦ ∫ t in (0 : ℝ)..1, g (t, x)) := by
    rw [contDiff_one_iff_hasFDerivAt]
    exact ⟨(fun x ↦ ∫ t in (0 : ℝ)..1, D x t), hderiv_cont, h_has⟩
  refine ⟨hcd, fun x v ↦ ?_⟩
  rw [(h_has x).fderiv]
  have hDi : IntervalIntegrable (fun t ↦ D x t) volume 0 1 :=
    (hD_cont.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  rw [ContinuousLinearMap.intervalIntegral_apply hDi v]
  simp_rw [hD_eq]

/-- The integrand of the cone formula: `t • (F (t x) × x)`, component `k`. -/
def apm_t01J06_coneField (F : Fin 3 → apm_t01J06_E3 → ℝ) (k : Fin 3)
    (p : ℝ × apm_t01J06_E3) : ℝ :=
  p.1 * (F (k + 1) (p.1 • p.2) * p.2 (k + 2) - F (k + 2) (p.1 • p.2) * p.2 (k + 1))

/-- Seat: the pointwise cone identity. By the product and chain rules, the left side is
`2 t F i (t x) + t² (∂ (i + 1) F i x (i + 1) + ∂ (i + 2) F i x (i + 2)) - t² x i (∂ (i + 1) F (i + 1) + ∂ (i + 2) F (i + 2))`,
all derivatives at `t x`. `hdiv` turns the last bracket into `-∂ i F i`, giving `2 t F i + t² Σ x j ∂ j F i`, the
derivative in `t` of `t² F i (t x)`. Do `i` generally, or `fin_cases i`. -/
/- Chain rule for the `t • y` composition, applied to a vector. -/
theorem apm_t01J06_cone_identity_aux_comp (g : apm_t01J06_E3 → ℝ) (t : ℝ) (x : apm_t01J06_E3)
    (hg : DifferentiableAt ℝ g (t • x)) (v : apm_t01J06_E3) :
    fderiv ℝ (fun y ↦ g (t • y)) x v = t * fderiv ℝ g (t • x) v := by
  have hlin : HasFDerivAt (fun y : apm_t01J06_E3 ↦ t • y)
      (t • ContinuousLinearMap.id ℝ apm_t01J06_E3) x :=
    (t • ContinuousLinearMap.id ℝ apm_t01J06_E3).hasFDerivAt
  have hcomp := hg.hasFDerivAt.comp x hlin
  have h := hcomp.fderiv
  have heq : (fun y ↦ g (t • y)) = g ∘ (fun y : apm_t01J06_E3 ↦ t • y) := rfl
  rw [heq, h]
  simp [ContinuousLinearMap.comp_apply, smul_eq_mul]

/-- Derivative of a coordinate function. -/
theorem apm_t01J06_cone_identity_aux_coord (k : Fin 3) (x v : apm_t01J06_E3) :
    fderiv ℝ (fun y ↦ y k) x v = v k := by
  have heq : (fun y : apm_t01J06_E3 ↦ y k) =
      ⇑(PiLp.proj (2 : ℝ≥0∞) (fun _ : Fin 3 ↦ ℝ) k : apm_t01J06_E3 →L[ℝ] ℝ) := by
    funext y
    rfl
  rw [heq, ContinuousLinearMap.fderiv]
  rfl

/-- `x` in the basis of the `e j`. -/
theorem apm_t01J06_cone_identity_aux_basis (x : apm_t01J06_E3) :
    x = x 0 • apm_t01J06_e 0 + x 1 • apm_t01J06_e 1 + x 2 • apm_t01J06_e 2 := by
  ext k
  fin_cases k <;>
    simp [apm_t01J06_e, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      EuclideanSpace.single_apply]

/-- `fderiv g z x` expanded in partial derivatives. -/
theorem apm_t01J06_cone_identity_aux_decomp (g : apm_t01J06_E3 → ℝ) (z x : apm_t01J06_E3) :
    fderiv ℝ g z x = x 0 * apm_t01J06_partial 0 g z +
      x 1 * apm_t01J06_partial 1 g z + x 2 * apm_t01J06_partial 2 g z := by
  conv_lhs => rw [apm_t01J06_cone_identity_aux_basis x]
  simp [map_add, map_smul, smul_eq_mul, apm_t01J06_partial]

/-- Derivative of `s ↦ s ^ 2 * g (s • x)`. -/
theorem apm_t01J06_cone_identity_aux_rhs (g : apm_t01J06_E3 → ℝ) (t : ℝ) (x : apm_t01J06_E3)
    (hg : ∀ s : ℝ, DifferentiableAt ℝ g (s • x)) :
    deriv (fun s : ℝ ↦ s ^ 2 * g (s • x)) t =
      2 * t * g (t • x) + t ^ 2 * fderiv ℝ g (t • x) x := by
  have hv : HasDerivAt (fun s : ℝ ↦ s • x) x t := by
    simpa using (hasDerivAt_id t).smul_const x
  have hvg : HasDerivAt (fun s : ℝ ↦ g (s • x)) (fderiv ℝ g (t • x) x) t := by
    have h := (hg t).hasFDerivAt.comp_hasDerivAt t hv
    simpa using h
  have hu : HasDerivAt (fun s : ℝ ↦ s ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t)
  have h := hu.mul hvg
  rw [show (fun s : ℝ ↦ s ^ 2 * g (s • x)) =
      (fun s : ℝ ↦ s ^ 2) * (fun s : ℝ ↦ g (s • x)) from rfl, h.deriv]

/-- `fderiv` of the cone-field integrand `y ↦ t * (g (t • y) * y a - h (t • y) * y b)`. -/
theorem apm_t01J06_cone_identity_aux_expand (t : ℝ) (x v : apm_t01J06_E3)
    (g h : apm_t01J06_E3 → ℝ)
    (hg : DifferentiableAt ℝ g (t • x)) (hh : DifferentiableAt ℝ h (t • x))
    (a b : Fin 3) :
    fderiv ℝ (fun y ↦ t * (g (t • y) * y a - h (t • y) * y b)) x v =
      t * ((t * fderiv ℝ g (t • x) v) * x a + g (t • x) * v a -
        ((t * fderiv ℝ h (t • x) v) * x b + h (t • x) * v b)) := by
  have hg' : DifferentiableAt ℝ (fun y ↦ g (t • y)) x := by
    apply DifferentiableAt.comp x hg
    exact (t • ContinuousLinearMap.id ℝ apm_t01J06_E3).differentiableAt
  have hh' : DifferentiableAt ℝ (fun y ↦ h (t • y)) x := by
    apply DifferentiableAt.comp x hh
    exact (t • ContinuousLinearMap.id ℝ apm_t01J06_E3).differentiableAt
  have hca : DifferentiableAt ℝ (fun y : apm_t01J06_E3 ↦ y a) x :=
    (PiLp.proj (2 : ℝ≥0∞) (fun _ : Fin 3 ↦ ℝ) a : apm_t01J06_E3 →L[ℝ] ℝ).differentiableAt
  have hcb : DifferentiableAt ℝ (fun y : apm_t01J06_E3 ↦ y b) x :=
    (PiLp.proj (2 : ℝ≥0∞) (fun _ : Fin 3 ↦ ℝ) b : apm_t01J06_E3 →L[ℝ] ℝ).differentiableAt
  have h1 : DifferentiableAt ℝ (fun y ↦ g (t • y) * y a) x := hg'.mul hca
  have h2 : DifferentiableAt ℝ (fun y ↦ h (t • y) * y b) x := hh'.mul hcb
  have hA : DifferentiableAt ℝ (fun y ↦ g (t • y) * y a - h (t • y) * y b) x :=
    (hg'.mul hca).sub (hh'.mul hcb)
  rw [fderiv_const_mul hA t]
  rw [fderiv_fun_sub h1 h2, fderiv_fun_mul hg' hca, fderiv_fun_mul hh' hcb]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, smul_eq_mul]
  rw [apm_t01J06_cone_identity_aux_comp g t x hg v,
    apm_t01J06_cone_identity_aux_comp h t x hh v,
    apm_t01J06_cone_identity_aux_coord a x v, apm_t01J06_cone_identity_aux_coord b x v]
  ring

theorem apm_t01J06_cone_identity (F : Fin 3 → apm_t01J06_E3 → ℝ)
    (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (hdiv : ∀ x, apm_t01J06_partial 0 (F 0) x + apm_t01J06_partial 1 (F 1) x +
      apm_t01J06_partial 2 (F 2) x = 0) (i : Fin 3) (t : ℝ) (x : apm_t01J06_E3) :
    apm_t01J06_partial (i + 1) (fun y ↦ apm_t01J06_coneField F (i + 2) (t, y)) x -
      apm_t01J06_partial (i + 2) (fun y ↦ apm_t01J06_coneField F (i + 1) (t, y)) x =
    deriv (fun s : ℝ ↦ s ^ 2 * F i (s • x)) t := by
  have hdiff : ∀ j : Fin 3, ∀ s : ℝ, DifferentiableAt ℝ (F j) (s • x) :=
    fun j s ↦ ((hF j).differentiable (by simp)) (s • x)
  have hd0 := hdiv (t • x)
  simp only [apm_t01J06_partial] at hd0 ⊢
  fin_cases i
  · -- i = 0
    have eA := apm_t01J06_cone_identity_aux_expand t x (apm_t01J06_e 1) (F 0) (F 1)
      (hdiff 0 t) (hdiff 1 t) 1 0
    have eB := apm_t01J06_cone_identity_aux_expand t x (apm_t01J06_e 2) (F 2) (F 0)
      (hdiff 2 t) (hdiff 0 t) 0 2
    have eR := apm_t01J06_cone_identity_aux_rhs (F 0) t x (hdiff 0)
    have eD := apm_t01J06_cone_identity_aux_decomp (F 0) (t • x) x
    have hc1 : apm_t01J06_e (1 : Fin 3) (1 : Fin 3) = 1 := by
      simp [apm_t01J06_e, EuclideanSpace.single_apply]
    have hc2 : apm_t01J06_e (1 : Fin 3) (0 : Fin 3) = 0 := by
      simp [apm_t01J06_e, EuclideanSpace.single_apply]
    have hc3 : apm_t01J06_e (2 : Fin 3) (0 : Fin 3) = 0 := by
      simp [apm_t01J06_e, EuclideanSpace.single_apply]
    have hc4 : apm_t01J06_e (2 : Fin 3) (2 : Fin 3) = 1 := by
      simp [apm_t01J06_e, EuclideanSpace.single_apply]
    show fderiv ℝ (fun y ↦ apm_t01J06_coneField F 2 (t, y)) x (apm_t01J06_e 1) -
        fderiv ℝ (fun y ↦ apm_t01J06_coneField F 1 (t, y)) x (apm_t01J06_e 2) =
        deriv (fun s : ℝ ↦ s ^ 2 * F 0 (s • x)) t
    have eA' : fderiv ℝ (fun y ↦ apm_t01J06_coneField F 2 (t, y)) x (apm_t01J06_e 1) =
        t * ((t * fderiv ℝ (F 0) (t • x) (apm_t01J06_e 1)) * x 1 +
          F 0 (t • x) * apm_t01J06_e 1 1 -
          ((t * fderiv ℝ (F 1) (t • x) (apm_t01J06_e 1)) * x 0 +
          F 1 (t • x) * apm_t01J06_e 1 0)) := eA
    have eB' : fderiv ℝ (fun y ↦ apm_t01J06_coneField F 1 (t, y)) x (apm_t01J06_e 2) =
        t * ((t * fderiv ℝ (F 2) (t • x) (apm_t01J06_e 2)) * x 0 +
          F 2 (t • x) * apm_t01J06_e 2 0 -
          ((t * fderiv ℝ (F 0) (t • x) (apm_t01J06_e 2)) * x 2 +
          F 0 (t • x) * apm_t01J06_e 2 2)) := eB
    rw [eA', eB', eR, eD, hc1, hc2, hc3, hc4]
    simp only [apm_t01J06_partial]
    linear_combination (-t ^ 2 * x 0) * hd0
  · -- i = 1
    have eA := apm_t01J06_cone_identity_aux_expand t x (apm_t01J06_e 2) (F 1) (F 2)
      (hdiff 1 t) (hdiff 2 t) 2 1
    have eB := apm_t01J06_cone_identity_aux_expand t x (apm_t01J06_e 0) (F 0) (F 1)
      (hdiff 0 t) (hdiff 1 t) 1 0
    have eR := apm_t01J06_cone_identity_aux_rhs (F 1) t x (hdiff 1)
    have eD := apm_t01J06_cone_identity_aux_decomp (F 1) (t • x) x
    have hc1 : apm_t01J06_e (2 : Fin 3) (2 : Fin 3) = 1 := by
      simp [apm_t01J06_e, EuclideanSpace.single_apply]
    have hc2 : apm_t01J06_e (2 : Fin 3) (1 : Fin 3) = 0 := by
      simp [apm_t01J06_e, EuclideanSpace.single_apply]
    have hc3 : apm_t01J06_e (0 : Fin 3) (1 : Fin 3) = 0 := by
      simp [apm_t01J06_e, EuclideanSpace.single_apply]
    have hc4 : apm_t01J06_e (0 : Fin 3) (0 : Fin 3) = 1 := by
      simp [apm_t01J06_e, EuclideanSpace.single_apply]
    show fderiv ℝ (fun y ↦ apm_t01J06_coneField F 0 (t, y)) x (apm_t01J06_e 2) -
        fderiv ℝ (fun y ↦ apm_t01J06_coneField F 2 (t, y)) x (apm_t01J06_e 0) =
        deriv (fun s : ℝ ↦ s ^ 2 * F 1 (s • x)) t
    have eA' : fderiv ℝ (fun y ↦ apm_t01J06_coneField F 0 (t, y)) x (apm_t01J06_e 2) =
        t * ((t * fderiv ℝ (F 1) (t • x) (apm_t01J06_e 2)) * x 2 +
          F 1 (t • x) * apm_t01J06_e 2 2 -
          ((t * fderiv ℝ (F 2) (t • x) (apm_t01J06_e 2)) * x 1 +
          F 2 (t • x) * apm_t01J06_e 2 1)) := eA
    have eB' : fderiv ℝ (fun y ↦ apm_t01J06_coneField F 2 (t, y)) x (apm_t01J06_e 0) =
        t * ((t * fderiv ℝ (F 0) (t • x) (apm_t01J06_e 0)) * x 1 +
          F 0 (t • x) * apm_t01J06_e 0 1 -
          ((t * fderiv ℝ (F 1) (t • x) (apm_t01J06_e 0)) * x 0 +
          F 1 (t • x) * apm_t01J06_e 0 0)) := eB
    rw [eA', eB', eR, eD, hc1, hc2, hc3, hc4]
    simp only [apm_t01J06_partial]
    linear_combination (-t ^ 2 * x 1) * hd0
  · -- i = 2
    have eA := apm_t01J06_cone_identity_aux_expand t x (apm_t01J06_e 0) (F 2) (F 0)
      (hdiff 2 t) (hdiff 0 t) 0 2
    have eB := apm_t01J06_cone_identity_aux_expand t x (apm_t01J06_e 1) (F 1) (F 2)
      (hdiff 1 t) (hdiff 2 t) 2 1
    have eR := apm_t01J06_cone_identity_aux_rhs (F 2) t x (hdiff 2)
    have eD := apm_t01J06_cone_identity_aux_decomp (F 2) (t • x) x
    have hc1 : apm_t01J06_e (0 : Fin 3) (0 : Fin 3) = 1 := by
      simp [apm_t01J06_e, EuclideanSpace.single_apply]
    have hc2 : apm_t01J06_e (0 : Fin 3) (2 : Fin 3) = 0 := by
      simp [apm_t01J06_e, EuclideanSpace.single_apply]
    have hc3 : apm_t01J06_e (1 : Fin 3) (2 : Fin 3) = 0 := by
      simp [apm_t01J06_e, EuclideanSpace.single_apply]
    have hc4 : apm_t01J06_e (1 : Fin 3) (1 : Fin 3) = 1 := by
      simp [apm_t01J06_e, EuclideanSpace.single_apply]
    show fderiv ℝ (fun y ↦ apm_t01J06_coneField F 1 (t, y)) x (apm_t01J06_e 0) -
        fderiv ℝ (fun y ↦ apm_t01J06_coneField F 0 (t, y)) x (apm_t01J06_e 1) =
        deriv (fun s : ℝ ↦ s ^ 2 * F 2 (s • x)) t
    have eA' : fderiv ℝ (fun y ↦ apm_t01J06_coneField F 1 (t, y)) x (apm_t01J06_e 0) =
        t * ((t * fderiv ℝ (F 2) (t • x) (apm_t01J06_e 0)) * x 0 +
          F 2 (t • x) * apm_t01J06_e 0 0 -
          ((t * fderiv ℝ (F 0) (t • x) (apm_t01J06_e 0)) * x 2 +
          F 0 (t • x) * apm_t01J06_e 0 2)) := eA
    have eB' : fderiv ℝ (fun y ↦ apm_t01J06_coneField F 0 (t, y)) x (apm_t01J06_e 1) =
        t * ((t * fderiv ℝ (F 1) (t • x) (apm_t01J06_e 1)) * x 2 +
          F 1 (t • x) * apm_t01J06_e 1 2 -
          ((t * fderiv ℝ (F 2) (t • x) (apm_t01J06_e 1)) * x 1 +
          F 2 (t • x) * apm_t01J06_e 1 1)) := eB
    rw [eA', eB', eR, eD, hc1, hc2, hc3, hc4]
    simp only [apm_t01J06_partial]
    linear_combination (-t ^ 2 * x 2) * hd0

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
  have hcone : ∀ k : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (apm_t01J06_coneField F k) := by
    intro k
    show ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × apm_t01J06_E3 ↦
      p.1 * (F (k + 1) (p.1 • p.2) * p.2 (k + 2) - F (k + 2) (p.1 • p.2) * p.2 (k + 1)))
    fun_prop
  have hsmooth : ∀ k : Fin 3,
      ContDiff ℝ 1 (fun x ↦ ∫ t in (0 : ℝ)..1, apm_t01J06_coneField F k (t, x)) ∧
      ∀ x v, fderiv ℝ (fun y ↦ ∫ t in (0 : ℝ)..1, apm_t01J06_coneField F k (t, y)) x v =
        ∫ t in (0 : ℝ)..1, fderiv ℝ (fun y ↦ apm_t01J06_coneField F k (t, y)) x v :=
    fun k ↦ apm_t01J06_parametric_integral (apm_t01J06_coneField F k) (hcone k)
  have key : ∀ (i : Fin 3) (x : apm_t01J06_E3),
      apm_t01J06_partial (i + 1)
          (fun y ↦ ∫ t in (0 : ℝ)..1, apm_t01J06_coneField F (i + 2) (t, y)) x -
        apm_t01J06_partial (i + 2)
          (fun y ↦ ∫ t in (0 : ℝ)..1, apm_t01J06_coneField F (i + 1) (t, y)) x = F i x := by
    intro i x
    have hdiff : ∀ s : ℝ, DifferentiableAt ℝ (F i) (s • x) :=
      fun s ↦ ((hF i).differentiable (by simp)) (s • x)
    have hD : ∀ t : ℝ, HasDerivAt (fun s : ℝ ↦ s ^ 2 * F i (s • x))
        (2 * t * F i (t • x) + t ^ 2 * fderiv ℝ (F i) (t • x) x) t := by
      intro t
      have hv : HasDerivAt (fun s : ℝ ↦ s • x) x t := by
        simpa using (hasDerivAt_id t).smul_const x
      have hvg : HasDerivAt (fun s : ℝ ↦ F i (s • x)) (fderiv ℝ (F i) (t • x) x) t := by
        have h := (hdiff t).hasFDerivAt.comp_hasDerivAt t hv
        simpa using h
      have hu : HasDerivAt (fun s : ℝ ↦ s ^ 2) (2 * t) t := by
        simpa using (hasDerivAt_pow 2 t)
      exact hu.mul hvg
    have hDcont : Continuous (fun t : ℝ ↦
        2 * t * F i (t • x) + t ^ 2 * fderiv ℝ (F i) (t • x) x) := by
      have htx : Continuous (fun t : ℝ ↦ t • x) := continuous_id.smul continuous_const
      have h1 : Continuous (fun t : ℝ ↦ F i (t • x)) := (hF i).continuous.comp htx
      have h2 : Continuous (fun t : ℝ ↦ fderiv ℝ (F i) (t • x) x) :=
        (((hF i).continuous_fderiv (by simp)).comp htx).clm_apply continuous_const
      exact ((continuous_const.mul continuous_id).mul h1).add ((continuous_pow 2).mul h2)
    have hFTC' : (∫ t in (0 : ℝ)..1, deriv (fun s : ℝ ↦ s ^ 2 * F i (s • x)) t) =
        F i x := by
      have hHas : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
          DifferentiableAt ℝ (fun s : ℝ ↦ s ^ 2 * F i (s • x)) t :=
        fun t _ ↦ (hD t).differentiableAt
      have hint : IntervalIntegrable
          (fun t : ℝ ↦ deriv (fun s : ℝ ↦ s ^ 2 * F i (s • x)) t) volume 0 1 := by
        have heq : (fun t : ℝ ↦ deriv (fun s : ℝ ↦ s ^ 2 * F i (s • x)) t) =
            fun t : ℝ ↦ 2 * t * F i (t • x) + t ^ 2 * fderiv ℝ (F i) (t • x) x :=
          funext fun t ↦ (hD t).deriv
        rw [heq]
        exact hDcont.intervalIntegrable 0 1
      have h := intervalIntegral.integral_deriv_eq_sub hHas hint
      rw [h]
      simp
    have hpartial : ∀ k j : Fin 3,
        apm_t01J06_partial j
            (fun y ↦ ∫ t in (0 : ℝ)..1, apm_t01J06_coneField F k (t, y)) x =
          ∫ t in (0 : ℝ)..1,
            apm_t01J06_partial j (fun y ↦ apm_t01J06_coneField F k (t, y)) x := by
      intro k j
      show fderiv ℝ (fun y ↦ ∫ t in (0 : ℝ)..1, apm_t01J06_coneField F k (t, y)) x
          (apm_t01J06_e j) = _
      rw [(hsmooth k).2 x (apm_t01J06_e j)]
      rfl
    have hcontP : ∀ k j : Fin 3, Continuous (fun t : ℝ ↦
        apm_t01J06_partial j (fun y ↦ apm_t01J06_coneField F k (t, y)) x) := by
      intro k j
      have hf : Continuous (fderiv ℝ (apm_t01J06_coneField F k)) :=
        (hcone k).continuous_fderiv (by simp)
      have hc : Continuous (fun t : ℝ ↦
          (fderiv ℝ (apm_t01J06_coneField F k) (t, x)).comp
            (ContinuousLinearMap.inr ℝ ℝ apm_t01J06_E3)) :=
        (hf.comp (continuous_id.prodMk continuous_const)).clm_comp continuous_const
      have heq : (fun t : ℝ ↦
          apm_t01J06_partial j (fun y ↦ apm_t01J06_coneField F k (t, y)) x) =
          fun t : ℝ ↦ ((fderiv ℝ (apm_t01J06_coneField F k) (t, x)).comp
            (ContinuousLinearMap.inr ℝ ℝ apm_t01J06_E3)) (apm_t01J06_e j) := by
        funext t
        have ht : HasFDerivAt (fun y : apm_t01J06_E3 ↦ (t, y))
            (ContinuousLinearMap.inr ℝ ℝ apm_t01J06_E3) x :=
          hasFDerivAt_prodMk_right t x
        have hd := (((hcone k).differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
          ht).fderiv
        have hcomp : (fun y ↦ apm_t01J06_coneField F k (t, y)) =
            apm_t01J06_coneField F k ∘ fun y ↦ (t, y) := rfl
        show fderiv ℝ (fun y ↦ apm_t01J06_coneField F k (t, y)) x (apm_t01J06_e j) = _
        rw [hcomp, hd]
      rw [heq]
      exact hc.clm_apply continuous_const
    rw [hpartial (i + 2) (i + 1), hpartial (i + 1) (i + 2),
      ← intervalIntegral.integral_sub
        ((hcontP (i + 2) (i + 1)).intervalIntegrable 0 1)
        ((hcontP (i + 1) (i + 2)).intervalIntegrable 0 1),
      intervalIntegral.integral_congr
        (fun t _ ↦ apm_t01J06_cone_identity F hF hdiv i t x), hFTC']
  refine ⟨fun k x ↦ ∫ t in (0 : ℝ)..1, apm_t01J06_coneField F k (t, x),
    fun k ↦ (hsmooth k).1, fun x ↦ ⟨?_, ?_, ?_⟩⟩
  · show F 0 x = apm_t01J06_partial 1
        (fun y ↦ ∫ t in (0 : ℝ)..1, apm_t01J06_coneField F 2 (t, y)) x -
      apm_t01J06_partial 2 (fun y ↦ ∫ t in (0 : ℝ)..1, apm_t01J06_coneField F 1 (t, y)) x
    exact (key 0 x).symm
  · show F 1 x = apm_t01J06_partial 2
        (fun y ↦ ∫ t in (0 : ℝ)..1, apm_t01J06_coneField F 0 (t, y)) x -
      apm_t01J06_partial 0 (fun y ↦ ∫ t in (0 : ℝ)..1, apm_t01J06_coneField F 2 (t, y)) x
    exact (key 1 x).symm
  · show F 2 x = apm_t01J06_partial 0
        (fun y ↦ ∫ t in (0 : ℝ)..1, apm_t01J06_coneField F 1 (t, y)) x -
      apm_t01J06_partial 1 (fun y ↦ ∫ t in (0 : ℝ)..1, apm_t01J06_coneField F 0 (t, y)) x
    exact (key 2 x).symm

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

/-- Seat: the derivative at every time. `R (t + s) x = R s (R t x)` by `_aux_rot_add`; compose
`_aux_hasDeriv` at `R t x` with the shift `s ↦ s - t` (`HasDerivAt.comp_sub_const` or similar). -/
theorem apm_t01J06_rotation_derivative_integral_aux_hasDeriv_all (k : Fin 3) (x : apm_t01J06_E3) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ apm_t01J06_rotation_derivative_integral_aux_rot k s x)
      (apm_t01J06_rotField k (apm_t01J06_rotation_derivative_integral_aux_rot k t x)) t := by
  have hshift : HasDerivAt (fun s : ℝ ↦ s - t) 1 t :=
    (hasDerivAt_id t).sub_const t
  have hbase : HasDerivAt
      (fun u : ℝ ↦ apm_t01J06_rotation_derivative_integral_aux_rot k u
        (apm_t01J06_rotation_derivative_integral_aux_rot k t x))
      (apm_t01J06_rotField k (apm_t01J06_rotation_derivative_integral_aux_rot k t x))
      ((fun s : ℝ ↦ s - t) t) := by
    simpa using apm_t01J06_rotation_derivative_integral_aux_hasDeriv k
      (apm_t01J06_rotation_derivative_integral_aux_rot k t x)
  have h := hbase.scomp (h := fun s : ℝ ↦ s - t) t hshift
  convert h using 1
  funext s
  simp only [Function.comp_apply]
  rw [apm_t01J06_rotation_derivative_integral_aux_rot_add]
  congr 2
  ring
  simp

/-- Seat: rotation invariance of the integral. Build the isometry equivalence of the sphere from `_aux_rot`,
`_aux_rot_neg`, `_aux_norm` and `_aux_isometry` (a `LinearIsometryEquiv` needs linearity, available coordinatewise), then
`IntrinsicSphereSecondMoments.integral_isometry` for `μH[2]`, with `Measure.euclideanHausdorffMeasure_def` and
`integral_smul_nnreal_measure` for `μHE[2]`; or use `Isometry.euclideanHausdorffMeasure_image` with the measure-preserving
map. -/
theorem apm_t01J06_rotation_derivative_integral_aux_const (k : Fin 3) (t : ℝ) (f : apm_t01J06_E3 → ℝ)
    (hf : Continuous f) :
    (∫ q : apm_t01J06_S2, f (apm_t01J06_rotation_derivative_integral_aux_rot k t q.1) ∂μHE[2]) =
      ∫ q : apm_t01J06_S2, f q.1 ∂μHE[2] := by
  let ee : apm_t01J06_S2 ≃ apm_t01J06_S2 := {
      toFun := fun q ↦ (⟨apm_t01J06_rotation_derivative_integral_aux_rot k t q.1, by
        simpa [Metric.mem_sphere, dist_eq_norm,
          apm_t01J06_rotation_derivative_integral_aux_norm] using q.property⟩ : apm_t01J06_S2)
      invFun := fun q ↦ (⟨apm_t01J06_rotation_derivative_integral_aux_rot k (-t) q.1, by
        simpa [Metric.mem_sphere, dist_eq_norm,
          apm_t01J06_rotation_derivative_integral_aux_norm] using q.property⟩ : apm_t01J06_S2)
      left_inv := fun q ↦ Subtype.ext
        (apm_t01J06_rotation_derivative_integral_aux_rot_neg k t q.1)
      right_inv := fun q ↦ Subtype.ext (by simpa only [neg_neg] using
        apm_t01J06_rotation_derivative_integral_aux_rot_neg k (-t) q.1) }
  let e : apm_t01J06_S2 ≃ᵢ apm_t01J06_S2 := ⟨ee, by
    intro q r
    simp only [edist_dist]
    congr 1
    exact (apm_t01J06_rotation_derivative_integral_aux_isometry k t).dist_eq q.1 r.1⟩
  let em := e.toHomeomorph.toMeasurableEquiv
  have h : MeasurePreserving em μHE[2] μHE[2] :=
    e.measurePreserving_euclideanHausdorffMeasure 2
  exact h.integral_comp' (fun q : apm_t01J06_S2 ↦ f q.1)

lemma apm_t01J06_rotation_derivative_integral_aux_key (k : Fin 3)
    (f : apm_t01J06_E3 → ℝ) (hf : ContDiff ℝ 1 f) :
    (∫ q : apm_t01J06_S2, fderiv ℝ f q.1 (apm_t01J06_rotField k q.1) ∂μHE[2]) = 0 := by
  let F : ℝ → apm_t01J06_S2 → ℝ := fun t q ↦
    f (apm_t01J06_rotation_derivative_integral_aux_rot k t q.1)
  let F' : ℝ → apm_t01J06_S2 → ℝ := fun t q ↦
    fderiv ℝ f (apm_t01J06_rotation_derivative_integral_aux_rot k t q.1)
      (apm_t01J06_rotField k
        (apm_t01J06_rotation_derivative_integral_aux_rot k t q.1))
  have hrot_cont : Continuous (fun p : ℝ × apm_t01J06_S2 ↦
      apm_t01J06_rotation_derivative_integral_aux_rot k p.1 p.2.1) := by
    apply (PiLp.continuous_toLp 2 _).comp
    rw [continuous_pi_iff]
    intro i
    fin_cases k <;> fin_cases i <;>
      simp [apm_t01J06_rotation_derivative_integral_aux_rot] <;> fun_prop
  have hfield_cont : Continuous (apm_t01J06_rotField k) := by
    apply (PiLp.continuous_toLp 2 _).comp
    rw [continuous_pi_iff]
    intro i
    fin_cases k <;> fin_cases i <;> simp [apm_t01J06_rotField] <;> fun_prop
  have hF'_cont : Continuous (fun p : ℝ × apm_t01J06_S2 ↦ F' p.1 p.2) := by
    dsimp [F']
    apply Continuous.clm_apply
    · exact (hf.continuous_fderiv (by simp)).comp hrot_cont
    · exact hfield_cont.comp hrot_cont
  obtain ⟨C, hC⟩ :=
    ((isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).prod
      (isCompact_univ : IsCompact (Set.univ : Set apm_t01J06_S2))).exists_bound_of_continuousOn
      hF'_cont.continuousOn
  have hmass := apm_t02a05_euclideanHausdorff_unitSphere_mass
  have hmass_ne : (μHE[2] (Set.univ : Set apm_t01J06_S2)) ≠ ∞ := by
    intro he
    rw [he] at hmass
    have hz : (0 : ℝ) = 4 * Real.pi := by simpa using hmass
    nlinarith [Real.pi_pos]
  letI : IsFiniteMeasure (μHE[2] : Measure apm_t01J06_S2) :=
    ⟨lt_top_iff_ne_top.mpr hmass_ne⟩
  have hderiv : HasDerivAt (fun t ↦ ∫ q, F t q ∂μHE[2])
      (∫ q, F' 0 q ∂μHE[2]) 0 := by
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (μHE[2] : Measure apm_t01J06_S2)) (x₀ := (0 : ℝ))
      (F := F) (F' := F') (bound := fun _ ↦ C) (s := Set.Icc (-1 : ℝ) 1)
      (by exact Icc_mem_nhds (by norm_num) (by norm_num))
      (by
        filter_upwards with t
        dsimp [F]
        exact (hf.continuous.comp
          (hrot_cont.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable)
      (by
        rw [← integrableOn_univ]
        apply ContinuousOn.integrableOn_compact isCompact_univ
        dsimp [F]
        exact (hf.continuous.comp
          (hrot_cont.comp (continuous_const.prodMk continuous_id))).continuousOn)
      (by exact (hF'_cont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (by
        filter_upwards with q
        intro t ht
        exact hC (t, q) ⟨ht, Set.mem_univ q⟩)
      (integrable_const C)
      (by
        filter_upwards with q
        intro t ht
        dsimp [F, F']
        exact (hf.differentiable (by simp)
          (apm_t01J06_rotation_derivative_integral_aux_rot k t q.1)).hasFDerivAt.comp_hasDerivAt
            t (apm_t01J06_rotation_derivative_integral_aux_hasDeriv_all k q.1 t))).2
  have hconst : (fun t ↦ ∫ q, F t q ∂μHE[2]) =
      fun _ ↦ ∫ q : apm_t01J06_S2, f q.1 ∂μHE[2] := by
    funext t
    exact apm_t01J06_rotation_derivative_integral_aux_const k t f hf.continuous
  rw [hconst] at hderiv
  have hz : (∫ q, F' 0 q ∂μHE[2]) = 0 :=
    hderiv.unique (hasDerivAt_const (x := 0) (∫ q : apm_t01J06_S2, f q.1 ∂μHE[2]))
  simpa [F', apm_t01J06_rotation_derivative_integral_aux_rot_zero] using hz

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
  have hrot0 (x : apm_t01J06_E3) :
      apm_t01J06_rotField 0 x = -x 2 • apm_t01J06_e 1 + x 1 • apm_t01J06_e 2 := by
    ext i
    fin_cases i <;> simp [apm_t01J06_rotField, apm_t01J06_e]
  have hrot1 (x : apm_t01J06_E3) :
      apm_t01J06_rotField 1 x = x 2 • apm_t01J06_e 0 - x 0 • apm_t01J06_e 2 := by
    ext i
    fin_cases i <;> simp [apm_t01J06_rotField, apm_t01J06_e]
  have hrot2 (x : apm_t01J06_E3) :
      apm_t01J06_rotField 2 x = -x 1 • apm_t01J06_e 0 + x 0 • apm_t01J06_e 1 := by
    ext i
    fin_cases i <;> simp [apm_t01J06_rotField, apm_t01J06_e]
  have hpoint (q : apm_t01J06_S2) :
      q.1 0 * (apm_t01J06_partial 1 (A 2) q.1 - apm_t01J06_partial 2 (A 1) q.1) +
        q.1 1 * (apm_t01J06_partial 2 (A 0) q.1 - apm_t01J06_partial 0 (A 2) q.1) +
        q.1 2 * (apm_t01J06_partial 0 (A 1) q.1 - apm_t01J06_partial 1 (A 0) q.1) =
      fderiv ℝ (A 0) q.1 (apm_t01J06_rotField 0 q.1) +
        fderiv ℝ (A 1) q.1 (apm_t01J06_rotField 1 q.1) +
        fderiv ℝ (A 2) q.1 (apm_t01J06_rotField 2 q.1) := by
    rw [hrot0, hrot1, hrot2]
    simp only [map_add, map_sub, map_smul, smul_eq_mul]
    unfold apm_t01J06_partial
    ring
  simp_rw [hpoint]
  have hmass_ne : (μHE[2] (Set.univ : Set apm_t01J06_S2)) ≠ ∞ := by
    intro he
    have hmass := apm_t02a05_euclideanHausdorff_unitSphere_mass
    rw [he] at hmass
    have hz : (0 : ℝ) = 4 * Real.pi := by simpa using hmass
    nlinarith [Real.pi_pos]
  letI : IsFiniteMeasure (μHE[2] : Measure apm_t01J06_S2) :=
    ⟨lt_top_iff_ne_top.mpr hmass_ne⟩
  have hrot_cont (k : Fin 3) : Continuous (apm_t01J06_rotField k) := by
    apply (PiLp.continuous_toLp 2 _).comp
    rw [continuous_pi_iff]
    intro i
    fin_cases k <;> fin_cases i <;> simp [apm_t01J06_rotField] <;> fun_prop
  have hint (k : Fin 3) : Integrable
      (fun q : apm_t01J06_S2 ↦
        fderiv ℝ (A k) q.1 (apm_t01J06_rotField k q.1)) μHE[2] := by
    rw [← integrableOn_univ]
    apply ContinuousOn.integrableOn_compact isCompact_univ
    exact Continuous.clm_apply
      ((hA k).continuous_fderiv (by simp) |>.comp continuous_subtype_val)
      ((hrot_cont k).comp continuous_subtype_val) |>.continuousOn
  rw [integral_add]
  · rw [integral_add]
    · rw [apm_t01J06_rotation_derivative_integral 0 (A 0) (hA 0),
        apm_t01J06_rotation_derivative_integral 1 (A 1) (hA 1),
        apm_t01J06_rotation_derivative_integral 2 (A 2) (hA 2)]
      norm_num
    · exact hint 0
    · exact hint 1
  · exact (hint 0).add (hint 1)
  · exact hint 2

/-- Seat: assembly of the Stokes obstruction. Take `F 0 = eta(e 1, e 2)`, `F 1 = -eta(e 0, e 2)`,
`F 2 = eta(e 0, e 1)`; they are smooth, `apm_t01J06_closed_divergence_free` gives `div F = 0`,
`apm_t01J06_divergenceFree_isCurl` gives `A`, `apm_t01J06_orientedCoefficient_flux` rewrites the integrand,
and `apm_t01J06_curl_flux_zero` finishes. -/
-- BEGIN SEAT AREA
theorem apm_t01J06_closed_extension_integral_zero
    (eta : apm_t01J06_AmbientForm2) (alpha : apm_t01J06_SphereForm2)
    (hs : ContDiff ℝ (⊤ : ℕ∞) eta) (hc : extDeriv eta = 0)
    (hp : apm_t01J06_isInclusionPullback eta alpha) :
    apm_t01J06_sphereIntegral alpha = 0 := by
  let F : Fin 3 → apm_t01J06_E3 → ℝ := fun i ↦
    match i with
    | 0 => fun x ↦ eta x ![apm_t01J06_e 1, apm_t01J06_e 2]
    | 1 => fun x ↦ -eta x ![apm_t01J06_e 0, apm_t01J06_e 2]
    | 2 => fun x ↦ eta x ![apm_t01J06_e 0, apm_t01J06_e 1]
  have hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i) := by
    let L : (apm_t01J06_E3 [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ apm_t01J06_E3) ℝ :=
      ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ
    let C := fun x ↦ (eta x).toContinuousMultilinearMap
    have heta : ContDiff ℝ (⊤ : ℕ∞) C := by
      simpa [C, L] using L.contDiff.comp hs
    intro i
    fin_cases i
    · change ContDiff ℝ (⊤ : ℕ∞) (fun x ↦
        C x ![apm_t01J06_e 1, apm_t01J06_e 2])
      simpa only [Function.comp_apply] using
        (ContinuousMultilinearMap.apply ℝ _ ℝ
          ![apm_t01J06_e 1, apm_t01J06_e 2]).contDiff.comp heta
    · change ContDiff ℝ (⊤ : ℕ∞) (fun x ↦
        -C x ![apm_t01J06_e 0, apm_t01J06_e 2])
      exact ((by simpa only [Function.comp_apply] using
        (ContinuousMultilinearMap.apply ℝ _ ℝ
          ![apm_t01J06_e 0, apm_t01J06_e 2]).contDiff.comp heta) :
            ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ C x
              ![apm_t01J06_e 0, apm_t01J06_e 2])).neg
    · change ContDiff ℝ (⊤ : ℕ∞) (fun x ↦
        C x ![apm_t01J06_e 0, apm_t01J06_e 1])
      simpa only [Function.comp_apply] using
        (ContinuousMultilinearMap.apply ℝ _ ℝ
          ![apm_t01J06_e 0, apm_t01J06_e 1]).contDiff.comp heta
  have hdiv : ∀ x, apm_t01J06_partial 0 (F 0) x +
      apm_t01J06_partial 1 (F 1) x + apm_t01J06_partial 2 (F 2) x = 0 := by
    intro x
    have h := apm_t01J06_closed_divergence_free eta hs hc x
    simpa [F, apm_t01J06_partial, fderiv_neg] using h
  obtain ⟨A, hA, hcurl⟩ := apm_t01J06_divergenceFree_isCurl F hF hdiv
  unfold apm_t01J06_sphereIntegral
  simp_rw [apm_t01J06_orientedCoefficient_flux eta alpha hp]
  have hpoint (q : apm_t01J06_S2) :
      q.1 0 * eta q ![apm_t01J06_e 1, apm_t01J06_e 2] -
          q.1 1 * eta q ![apm_t01J06_e 0, apm_t01J06_e 2] +
          q.1 2 * eta q ![apm_t01J06_e 0, apm_t01J06_e 1] =
        q.1 0 * (apm_t01J06_partial 1 (A 2) q.1 -
          apm_t01J06_partial 2 (A 1) q.1) +
        q.1 1 * (apm_t01J06_partial 2 (A 0) q.1 -
          apm_t01J06_partial 0 (A 2) q.1) +
        q.1 2 * (apm_t01J06_partial 0 (A 1) q.1 -
          apm_t01J06_partial 1 (A 0) q.1) := by
    have h := hcurl q.1
    simp only [F] at h
    rcases h with ⟨h0, h1, h2⟩
    rw [← h0, ← h1, ← h2]
    ring
  simp_rw [hpoint]
  exact apm_t01J06_curl_flux_zero A hA
-- END SEAT AREA

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
  intro q v
  unfold apm_t01J06_productRestriction
  unfold apm_t01J06_exists_closed_product_extension_aux_Z
  unfold apm_t01J06_exists_closed_product_extension_aux_eta
  unfold apm_t01J06_exists_closed_product_extension_aux_scalar
  unfold apm_t01J06_exists_closed_product_extension_aux_solidAngle
  rw [halpha, homega]
  have hqnorm : ‖(q : apm_t01J06_E3)‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using q.property
  simp [hqnorm]
  have hq : q.1 0 ^ 2 + q.1 1 ^ 2 + q.1 2 ^ 2 = 1 := by
    have h : ‖(q : apm_t01J06_E3)‖ ^ 2 = 1 := by rw [hqnorm]; norm_num
    simpa only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, add_assoc,
      Real.norm_eq_abs, sq_abs] using h
  have hv (k : Fin 2) :
      q.1 0 * (v k : apm_t01J06_E3) 0 +
      q.1 1 * (v k : apm_t01J06_E3) 1 +
      q.1 2 * (v k : apm_t01J06_E3) 2 = 0 := by
    have ho := (v k).property
    unfold apm_t01J06_sphereTangent at ho
    rw [Submodule.mem_orthogonal'] at ho
    have hi := ho (q : apm_t01J06_E3) (Submodule.mem_span_singleton_self _)
    rw [real_inner_comm] at hi
    rw [PiLp.inner_apply] at hi
    simpa [Fin.sum_univ_three, real_inner_eq_re_inner, mul_comm] using hi
  change ((q.1 2 + 3) * q.1 2) *
      Matrix.det (Matrix.vecCons (q : apm_t01J06_E3)
        (fun k j => (v k : apm_t01J06_E3) j)) =
    (q.1 2 + 3) *
      ((v 0 : apm_t01J06_E3) 0 * (v 1 : apm_t01J06_E3) 1 -
       (v 0 : apm_t01J06_E3) 1 * (v 1 : apm_t01J06_E3) 0)
  rw [Matrix.det_fin_three]
  simp
  linear_combination (q.1 2 + 3) *
    (q.1 0 * ((v 0 : apm_t01J06_E3) 1 * hv 1 -
      (v 1 : apm_t01J06_E3) 1 * hv 0) -
     q.1 1 * ((v 0 : apm_t01J06_E3) 0 * hv 1 -
      (v 1 : apm_t01J06_E3) 0 * hv 0) +
     ((v 0 : apm_t01J06_E3) 0 * (v 1 : apm_t01J06_E3) 1 -
      (v 0 : apm_t01J06_E3) 1 * (v 1 : apm_t01J06_E3) 0) * hq)

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
