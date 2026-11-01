import Mathlib
import ConstructionTargets.C1GraphGlobalBounds
import ConstructionTargets.SphereCapNullEquatorMeasureAssembly

/-! # Euclidean Hausdorff mass of the unit two-sphere

`μHE[2]` of the unit sphere of `ℝ³` is `4π`. Moved here unchanged from `problems/t02A05` so that other
problems can use it. Mathlib's raw `μH[2]` is not area on Euclidean space: it is a constant multiple. -/

open MeasureTheory
open scoped ENNReal

noncomputable section

abbrev apm_t02a05_E3 := EuclideanSpace ℝ (Fin 3)

/-! ### Split of `apm_t02a05_euclideanHausdorff_unitSphere_mass` (claude-14, 2026-10-13, after a partial). Mathlib's raw `μH[2]`
(`SphereCapNullEquatorMeasureAssembly.sphere_two_measure`, `domainMeasure`) differs from `μHE[2]` by
the dimension-2 scalar, which turns `μH[2]` on `ℝ²` into Lebesgue measure. The three pieces are
independent. -/

/-- (A) Hausdorff measure of the sphere as a subtype equals that of the subset (isometric embedding). -/
theorem apm_t02a05_sphere_subtype_mass :
    (μHE[2] (Set.univ : Set (Metric.sphere (0 : apm_t02a05_E3) 1))) =
      (μHE[2] (Metric.sphere (0 : apm_t02a05_E3) 1)) := by
  have h := (isometry_subtype_coe : Isometry
    (Subtype.val : Metric.sphere (0 : apm_t02a05_E3) 1 → apm_t02a05_E3))
    |>.euclideanHausdorffMeasure_image (d := 2) Set.univ
  have himage :
      (Subtype.val '' (Set.univ : Set (Metric.sphere (0 : apm_t02a05_E3) 1))) =
        Metric.sphere (0 : apm_t02a05_E3) 1 := by
    ext x
    simp
  calc
    _ = μHE[2] (Subtype.val ''
        (Set.univ : Set (Metric.sphere (0 : apm_t02a05_E3) 1))) := h.symm
    _ = _ := congrArg (fun s : Set apm_t02a05_E3 ↦ μHE[2] s) himage

lemma apm_t02a05_sphere_mass_eq_two_caps_aux_raw :
    (μH[(2 : ℕ)] : Measure apm_t02a05_E3) (Metric.sphere 0 1) =
      (∫⁻ x in ConstructionTargets.SphereCapHeight.domain 2,
        ENNReal.ofReal (1 / ConstructionTargets.SphereCapHeight.upper 2 x)
          ∂ConstructionTargets.C1GraphMeasureDecomposition.domainMeasure 2) +
      (∫⁻ x in ConstructionTargets.SphereCapHeight.domain 2,
        ENNReal.ofReal (1 / ConstructionTargets.SphereCapHeight.upper 2 x)
          ∂ConstructionTargets.C1GraphMeasureDecomposition.domainMeasure 2) := by
  convert ConstructionTargets.SphereCapNullEquatorMeasureAssembly.sphere_two_measure
    using 1 <;> norm_num

/-- (B) Two caps over the unit disk, with `μHE[2]` on the sphere and Lebesgue measure on the disk:
`sphere_two_measure` scaled by the `μHE[2]` constant, which maps `μH[2]` on `ℝ²` to `volume`. -/
lemma apm_t02a05_sphere_mass_eq_two_caps_aux_measurable :
    ConstructionTargets.LinearGraphMeasure.domainMeasurable 2 =
      WithLp.measurableSpace 2 (Fin 2 → ℝ) := by
  change borel _ = _
  symm
  exact @BorelSpace.measurable_eq _ _
    (WithLp.measurableSpace 2 (Fin 2 → ℝ)) (by infer_instance)

local instance apm_t02a05_sphere_mass_eq_two_caps_aux_haar :
    (μH[(2 : ℕ)] : Measure (EuclideanSpace ℝ (Fin 2))).IsAddHaarMeasure := by
  simpa using (MeasureTheory.isAddHaarMeasure_hausdorffMeasure
    (E := EuclideanSpace ℝ (Fin 2)))

lemma apm_t02a05_sphere_mass_eq_two_caps_aux_scaled_domain :
    Measure.addHaarScalarFactor
          (volume : Measure (EuclideanSpace ℝ (Fin 2))) μH[(2 : ℕ)] •
      ConstructionTargets.C1GraphMeasureDecomposition.domainMeasure 2 =
      volume := by
  unfold ConstructionTargets.C1GraphMeasureDecomposition.domainMeasure
  exact (MeasureTheory.Measure.isAddLeftInvariant_eq_smul _ _).symm

lemma apm_t02a05_sphere_mass_eq_two_caps_aux_cap :
    Measure.addHaarScalarFactor
          (volume : Measure (EuclideanSpace ℝ (Fin 2))) μH[(2 : ℕ)] •
        (∫⁻ x in ConstructionTargets.SphereCapHeight.domain 2,
          ENNReal.ofReal (1 / ConstructionTargets.SphereCapHeight.upper 2 x)
            ∂ConstructionTargets.C1GraphMeasureDecomposition.domainMeasure 2) =
      (∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
        ENNReal.ofReal (1 / Real.sqrt (1 - ‖x‖ ^ 2))) := by
  rw [← lintegral_smul_measure, ← Measure.restrict_smul,
    apm_t02a05_sphere_mass_eq_two_caps_aux_scaled_domain]
  rfl

section mathlibInstance

/-- Mathlib's normalising constant for `μH[2]` on `ℝ²`. -/
noncomputable def apm_t02a05_cM : NNReal :=
  Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin 2))) μH[(2 : ℕ)]

/-- Mathlib's `μH[2]` value of the unit square (Mathlib instance). -/
noncomputable def apm_t02a05_hP : ENNReal :=
  (μH[(2 : ℕ)] : Measure (EuclideanSpace ℝ (Fin 2)))
    (parallelepiped (EuclideanSpace.basisFun (Fin 2) ℝ))

lemma apm_t02a05_cM_mul_parallelepiped :
    (apm_t02a05_cM : ENNReal) * apm_t02a05_hP = 1 := by
  have h := EuclideanSpace.euclideanHausdorffMeasure_eq_volume 2
  rw [MeasureTheory.Measure.euclideanHausdorffMeasure_def] at h
  have := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin 2)) ↦
    μ (parallelepiped (EuclideanSpace.basisFun (Fin 2) ℝ))) h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
  erw [(EuclideanSpace.basisFun (Fin 2) ℝ).volume_parallelepiped] at this
  simpa [apm_t02a05_cM, apm_t02a05_hP] using this

end mathlibInstance

lemma apm_t02a05_muH_parallelepiped_d :
    (μH[(2 : ℕ)] : Measure (EuclideanSpace ℝ (Fin 2)))
        (parallelepiped (EuclideanSpace.basisFun (Fin 2) ℝ)) = apm_t02a05_hP := by
  unfold apm_t02a05_hP
  simp only [MeasureTheory.Measure.hausdorffMeasure_apply]

lemma apm_t02a05_cD_mul_parallelepiped :
    (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin 2))) μH[(2 : ℕ)] : ENNReal) *
      (μH[(2 : ℕ)] : Measure (EuclideanSpace ℝ (Fin 2)))
        (parallelepiped (EuclideanSpace.basisFun (Fin 2) ℝ)) = 1 := by
  have h := apm_t02a05_sphere_mass_eq_two_caps_aux_scaled_domain
  have := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin 2)) ↦
    μ (parallelepiped (EuclideanSpace.basisFun (Fin 2) ℝ))) h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
  erw [(EuclideanSpace.basisFun (Fin 2) ℝ).volume_parallelepiped] at this
  simpa [ConstructionTargets.C1GraphMeasureDecomposition.domainMeasure] using this

lemma apm_t02a05_cM_eq_cD :
    apm_t02a05_cM =
      Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin 2))) μH[(2 : ℕ)] := by
  have hm := ENNReal.eq_inv_of_mul_eq_one_left apm_t02a05_cM_mul_parallelepiped
  have hd := apm_t02a05_cD_mul_parallelepiped
  rw [apm_t02a05_muH_parallelepiped_d] at hd
  have hd' := ENNReal.eq_inv_of_mul_eq_one_left hd
  exact_mod_cast hm.trans hd'.symm

theorem apm_t02a05_sphere_mass_eq_two_caps :
    (μHE[2] (Metric.sphere (0 : apm_t02a05_E3) 1)) = 2 * (∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1, ENNReal.ofReal (1 / Real.sqrt (1 - ‖x‖ ^ 2))) := by
  rw [MeasureTheory.Measure.euclideanHausdorffMeasure_def, Measure.smul_apply,
    apm_t02a05_sphere_mass_eq_two_caps_aux_raw]
  change apm_t02a05_cM • _ = _
  rw [apm_t02a05_cM_eq_cD, ← two_mul, ← apm_t02a05_sphere_mass_eq_two_caps_aux_cap,
    ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
  ring

/-- (C) The cap integral against Lebesgue measure: `∫₀^{2π} ∫₀¹ r / √(1 − r²) dr dθ = 2π`. -/
lemma apm_t02a05_cap_integral_aux_measurable :
    Measurable (fun x : EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal (1 / Real.sqrt (1 - ‖x‖ ^ 2))) := by
  fun_prop

lemma apm_t02a05_cap_integral_aux_nonneg
    (x : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ ENNReal.ofReal (1 / Real.sqrt (1 - ‖x‖ ^ 2)) := by
  exact bot_le

/-- Polar coordinates: the radial integrand over the unit disc. -/
lemma apm_t02a05_cap_integral_aux_polar_aux_factor :
    (∫⁻ p in Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal (p.1 / Real.sqrt (1 - p.1 ^ 2))) =
      ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ r in Set.Ioo (0 : ℝ) 1,
          ENNReal.ofReal (r / Real.sqrt (1 - r ^ 2)) := by
  have hm : Measurable (fun r : ℝ => ENNReal.ofReal (r / Real.sqrt (1 - r ^ 2))) := by
    fun_prop
  rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
    MeasureTheory.lintegral_prod (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 / Real.sqrt (1 - p.1 ^ 2))) (hm.comp measurable_fst).aemeasurable]
  simp only [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Real.volume_Ioo]
  rw [MeasureTheory.lintegral_mul_const _ hm, mul_comm]
  congr 2
  ring

section
lemma apm_t02a05_cap_integral_aux_polar_aux_inst :
    ConstructionTargets.LinearGraphMeasure.domainMeasurable 2 =
      (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin 2))) := by
  unfold ConstructionTargets.LinearGraphMeasure.domainMeasurable
  exact BorelSpace.measurable_eq.symm

lemma apm_t02a05_cap_integral_aux_polar_aux_coords (f : ℝ × ℝ → ENNReal) (hf : Measurable f) :
    (∫⁻ x : EuclideanSpace ℝ (Fin 2), f (x 0, x 1)) = ∫⁻ q : ℝ × ℝ, f q := by
  have hmp : MeasureTheory.MeasurePreserving
      (fun x : EuclideanSpace ℝ (Fin 2) => (x 0, x 1)) :=
    (MeasureTheory.volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
  exact hmp.lintegral_comp hf
end

lemma apm_t02a05_cap_integral_aux_polar_aux_transport :
    (∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
        ENNReal.ofReal (1 / Real.sqrt (1 - ‖x‖ ^ 2))) =
      ∫⁻ p in Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal (p.1 / Real.sqrt (1 - p.1 ^ 2)) := by
  set g : ℝ → ENNReal := fun t => ENNReal.ofReal (1 / Real.sqrt (1 - t)) with hg
  set f : ℝ × ℝ → ENNReal :=
    Set.indicator {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 < 1} (fun q => g (q.1 ^ 2 + q.2 ^ 2)) with hf
  have hfm : Measurable f := by
    refine Measurable.indicator (by fun_prop) ?_
    exact measurableSet_lt (by fun_prop) measurable_const
  have hnorm : ∀ x : EuclideanSpace ℝ (Fin 2), ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs,
      sq_abs, sq_abs]
  have hstep1 : (∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
        ENNReal.ofReal (1 / Real.sqrt (1 - ‖x‖ ^ 2))) =
      ∫⁻ x : EuclideanSpace ℝ (Fin 2), f (x 0, x 1) := by
    rw [← MeasureTheory.lintegral_indicator Metric.isOpen_ball.measurableSet]
    congr 1
    funext x
    have hb : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔ x 0 ^ 2 + x 1 ^ 2 < 1 := by
      rw [Metric.mem_ball, dist_zero_right, ← hnorm]
      constructor
      · intro h; nlinarith [norm_nonneg x]
      · intro h; nlinarith [norm_nonneg x]
    by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1
    · rw [Set.indicator_of_mem hx, hf, Set.indicator_of_mem (show (x 0, x 1) ∈ _ from hb.1 hx), hg,
        hnorm]
    · rw [Set.indicator_of_notMem hx, hf, Set.indicator_of_notMem
        (show (x 0, x 1) ∉ {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 < 1} from fun h => hx (hb.2 h))]
  have hstep2 : (∫⁻ x : EuclideanSpace ℝ (Fin 2), f (x 0, x 1)) = ∫⁻ q : ℝ × ℝ, f q := by
    convert apm_t02a05_cap_integral_aux_polar_aux_coords f hfm using 3
    all_goals first
      | exact apm_t02a05_cap_integral_aux_polar_aux_inst
      | exact apm_t02a05_cap_integral_aux_polar_aux_inst.symm
      | (congr 1 <;> first
          | exact apm_t02a05_cap_integral_aux_polar_aux_inst
          | exact apm_t02a05_cap_integral_aux_polar_aux_inst.symm
          | exact proof_irrel_heq _ _)
  rw [hstep1, hstep2, ← lintegral_comp_polarCoord_symm, polarCoord_target]
  have hset : (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi) =
      (Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ) ∩ (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
    ext p
    simp only [Set.mem_prod, Set.mem_Ioo, Set.mem_inter_iff, Set.mem_univ, Set.mem_Ioi]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨h1, h2⟩, trivial⟩, h1, h3⟩
    · rintro ⟨⟨⟨h1, h2⟩, _⟩, _, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
  rw [hset, ← MeasureTheory.Measure.restrict_restrict (measurableSet_Ioo.prod MeasurableSet.univ),
    ← MeasureTheory.lintegral_indicator (measurableSet_Ioo.prod MeasurableSet.univ)]
  refine MeasureTheory.setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) ?_
  rintro ⟨r, θ⟩ ⟨hr, _⟩
  simp only [Set.mem_Ioi] at hr
  have hsq : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    nlinarith [Real.cos_sq_add_sin_sq θ]
  simp only [polarCoord_symm_apply, smul_eq_mul]
  by_cases h1 : r < 1
  · have hm : (r, θ) ∈ Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ) := ⟨⟨hr, h1⟩, trivial⟩
    have hq : (r * Real.cos θ, r * Real.sin θ) ∈ {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 < 1} := by
      show (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 < 1
      rw [hsq]; nlinarith
    rw [Set.indicator_of_mem hm, hf, Set.indicator_of_mem hq, hg]
    simp only
    rw [hsq, ← ENNReal.ofReal_mul hr.le, mul_one_div]
  · have hm : (r, θ) ∉ Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set ℝ) := fun h => h1 h.1.2
    have hq : (r * Real.cos θ, r * Real.sin θ) ∉ {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 < 1} := by
      show ¬ (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 < 1
      rw [hsq]; nlinarith
    rw [Set.indicator_of_notMem hm, hf, Set.indicator_of_notMem hq, mul_zero]

lemma apm_t02a05_cap_integral_aux_polar :
    (∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1, ENNReal.ofReal (1 / Real.sqrt (1 - ‖x‖ ^ 2))) =
      ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ r in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (r / Real.sqrt (1 - r ^ 2)) := by
  rw [apm_t02a05_cap_integral_aux_polar_aux_transport,
    apm_t02a05_cap_integral_aux_polar_aux_factor]

/-- The radial integral: `∫₀¹ r / √(1 - r²) dr = 1` (antiderivative `-√(1 - r²)`). -/
lemma apm_t02a05_cap_integral_aux_radial_hasDeriv
    (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t : ℝ => -Real.sqrt (1 - t ^ 2))
      (r / Real.sqrt (1 - r ^ 2)) r := by
  have hpos : 0 < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
  have hs : Real.sqrt (1 - r ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  convert ((Real.hasDerivAt_sqrt hpos.ne').comp r
    ((hasDerivAt_const r (1 : ℝ)).sub ((hasDerivAt_id r).pow 2))).neg using 1
  field_simp
  simp [id] <;> ring

lemma apm_t02a05_cap_integral_aux_radial :
    (∫⁻ r in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (r / Real.sqrt (1 - r ^ 2))) = 1 := by
  set g' : ℝ → ℝ := fun r => r / Real.sqrt (1 - r ^ 2) with hg'
  have hcont : ContinuousOn (fun t : ℝ => -Real.sqrt (1 - t ^ 2)) (Set.Icc 0 1) :=
    (by fun_prop : Continuous (fun t : ℝ => -Real.sqrt (1 - t ^ 2))).continuousOn
  have hnn : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ g' x := fun x hx =>
    div_nonneg hx.1.le (Real.sqrt_nonneg _)
  have hint : MeasureTheory.IntegrableOn g' (Set.Ioc 0 1) :=
    intervalIntegral.integrableOn_deriv_of_nonneg hcont
      apm_t02a05_cap_integral_aux_radial_hasDeriv hnn
  have hftc : ∫ y in (0 : ℝ)..1, g' y = 1 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont
      apm_t02a05_cap_integral_aux_radial_hasDeriv
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 hint)]
    norm_num
  rw [intervalIntegral.integral_of_le zero_le_one] at hftc
  rw [MeasureTheory.setLIntegral_congr MeasureTheory.Ioo_ae_eq_Ioc,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint, hftc, ENNReal.ofReal_one]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
  exact div_nonneg hx.1.le (Real.sqrt_nonneg _)

theorem apm_t02a05_cap_integral :
    (∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1, ENNReal.ofReal (1 / Real.sqrt (1 - ‖x‖ ^ 2))) = ENNReal.ofReal (2 * Real.pi) := by
  rw [apm_t02a05_cap_integral_aux_polar, apm_t02a05_cap_integral_aux_radial, mul_one]

/-- The normalized two-dimensional Hausdorff mass of the Euclidean unit
sphere in three-space. -/
theorem apm_t02a05_euclideanHausdorff_unitSphere_mass :
    (μHE[2] (Set.univ : Set (Metric.sphere (0 : apm_t02a05_E3) 1))).toReal =
      4 * Real.pi := by
  rw [apm_t02a05_sphere_subtype_mass, apm_t02a05_sphere_mass_eq_two_caps,
    apm_t02a05_cap_integral, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  norm_num
  ring

#print axioms apm_t02a05_euclideanHausdorff_unitSphere_mass
