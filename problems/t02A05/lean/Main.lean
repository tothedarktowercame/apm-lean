import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import ConstructionTargets.IntrinsicSphereFourthMoments
import ConstructionTargets.C1GraphGlobalBounds
import ConstructionTargets.SphereCapNullEquatorMeasureAssembly

open MeasureTheory
open scoped ENNReal

noncomputable section

abbrev apm_t02a05_E3 := EuclideanSpace ℝ (Fin 3)
abbrev apm_t02a05_Form2 :=
  apm_t02a05_E3 → apm_t02a05_E3 [⋀^Fin 2]→L[ℝ] ℝ

def apm_t02a05_isOmega (omega : apm_t02a05_Form2) : Prop :=
  ∀ (x : apm_t02a05_E3) (v : Fin 2 → apm_t02a05_E3),
    omega x v =
      (x 0 - 1) ^ 3 * (v 0 1 * v 1 2 - v 0 2 * v 1 1) +
      (x 1 - 2) ^ 3 * (v 0 2 * v 1 0 - v 0 0 * v 1 2) +
      (x 2 - 3) * (v 0 0 * v 1 1 - v 0 1 * v 1 0)

def apm_t02a05_unitSphere (c : apm_t02a05_E3) : Set apm_t02a05_E3 :=
  Metric.sphere c 1

def apm_t02a05_sphereTangent (c : apm_t02a05_E3)
    (q : Metric.sphere c 1) : Submodule ℝ apm_t02a05_E3 :=
  (Submodule.span ℝ ({(q : apm_t02a05_E3) - c} : Set apm_t02a05_E3)).orthogonal

def apm_t02a05_tangentProjection (c : apm_t02a05_E3)
    (q : Metric.sphere c 1) (i : Fin 3) : apm_t02a05_sphereTangent c q :=
  (apm_t02a05_sphereTangent c q).orthogonalProjection
    (EuclideanSpace.single i 1)

def apm_t02a05_orientedCoefficient (omega : apm_t02a05_Form2)
    (c : apm_t02a05_E3) (q : Metric.sphere c 1) : ℝ :=
  ((q : apm_t02a05_E3) - c) 0 * omega q
      ![apm_t02a05_tangentProjection c q 1, apm_t02a05_tangentProjection c q 2] -
  ((q : apm_t02a05_E3) - c) 1 * omega q
      ![apm_t02a05_tangentProjection c q 0, apm_t02a05_tangentProjection c q 2] +
  ((q : apm_t02a05_E3) - c) 2 * omega q
      ![apm_t02a05_tangentProjection c q 0, apm_t02a05_tangentProjection c q 1]

def apm_t02a05_outwardSphereIntegral
    (omega : apm_t02a05_Form2) (c : apm_t02a05_E3) : ℝ :=
  ∫ q : Metric.sphere c 1, apm_t02a05_orientedCoefficient omega c q ∂μHE[2]

/-- The ordinary radial flux density, separated from tangent projections. -/
def apm_t02a05_radialFlux (c x : apm_t02a05_E3) : ℝ :=
  (x - c) 0 * (x 0 - 1) ^ 3 +
  (x - c) 1 * (x 1 - 2) ^ 3 +
  (x - c) 2 * (x 2 - 3)

/-- Pointwise, the projected alternating coefficient is the radial flux. -/
theorem apm_t02a05_orientedCoefficient_eq_radialFlux
    (omega : apm_t02a05_Form2) (homega : apm_t02a05_isOmega omega)
    (c : apm_t02a05_E3) (q : Metric.sphere c 1) :
    apm_t02a05_orientedCoefficient omega c q =
      apm_t02a05_radialFlux c q := by
  let n : apm_t02a05_E3 := (q : apm_t02a05_E3) - c
  have hn : ‖n‖ = 1 := by
    have hq := q.property
    simpa [Metric.mem_sphere, dist_eq_norm, n] using hq
  have hproj (i j : Fin 3) :
      (apm_t02a05_tangentProjection c q i : apm_t02a05_E3) j =
        (EuclideanSpace.single i 1 : apm_t02a05_E3) j - n i * n j := by
    change (((Submodule.span ℝ ({n} : Set apm_t02a05_E3)).orthogonal
      ).orthogonalProjection (EuclideanSpace.single i 1) : apm_t02a05_E3) j = _
    change (((ℝ ∙ n)ᗮ.starProjection
      (EuclideanSpace.single i 1 : apm_t02a05_E3)) j) = _
    rw [Submodule.starProjection_orthogonal_val,
      Submodule.starProjection_singleton ℝ]
    rw [hn]
    simp only [one_pow, Nat.cast_one, div_one, PiLp.sub_apply,
      PiLp.smul_apply, smul_eq_mul]
    have hi : inner ℝ n (EuclideanSpace.single i 1) = n i := by
      simpa using EuclideanSpace.inner_single_right i (1 : ℝ) n
    rw [hi]
    norm_num
  unfold apm_t02a05_orientedCoefficient apm_t02a05_radialFlux
  rw [homega, homega, homega]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  simp_rw [hproj]
  simp
  change n 0 * _ - n 1 * _ + n 2 * _ = _
  have hnormsq : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    have := congrArg (fun z : ℝ => z ^ 2) hn
    simpa [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ, add_assoc] using this
  dsimp [n]
  ring_nf at hnormsq ⊢

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

/-- Translation to the centered sphere, conversion from `μHE[2]` to the raw
intrinsic measure used by `unitFlux_moment`, and the resulting flux moment.
The normalization conclusion is an explicit hypothesis so this lemma can be
proved independently of the mass lemma. -/
def apm_t02a05_radialFlux_integral_aux_translateSphere
    (c : apm_t02a05_E3) :
    Metric.sphere (0 : apm_t02a05_E3) 1 ≃ᵢ Metric.sphere c 1 where
  toFun z := ⟨c + z.1, by
    rw [Metric.mem_sphere, dist_eq_norm]
    simpa [add_sub_cancel_left] using z.2⟩
  invFun q := ⟨q.1 - c, by
    change dist (q.1 - c) 0 = 1
    rw [dist_eq_norm, sub_zero]
    have hq : dist q.1 c = 1 := q.2
    simpa [dist_eq_norm] using hq⟩
  left_inv z := by ext; simp
  right_inv q := by ext; simp
  isometry_toFun := by
    intro a b
    rw [edist_dist, edist_dist]
    apply congrArg ENNReal.ofReal
    change dist (c + a.1) (c + b.1) = dist a.1 b.1
    exact dist_add_left c a.1 b.1

lemma apm_t02a05_radialFlux_integral_aux_transport
    (c : apm_t02a05_E3) :
    (∫ q : Metric.sphere c 1, apm_t02a05_radialFlux c q ∂μHE[2]) =
      ∫ z : Metric.sphere (0 : apm_t02a05_E3) 1,
        (z.1 0 * (z.1 0 + c 0 - 1) ^ 3 +
         z.1 1 * (z.1 1 + c 1 - 2) ^ 3 +
         z.1 2 * (z.1 2 + c 2 - 3)) ∂μHE[2] := by
  let e := apm_t02a05_radialFlux_integral_aux_translateSphere c
  have hmp := e.measurePreserving_euclideanHausdorffMeasure 2
  rw [← hmp.integral_comp e.toHomeomorph.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with z
  change apm_t02a05_radialFlux c (c + z.1) = _
  simp [apm_t02a05_radialFlux]
  ring

section
lemma apm_t02a05_radialFlux_integral_aux_inst :
    ConstructionTargets.LinearGraphMeasure.domainMeasurable 3 =
      (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin 3))) := by
  unfold ConstructionTargets.LinearGraphMeasure.domainMeasurable
  exact BorelSpace.measurable_eq.symm
end

lemma apm_t02a05_radialFlux_integral_aux_centeredMoment
    (hmass :
      (μHE[2] (Set.univ : Set (Metric.sphere (0 : apm_t02a05_E3) 1))).toReal =
        4 * Real.pi)
    (c : apm_t02a05_E3) :
    (∫ z : Metric.sphere (0 : apm_t02a05_E3) 1,
        (z.1 0 * (z.1 0 + c 0 - 1) ^ 3 +
         z.1 1 * (z.1 1 + c 1 - 2) ^ 3 +
         z.1 2 * (z.1 2 + c 2 - 3)) ∂μHE[2]) =
      44 * Real.pi / 15 +
        4 * Real.pi * ((c 0 - 1) ^ 2 + (c 1 - 2) ^ 2) := by
  have hmom := ConstructionTargets.IntrinsicSphereFourthMoments.unitFlux_moment c
  rw [MeasureTheory.Measure.euclideanHausdorffMeasure_def, integral_smul_nnreal_measure]
  rw [MeasureTheory.Measure.euclideanHausdorffMeasure_def, Measure.smul_apply,
    ENNReal.toReal_smul] at hmass
  simp only [Nat.cast_ofNat] at hmass ⊢
  have hI : (∫ z : Metric.sphere (0 : apm_t02a05_E3) 1,
        (z.1 0 * (z.1 0 + c 0 - 1) ^ 3 +
         z.1 1 * (z.1 1 + c 1 - 2) ^ 3 +
         z.1 2 * (z.1 2 + c 2 - 3)) ∂μH[2]) =
      (μH[2] (Set.univ : Set (Metric.sphere (0 : apm_t02a05_E3) 1))).toReal *
        (11 / 15 + (c 0 - 1) ^ 2 + (c 1 - 2) ^ 2) := by
    have hinst := apm_t02a05_radialFlux_integral_aux_inst
    convert hmom using 3
    all_goals first
      | exact hinst
      | (unfold ConstructionTargets.IntrinsicSphereSecondMoments.mass
         simp only [MeasureTheory.Measure.hausdorffMeasure_apply, Nat.cast_ofNat])
  rw [hI]
  rw [NNReal.smul_def, smul_eq_mul] at hmass ⊢
  erw [← mul_assoc, hmass]
  ring

theorem apm_t02a05_radialFlux_integral
    (hmass :
      (μHE[2] (Set.univ : Set (Metric.sphere (0 : apm_t02a05_E3) 1))).toReal =
        4 * Real.pi)
    (c : apm_t02a05_E3) :
    (∫ q : Metric.sphere c 1, apm_t02a05_radialFlux c q ∂μHE[2]) =
      44 * Real.pi / 15 +
        4 * Real.pi * ((c 0 - 1) ^ 2 + (c 1 - 2) ^ 2) := by
  rw [apm_t02a05_radialFlux_integral_aux_transport]
  exact apm_t02a05_radialFlux_integral_aux_centeredMoment hmass c

/-- The geometric bridge is assembly only. -/
theorem apm_t02A05_bridge_1
    (omega : apm_t02a05_Form2) (homega : apm_t02a05_isOmega omega)
    (c : apm_t02a05_E3) :
    apm_t02a05_outwardSphereIntegral omega c =
      44 * Real.pi / 15 +
        4 * Real.pi * ((c 0 - 1) ^ 2 + (c 1 - 2) ^ 2) := by
  rw [apm_t02a05_outwardSphereIntegral]
  calc
    (∫ q : Metric.sphere c 1,
        apm_t02a05_orientedCoefficient omega c q ∂μHE[2]) =
        ∫ q : Metric.sphere c 1, apm_t02a05_radialFlux c q ∂μHE[2] := by
          apply integral_congr_ae
          filter_upwards with q
          exact apm_t02a05_orientedCoefficient_eq_radialFlux omega homega c q
    _ = _ := apm_t02a05_radialFlux_integral
      apm_t02a05_euclideanHausdorff_unitSphere_mass c

lemma apm_t02a05_quadratic_minimum (a b : ℝ) :
    44 * Real.pi / 15 ≤
        44 * Real.pi / 15 +
          4 * Real.pi * ((a - 1) ^ 2 + (b - 2) ^ 2) ∧
    (44 * Real.pi / 15 +
          4 * Real.pi * ((a - 1) ^ 2 + (b - 2) ^ 2) =
        44 * Real.pi / 15 ↔ a = 1 ∧ b = 2) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have ha : 0 ≤ (a - 1) ^ 2 := sq_nonneg _
  have hb : 0 ≤ (b - 2) ^ 2 := sq_nonneg _
  constructor
  · nlinarith
  · constructor
    · intro h
      have hmul : 4 * Real.pi * ((a - 1) ^ 2 + (b - 2) ^ 2) = 0 := by
        linarith
      have hcoeff : 4 * Real.pi ≠ 0 :=
        mul_ne_zero (by norm_num) (ne_of_gt hpi)
      have hsum : (a - 1) ^ 2 + (b - 2) ^ 2 = 0 :=
        (mul_eq_zero.mp hmul).resolve_left hcoeff
      constructor <;> nlinarith
    · rintro ⟨rfl, rfl⟩
      ring

theorem apm_t02a05
    (omega : apm_t02a05_Form2) (homega : apm_t02a05_isOmega omega) :
    (∀ c : apm_t02a05_E3,
      44 * Real.pi / 15 ≤
        apm_t02a05_outwardSphereIntegral omega c) ∧
    (∀ c : apm_t02a05_E3,
      apm_t02a05_outwardSphereIntegral omega c = 44 * Real.pi / 15 ↔
        c 0 = 1 ∧ c 1 = 2) := by
  constructor
  · intro c
    rw [apm_t02A05_bridge_1 omega homega c]
    exact (apm_t02a05_quadratic_minimum (c 0) (c 1)).1
  · intro c
    rw [apm_t02A05_bridge_1 omega homega c]
    exact (apm_t02a05_quadratic_minimum (c 0) (c 1)).2

#print axioms apm_t02a05
