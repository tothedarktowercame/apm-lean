import ConstructionTargets.CappedCylinderSurfaceIntegral
import ConstructionTargets.UnitDiskOddInverseSqrtIntegrals

/-! # The hemispherical contribution to the capped-cylinder integral

The frozen pullback separates into two reflection-odd terms and the radial
term `1 + (1-r²)⁻¹ᐟ²`.  This file evaluates the latter by the same honest
polar substitution used to establish integrability.
-/

open MeasureTheory Metric Real Set
open scoped Interval
noncomputable section

namespace ConstructionTargets.CappedCylinderHemisphereIntegral

open ConstructionTargets.HemisphereInverseSqrtDiskIntegral
open ConstructionTargets.UnitDiskInverseSqrtIntegrability
open ConstructionTargets.UnitDiskOddInverseSqrtIntegrals

def capHeight (p : ℝ × ℝ) : ℝ :=
  1 + Real.sqrt (1 - p.1 ^ 2 - p.2 ^ 2)

def hemisphereIntegrand (p : ℝ × ℝ) : ℝ :=
  capHeight p -
    (capHeight p ^ 2 * Real.exp (p.1 * capHeight p) *
      Real.log (p.1 ^ 2 + 1) - p.2) * yInverseSqrt p +
    (p.1 + p.2 ^ 2 * capHeight p ^ 3 *
      Real.cos (p.2 ^ 2 + capHeight p ^ 2)) * xInverseSqrt p

def yOddCoefficient (p : ℝ × ℝ) : ℝ :=
  -(capHeight p ^ 2 * Real.exp (p.1 * capHeight p) *
      Real.log (p.1 ^ 2 + 1))

def xOddCoefficient (p : ℝ × ℝ) : ℝ :=
  p.2 ^ 2 * capHeight p ^ 3 *
    Real.cos (p.2 ^ 2 + capHeight p ^ 2)

def yOddTerm (p : ℝ × ℝ) : ℝ := yInverseSqrt p * yOddCoefficient p
def xOddTerm (p : ℝ × ℝ) : ℝ := xInverseSqrt p * xOddCoefficient p

theorem hemisphereIntegrand_decomposition (p : ℝ × ℝ) (hp : p ∈ unitDisk) :
    hemisphereIntegrand p =
      1 + inverseSqrtKernel p + yOddTerm p + xOddTerm p := by
  let s := Real.sqrt (1 - p.1 ^ 2 - p.2 ^ 2)
  have hs_sq : s ^ 2 = 1 - p.1 ^ 2 - p.2 ^ 2 := by
    dsimp [s]
    rw [sq_sqrt]
    change p.1 ^ 2 + p.2 ^ 2 ≤ 1 at hp
    linarith
  have hradial : (p.1 ^ 2 + p.2 ^ 2) * s⁻¹ = s⁻¹ - s := by
    have hr : p.1 ^ 2 + p.2 ^ 2 = 1 - s ^ 2 := by linarith
    rw [hr]
    by_cases hs : s = 0
    · simp [hs]
    · field_simp
  have halgebra : hemisphereIntegrand p =
      capHeight p + (p.1 ^ 2 + p.2 ^ 2) * inverseSqrtKernel p +
        yOddTerm p + xOddTerm p := by
    simp only [hemisphereIntegrand, yOddTerm, xOddTerm, yOddCoefficient,
      xOddCoefficient, xInverseSqrt, yInverseSqrt]
    ring
  rw [halgebra, inverseSqrtKernel]
  simp only [one_div]
  change capHeight p + (p.1 ^ 2 + p.2 ^ 2) * s⁻¹ +
      yOddTerm p + xOddTerm p = _
  rw [hradial]
  simp only [capHeight, s]
  ring

theorem continuous_capHeight : Continuous capHeight := by
  unfold capHeight
  fun_prop

theorem continuous_yOddCoefficient : Continuous yOddCoefficient := by
  unfold yOddCoefficient
  have hlog : Continuous (fun p : ℝ × ℝ => Real.log (p.1 ^ 2 + 1)) :=
    ((continuous_fst.pow 2).add continuous_const).log
      (fun p => (add_pos_of_nonneg_of_pos (sq_nonneg p.1) zero_lt_one).ne')
  exact (((continuous_capHeight.pow 2).mul
    (Real.continuous_exp.comp (continuous_fst.mul continuous_capHeight))).mul hlog).neg

theorem continuous_xOddCoefficient : Continuous xOddCoefficient := by
  unfold xOddCoefficient
  exact ((continuous_snd.pow 2).mul (continuous_capHeight.pow 3)).mul
    (Real.continuous_cos.comp ((continuous_snd.pow 2).add (continuous_capHeight.pow 2)))

theorem isCompact_unitDisk : IsCompact unitDisk := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · unfold unitDisk
    exact isClosed_le (continuous_fst.pow 2 |>.add (continuous_snd.pow 2)) continuous_const
  · refine ((isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).prod
      (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1))).isBounded.subset ?_
    intro p hp
    exact ⟨⟨(abs_le.1 (abs_fst_le_one_of_mem_unitDisk hp)).1,
      (abs_le.1 (abs_fst_le_one_of_mem_unitDisk hp)).2⟩,
      ⟨(abs_le.1 (abs_snd_le_one_of_mem_unitDisk hp)).1,
      (abs_le.1 (abs_snd_le_one_of_mem_unitDisk hp)).2⟩⟩

theorem yOddTerm_integrableOn : IntegrableOn yOddTerm unitDisk := by
  exact yInverseSqrt_integrableOn.mul_continuousOn
    continuous_yOddCoefficient.continuousOn isCompact_unitDisk

theorem xOddTerm_integrableOn : IntegrableOn xOddTerm unitDisk := by
  exact xInverseSqrt_integrableOn.mul_continuousOn
    continuous_xOddCoefficient.continuousOn isCompact_unitDisk

theorem yOddTerm_reflectY (p : ℝ × ℝ) :
    yOddTerm (reflectY p) = -yOddTerm p := by
  rw [yOddTerm, yOddTerm, yInverseSqrt_reflectY]
  have hc : yOddCoefficient (reflectY p) = yOddCoefficient p := by
    simp [yOddCoefficient, capHeight, reflectY]
  rw [hc]
  ring

theorem xOddTerm_reflectX (p : ℝ × ℝ) :
    xOddTerm (reflectX p) = -xOddTerm p := by
  rw [xOddTerm, xOddTerm, xInverseSqrt_reflectX]
  have hc : xOddCoefficient (reflectX p) = xOddCoefficient p := by
    simp [xOddCoefficient, capHeight, reflectX]
  rw [hc]
  ring

theorem integral_yOddTerm_eq_zero : ∫ p in unitDisk, yOddTerm p = 0 := by
  have hmp : MeasurePreserving reflectYEquiv := by
    simpa [reflectYEquiv] using measurePreserving_reflectY
  have hchange := hmp.integral_comp'
    (fun p : ℝ × ℝ => unitDisk.indicator yOddTerm p)
  simp only [reflectYEquiv_apply] at hchange
  have hindicator : (fun p => unitDisk.indicator yOddTerm (reflectY p)) =
      unitDisk.indicator (fun p => yOddTerm (reflectY p)) := by
    funext p
    by_cases hp : p ∈ unitDisk
    · have hr := (reflectY_mem_unitDisk_iff p).mpr hp
      simp [hp, hr]
    · have hr : reflectY p ∉ unitDisk :=
        (reflectY_mem_unitDisk_iff p).not.mpr hp
      simp [hp, hr]
  rw [hindicator] at hchange
  rw [integral_indicator measurableSet_unitDisk,
    integral_indicator measurableSet_unitDisk] at hchange
  simp_rw [yOddTerm_reflectY, integral_neg] at hchange
  linarith

theorem integral_xOddTerm_eq_zero : ∫ p in unitDisk, xOddTerm p = 0 := by
  have hmp : MeasurePreserving reflectXEquiv := by
    simpa [reflectXEquiv] using measurePreserving_reflectX
  have hchange := hmp.integral_comp'
    (fun p : ℝ × ℝ => unitDisk.indicator xOddTerm p)
  simp only [reflectXEquiv_apply] at hchange
  have hindicator : (fun p => unitDisk.indicator xOddTerm (reflectX p)) =
      unitDisk.indicator (fun p => xOddTerm (reflectX p)) := by
    funext p
    by_cases hp : p ∈ unitDisk
    · have hr := (reflectX_mem_unitDisk_iff p).mpr hp
      simp [hp, hr]
    · have hr : reflectX p ∉ unitDisk :=
        (reflectX_mem_unitDisk_iff p).not.mpr hp
      simp [hp, hr]
  rw [hindicator] at hchange
  rw [integral_indicator measurableSet_unitDisk,
    integral_indicator measurableSet_unitDisk] at hchange
  simp_rw [xOddTerm_reflectX, integral_neg] at hchange
  linarith

theorem integral_zero_one_mul_radialInverseSqrt :
    (∫ r in (0 : ℝ)..1, r * radialInverseSqrt r) = 1 := by
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (a := (0 : ℝ)) (b := 1)
    (f := fun r : ℝ => 1 - r ^ 2) (f' := fun r : ℝ => -2 * r)
    (g := fun u : ℝ => u ^ (-(1 / 2 : ℝ)))
    (by fun_prop)
    (fun r _ => by
      simpa [mul_comm] using
        (hasDerivAt_const r 1).sub ((hasDerivAt_id r).pow 2))
    (fun r hr => by norm_num at hr ⊢; linarith)
  have hrpow : (∫ u in (0 : ℝ)..1, u ^ (-(1 / 2 : ℝ))) = 2 := by
    rw [integral_rpow]
    · norm_num
    · left
      norm_num
  have hreverse : (∫ u in (1 : ℝ)..0, u ^ (-(1 / 2 : ℝ))) = -2 := by
    rw [intervalIntegral.integral_symm, hrpow]
  dsimp only [Function.comp_apply] at hsub
  norm_num only [zero_pow, one_pow, sub_zero] at hsub
  change (∫ r in (0 : ℝ)..1,
      (1 - r ^ 2) ^ (-(1 / 2 : ℝ)) * (-2 * r)) =
        ∫ u in (1 : ℝ)..0, u ^ (-(1 / 2 : ℝ)) at hsub
  rw [hreverse] at hsub
  have hscale :
      (∫ r in (0 : ℝ)..1,
        (1 - r ^ 2) ^ (-(1 / 2 : ℝ)) * (-2 * r)) =
        -2 * ∫ r in (0 : ℝ)..1, r * radialInverseSqrt r := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r hr
    norm_num at hr
    change (1 - r ^ 2) ^ (-(1 / 2 : ℝ)) * (-2 * r) =
      -2 * (r * radialInverseSqrt r)
    rw [radialInverseSqrt_eq_rpow (by nlinarith)]
    ring
  rw [hscale] at hsub
  linarith

theorem integral_Ioi_mul_radialInverseSqrt :
    (∫ r in Ioi (0 : ℝ), r * radialInverseSqrt r) = 1 := by
  have htail : IntegrableOn (fun r : ℝ => r * radialInverseSqrt r) (Ioi 1) := by
    apply integrableOn_zero.congr_fun
    · intro r hr
      simp [radialInverseSqrt_eq_zero_of_one_le hr.le]
    · exact measurableSet_Ioi
  have hsplit := intervalIntegral.integral_interval_add_Ioi'
    (a := (0 : ℝ)) (b := 1) intervalIntegrable_mul_radialInverseSqrt htail
  rw [integral_zero_one_mul_radialInverseSqrt] at hsplit
  have hzero : (∫ r in Ioi (1 : ℝ), r * radialInverseSqrt r) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simp [radialInverseSqrt_eq_zero_of_one_le hr.le]
  rw [hzero, add_zero] at hsplit
  exact hsplit.symm

theorem integral_radialInverseSqrt_euclidean :
    (∫ q : E2, radialInverseSqrt ‖q‖) = 2 * Real.pi := by
  rw [MeasureTheory.integral_fun_norm_addHaar (volume : Measure E2) radialInverseSqrt]
  simp only [E2, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSubDiff,
    nsmul_eq_mul, smul_eq_mul]
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_two]
  norm_num
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi)]
  rw [integral_Ioi_mul_radialInverseSqrt]
  ring

def productToE2Equiv : (ℝ × ℝ) ≃ᵐ E2 :=
  (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ).symm.trans
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

@[simp] theorem productToE2Equiv_apply (p : ℝ × ℝ) :
    productToE2Equiv p = productToE2 p := rfl

theorem integral_inverseSqrtKernel_unitDisk :
    (∫ p in unitDisk, inverseSqrtKernel p) = 2 * Real.pi := by
  rw [← integral_indicator measurableSet_unitDisk]
  have hpoint : unitDisk.indicator inverseSqrtKernel =
      (fun q : E2 => radialInverseSqrt ‖q‖) ∘ productToE2 := by
    funext p
    by_cases hp : p ∈ unitDisk
    · rw [indicator_of_mem hp]
      exact inverseSqrtKernel_eq_radial p
    · rw [indicator_of_notMem hp]
      have hr : 1 ≤ ‖productToE2 p‖ := by
        rw [← sq_le_sq₀ (by positivity) (norm_nonneg _), productToE2_norm_sq]
        change ¬p.1 ^ 2 + p.2 ^ 2 ≤ 1 at hp
        linarith
      simp [radialInverseSqrt_eq_zero_of_one_le hr]
  rw [hpoint]
  have hmp : MeasurePreserving productToE2Equiv := by
    simpa [productToE2Equiv, productToE2, Function.comp_def] using
      measurePreserving_productToE2
  have hchange :
      (∫ p : ℝ × ℝ, ((fun q : E2 => radialInverseSqrt ‖q‖) ∘ productToE2) p) =
        ∫ q : E2, radialInverseSqrt ‖q‖ :=
    hmp.integral_comp'
      (fun q : E2 => radialInverseSqrt ‖q‖)
  calc
    (∫ p : ℝ × ℝ, ((fun q : E2 => radialInverseSqrt ‖q‖) ∘ productToE2) p) =
        ∫ q : E2, radialInverseSqrt ‖q‖ := hchange
    _ = 2 * Real.pi := integral_radialInverseSqrt_euclidean

theorem volume_unitDisk : volume.real unitDisk = Real.pi := by
  have hpre : productToE2 ⁻¹' closedBall (0 : E2) 1 = unitDisk := by
    ext p
    simp only [mem_preimage, mem_closedBall, dist_zero_right, unitDisk]
    constructor
    · intro h
      have hs := (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).2 h
      rw [productToE2_norm_sq] at hs
      change p.1 ^ 2 + p.2 ^ 2 ≤ 1
      norm_num at hs
      exact hs
    · intro h
      apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).1
      rw [productToE2_norm_sq]
      change p.1 ^ 2 + p.2 ^ 2 ≤ 1 at h
      norm_num
      exact h
  rw [← hpre]
  have hm : volume (productToE2 ⁻¹' closedBall (0 : E2) 1) =
      volume (closedBall (0 : E2) 1) :=
    measurePreserving_productToE2.measure_preimage
      measurableSet_closedBall.nullMeasurableSet
  rw [measureReal_def, hm, EuclideanSpace.volume_closedBall_fin_two]
  norm_num
  positivity

theorem integral_one_add_inverseSqrtKernel :
    (∫ p in unitDisk, (1 + inverseSqrtKernel p)) = 3 * Real.pi := by
  have hone : Integrable (fun _ : ℝ × ℝ => (1 : ℝ))
      (volume.restrict unitDisk) :=
    integrableOn_const isCompact_unitDisk.measure_lt_top.ne
  have hk : Integrable inverseSqrtKernel (volume.restrict unitDisk) :=
    radialInverseSqrtIntegrable
  rw [integral_add hone hk]
  rw [setIntegral_const, volume_unitDisk, integral_inverseSqrtKernel_unitDisk]
  simp
  ring

theorem hemisphereIntegrand_integrableOn :
    IntegrableOn hemisphereIntegrand unitDisk := by
  rw [integrableOn_congr_fun hemisphereIntegrand_decomposition
    measurableSet_unitDisk]
  exact ((integrableOn_const isCompact_unitDisk.measure_lt_top.ne).add
    radialInverseSqrtIntegrable).add yOddTerm_integrableOn |>.add xOddTerm_integrableOn

theorem hemisphere_surface_integral :
    (∫ p in unitDisk, hemisphereIntegrand p) = 3 * Real.pi := by
  rw [setIntegral_congr_fun measurableSet_unitDisk
    hemisphereIntegrand_decomposition]
  have hbase : Integrable (fun p : ℝ × ℝ => 1 + inverseSqrtKernel p)
      (volume.restrict unitDisk) :=
    (integrableOn_const isCompact_unitDisk.measure_lt_top.ne).add
      radialInverseSqrtIntegrable
  have hbasey : Integrable
      (fun p : ℝ × ℝ => 1 + inverseSqrtKernel p + yOddTerm p)
      (volume.restrict unitDisk) := hbase.add yOddTerm_integrableOn
  rw [integral_add hbasey xOddTerm_integrableOn,
    integral_add hbase yOddTerm_integrableOn]
  rw [integral_yOddTerm_eq_zero, integral_xOddTerm_eq_zero, add_zero, add_zero]
  exact integral_one_add_inverseSqrtKernel

theorem hemisphere_surface_integral_of_pointwise
    (pullback : ℝ × ℝ → ℝ)
    (hpullback : ∀ p, pullback p = hemisphereIntegrand p) :
    (∫ p in unitDisk, pullback p) = 3 * Real.pi := by
  rw [setIntegral_congr_fun measurableSet_unitDisk (fun p _ => hpullback p)]
  exact hemisphere_surface_integral

#print axioms integral_zero_one_mul_radialInverseSqrt
#print axioms integral_inverseSqrtKernel_unitDisk
#print axioms hemisphere_surface_integral
#print axioms hemisphere_surface_integral_of_pointwise

end ConstructionTargets.CappedCylinderHemisphereIntegral
