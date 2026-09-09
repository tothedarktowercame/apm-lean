import ConstructionTargets.UnitDiskInverseSqrtIntegrability

open MeasureTheory Set
noncomputable section

namespace ConstructionTargets.UnitDiskOddInverseSqrtIntegrals

open ConstructionTargets.HemisphereInverseSqrtDiskIntegral
open ConstructionTargets.UnitDiskInverseSqrtIntegrability

theorem measurableSet_unitDisk : MeasurableSet unitDisk := by
  apply measurableSet_le
  · fun_prop
  · fun_prop

theorem abs_fst_le_one_of_mem_unitDisk {p : ℝ × ℝ} (hp : p ∈ unitDisk) :
    |p.1| ≤ 1 := by
  change p.1 ^ 2 + p.2 ^ 2 ≤ 1 at hp
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg p.2]

theorem abs_snd_le_one_of_mem_unitDisk {p : ℝ × ℝ} (hp : p ∈ unitDisk) :
    |p.2| ≤ 1 := by
  change p.1 ^ 2 + p.2 ^ 2 ≤ 1 at hp
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg p.1]

theorem xInverseSqrt_integrableOn : IntegrableOn xInverseSqrt unitDisk := by
  refine inverseSqrtKernel_integrable.integrableOn.mono'
    ((continuous_fst.aestronglyMeasurable.mul
      inverseSqrtKernel_integrable.aestronglyMeasurable).mono_measure
        (Measure.restrict_le_self)) ?_
  filter_upwards [ae_restrict_mem measurableSet_unitDisk] with p hp
  have hk : 0 ≤ inverseSqrtKernel p := by
    simp [inverseSqrtKernel]
  simp only [Real.norm_eq_abs, xInverseSqrt, abs_mul, abs_of_nonneg hk]
  calc
    |p.1| * inverseSqrtKernel p ≤ 1 * inverseSqrtKernel p :=
      mul_le_mul_of_nonneg_right (abs_fst_le_one_of_mem_unitDisk hp) hk
    _ = inverseSqrtKernel p := one_mul _

theorem yInverseSqrt_integrableOn : IntegrableOn yInverseSqrt unitDisk := by
  refine inverseSqrtKernel_integrable.integrableOn.mono'
    ((continuous_snd.aestronglyMeasurable.mul
      inverseSqrtKernel_integrable.aestronglyMeasurable).mono_measure
        (Measure.restrict_le_self)) ?_
  filter_upwards [ae_restrict_mem measurableSet_unitDisk] with p hp
  have hk : 0 ≤ inverseSqrtKernel p := by
    simp [inverseSqrtKernel]
  simp only [Real.norm_eq_abs, yInverseSqrt, abs_mul, abs_of_nonneg hk]
  calc
    |p.2| * inverseSqrtKernel p ≤ 1 * inverseSqrtKernel p :=
      mul_le_mul_of_nonneg_right (abs_snd_le_one_of_mem_unitDisk hp) hk
    _ = inverseSqrtKernel p := one_mul _

theorem measurePreserving_reflectX : MeasurePreserving reflectX := by
  simpa [reflectX] using
    (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      (MeasurePreserving.id (volume : Measure ℝ))

theorem measurePreserving_reflectY : MeasurePreserving reflectY := by
  simpa [reflectY] using
    (MeasurePreserving.id (volume : Measure ℝ)).prod
      (Measure.measurePreserving_neg (volume : Measure ℝ))

def reflectXEquiv : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toEquiv :=
    { toFun := reflectX
      invFun := reflectX
      left_inv := by intro p; simp [reflectX]
      right_inv := by intro p; simp [reflectX] }
  measurable_toFun := by fun_prop
  measurable_invFun := by fun_prop

def reflectYEquiv : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toEquiv :=
    { toFun := reflectY
      invFun := reflectY
      left_inv := by intro p; simp [reflectY]
      right_inv := by intro p; simp [reflectY] }
  measurable_toFun := by fun_prop
  measurable_invFun := by fun_prop

@[simp] theorem reflectXEquiv_apply (p : ℝ × ℝ) : reflectXEquiv p = reflectX p := rfl
@[simp] theorem reflectYEquiv_apply (p : ℝ × ℝ) : reflectYEquiv p = reflectY p := rfl

theorem integral_xInverseSqrt_unitDisk_eq_zero :
    ∫ p in unitDisk, xInverseSqrt p = 0 := by
  have hpre : reflectX ⁻¹' unitDisk = unitDisk := by
    ext p
    exact reflectX_mem_unitDisk_iff p
  have hmp : MeasurePreserving reflectXEquiv := by
    simpa [reflectXEquiv] using measurePreserving_reflectX
  have hchange := hmp.integral_comp'
    (fun p : ℝ × ℝ => unitDisk.indicator xInverseSqrt p)
  simp only [reflectXEquiv_apply] at hchange
  rw [show (fun p => unitDisk.indicator xInverseSqrt (reflectX p)) =
      unitDisk.indicator (fun p => xInverseSqrt (reflectX p)) by
        funext p
        by_cases hp : p ∈ unitDisk
        · have hr : reflectX p ∈ unitDisk := (reflectX_mem_unitDisk_iff p).2 hp
          simp [Set.indicator_of_mem hp, Set.indicator_of_mem hr]
        · have hr : reflectX p ∉ unitDisk := by
            simpa [reflectX_mem_unitDisk_iff] using hp
          simp [hp, hr] ] at hchange
  rw [integral_indicator (measurableSet_unitDisk)] at hchange
  rw [integral_indicator (measurableSet_unitDisk)] at hchange
  simp_rw [xInverseSqrt_reflectX, integral_neg] at hchange
  linarith only [hchange]

theorem integral_yInverseSqrt_unitDisk_eq_zero :
    ∫ p in unitDisk, yInverseSqrt p = 0 := by
  have hpre : reflectY ⁻¹' unitDisk = unitDisk := by
    ext p
    exact reflectY_mem_unitDisk_iff p
  have hmp : MeasurePreserving reflectYEquiv := by
    simpa [reflectYEquiv] using measurePreserving_reflectY
  have hchange := hmp.integral_comp'
    (fun p : ℝ × ℝ => unitDisk.indicator yInverseSqrt p)
  simp only [reflectYEquiv_apply] at hchange
  rw [show (fun p => unitDisk.indicator yInverseSqrt (reflectY p)) =
      unitDisk.indicator (fun p => yInverseSqrt (reflectY p)) by
        funext p
        by_cases hp : p ∈ unitDisk
        · have hr : reflectY p ∈ unitDisk := (reflectY_mem_unitDisk_iff p).2 hp
          simp [Set.indicator_of_mem hp, Set.indicator_of_mem hr]
        · have hr : reflectY p ∉ unitDisk := by
            simpa [reflectY_mem_unitDisk_iff] using hp
          simp [hp, hr] ] at hchange
  rw [integral_indicator (measurableSet_unitDisk)] at hchange
  rw [integral_indicator (measurableSet_unitDisk)] at hchange
  simp_rw [yInverseSqrt_reflectY, integral_neg] at hchange
  linarith only [hchange]

#print axioms xInverseSqrt_integrableOn
#print axioms yInverseSqrt_integrableOn
#print axioms measurePreserving_reflectX
#print axioms measurePreserving_reflectY
#print axioms integral_xInverseSqrt_unitDisk_eq_zero
#print axioms integral_yInverseSqrt_unitDisk_eq_zero

end ConstructionTargets.UnitDiskOddInverseSqrtIntegrals
