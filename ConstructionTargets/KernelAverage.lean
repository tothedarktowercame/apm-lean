import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Kernel-weighted averages in `Lᵖ`

This module packages the Bochner triangle inequality in the form used by
kernel averages, together with a convenient sufficient condition for the
weighted family to be Bochner integrable.
-/

open MeasureTheory

noncomputable section

namespace ConstructionTargets.KernelAverage

/-- An integrable scalar kernel times an a.e. strongly measurable uniformly
bounded Banach-valued family is Bochner integrable. -/
lemma integrable_kernel_smul_of_norm_le
    {Y E : Type*} [MeasurableSpace Y] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ν : Measure Y} {k : Y → ℝ} {F : Y → E}
    (hk : Integrable k ν) (hF : AEStronglyMeasurable F ν)
    {C : ℝ} (hC : ∀ᵐ y ∂ν, ‖F y‖ ≤ C) :
    Integrable (fun y ↦ k y • F y) ν := by
  refine (hk.norm.const_mul C).mono'
    (hk.aestronglyMeasurable.smul hF) ?_
  filter_upwards [hC] with y hy
  rw [norm_smul, Real.norm_eq_abs]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hy (abs_nonneg (k y))

/-- Minkowski's integral inequality for a nonnegative scalar kernel and an
`Lᵖ`-valued family. -/
theorem norm_integral_kernel_smul_le
    {Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X]
    {ν : Measure Y} {μ : Measure X} {p : ENNReal} [Fact (1 ≤ p)]
    {k : Y → ℝ} (hk : ∀ᵐ y ∂ν, 0 ≤ k y)
    (F : Y → Lp ℝ p μ) :
    ‖∫ y, k y • F y ∂ν‖ ≤ ∫ y, k y * ‖F y‖ ∂ν := by
  calc
    ‖∫ y, k y • F y ∂ν‖ ≤ ∫ y, ‖k y • F y‖ ∂ν :=
      norm_integral_le_integral_norm _
    _ = ∫ y, k y * ‖F y‖ ∂ν := by
      apply integral_congr_ae
      filter_upwards [hk] with y hy
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hy]

end ConstructionTargets.KernelAverage
