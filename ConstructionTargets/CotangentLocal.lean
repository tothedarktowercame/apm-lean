import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import ConstructionTargets.AnalyticDivision

/-!
# The removable part of `π cot (πz)`

This module supplies the local analytic data needed by square-contour proofs
for the Basel sums.  The complex sinc function is constructed with `dslope`,
so its value at zero is part of the definition rather than an assumed limit.
-/

open Complex Real Set Function Filter Topology

noncomputable section

namespace ConstructionTargets.CotangentLocal

/-- Cotangent with argument `πz` is periodic under translation by an integer.
This is proved from the sine and cosine addition formulas. -/
theorem cot_pi_add_int (z : ℂ) (k : ℤ) :
    Complex.cot ((Real.pi : ℂ) * (z + (k : ℂ))) =
      Complex.cot ((Real.pi : ℂ) * z) := by
  rw [show (Real.pi : ℂ) * (z + (k : ℂ)) =
      (Real.pi : ℂ) * z + ((k : ℝ) * Real.pi : ℝ) by
    push_cast; ring]
  have hs : Complex.sin (((k : ℝ) * Real.pi : ℝ) : ℂ) = 0 := by
    rw [← Complex.ofReal_sin]
    exact_mod_cast Real.sin_int_mul_pi k
  have hc : Complex.cos (((k : ℝ) * Real.pi : ℝ) : ℂ) = ((-1 : ℝ) ^ k : ℝ) := by
    simpa using congrArg ((↑) : ℝ → ℂ) (Real.cos_int_mul_pi k)
  rw [Complex.cot, Complex.sin_add, Complex.cos_add, hs, hc]
  rw [Complex.cot]
  have hk : (((-1 : ℝ) ^ k : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (zpow_ne_zero k (by norm_num : (-1 : ℝ) ≠ 0))
  simp only [mul_zero, sub_zero, add_zero, div_eq_mul_inv, mul_inv_rev]
  calc
    _ = Complex.cos ((Real.pi : ℂ) * z) *
        ((((-1 : ℝ) ^ k : ℝ) : ℂ) * ((((-1 : ℝ) ^ k : ℝ) : ℂ))⁻¹) *
        (Complex.sin ((Real.pi : ℂ) * z))⁻¹ := by ring
    _ = _ := by rw [mul_inv_cancel₀ hk]; simp

/-- The entire extension of `sin (πz) / (πz)` across `z = 0`. -/
def sincPi (z : ℂ) : ℂ :=
  dslope (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) 0 z / (Real.pi : ℂ)

/-- The `dslope` construction makes complex sinc entire. -/
theorem differentiable_sincPi : Differentiable ℂ sincPi := by
  apply differentiableOn_univ.mp
  apply DifferentiableOn.div_const
  exact (Complex.differentiableOn_dslope (s := Set.univ) Filter.univ_mem).mpr
    (by fun_prop)

/-- Multiplying complex sinc by `z` recovers `sin (πz) / π`, including at
zero.  This identity determines all Taylor coefficients at zero. -/
theorem mul_sincPi (z : ℂ) :
    z * sincPi z = Complex.sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ) := by
  by_cases hz : z = 0
  · simp [hz, sincPi]
  · rw [sincPi, dslope_of_ne _ hz]
    rw [slope]
    simp only [sub_zero, smul_eq_mul, vsub_eq_sub, mul_zero,
      Complex.sin_zero]
    field_simp

/-- Complex sinc has value one at zero. -/
@[simp] theorem sincPi_zero : sincPi 0 = 1 := by
  rw [sincPi, dslope_same]
  rw [show deriv (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w)) 0 =
      (Real.pi : ℂ) by
    convert ((Complex.hasDerivAt_sin ((Real.pi : ℂ) * 0)).comp 0
      (hasDerivAt_const_mul (Real.pi : ℂ))).deriv using 1 <;> simp]
  exact div_self (ofReal_ne_zero.mpr Real.pi_ne_zero)

private theorem contDiffAt_sincPi (n : ℕ) : ContDiffAt ℂ n sincPi 0 :=
  (differentiable_sincPi.analyticAt 0).contDiffAt.of_le (by exact_mod_cast le_top)

private theorem iterated_identity (n : ℕ) :
    iteratedDeriv (n + 1) (fun z : ℂ => z * sincPi z) 0 =
      iteratedDeriv (n + 1)
        (fun z : ℂ => Complex.sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ)) 0 := by
  congr 1
  funext z
  exact mul_sincPi z

/-- The first derivative of complex sinc vanishes at zero. -/
theorem deriv_sincPi_zero : deriv sincPi 0 = 0 := by
  have h := iterated_identity 1
  norm_num at h
  change iteratedDeriv 2 ((fun z : ℂ => z) * sincPi) 0 = _ at h
  rw [iteratedDeriv_mul (n := 2) (x := (0 : ℂ)) (by fun_prop)
      (contDiffAt_sincPi 2)] at h
  rw [congrFun (iteratedDeriv_comp_const_mul (n := 2)
    Complex.contDiff_sin (Real.pi : ℂ)) 0] at h
  simp [iteratedDeriv_fun_id_zero, Finset.sum_range_succ,
    Complex.iteratedDeriv_even_sin] at h
  exact h

/-- The second derivative of complex sinc at zero is `-π²/3`. -/
theorem iteratedDeriv_two_sincPi_zero :
    iteratedDeriv 2 sincPi 0 = -(Real.pi : ℂ) ^ 2 / 3 := by
  have h := iterated_identity 2
  norm_num at h
  change iteratedDeriv 3 ((fun z : ℂ => z) * sincPi) 0 = _ at h
  rw [iteratedDeriv_mul (n := 3) (x := (0 : ℂ)) (by fun_prop)
      (contDiffAt_sincPi 3)] at h
  rw [congrFun (iteratedDeriv_comp_const_mul (n := 3)
    Complex.contDiff_sin (Real.pi : ℂ)) 0] at h
  simp [iteratedDeriv_fun_id_zero, Finset.sum_range_succ,
    Complex.iteratedDeriv_odd_sin] at h
  calc
    iteratedDeriv 2 sincPi 0 = (-((Real.pi : ℂ) ^ 3) / (Real.pi : ℂ)) / 3 := by
      linear_combination h / 3
    _ = -(Real.pi : ℂ) ^ 2 / 3 := by
      field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]

/-- The third derivative of complex sinc vanishes at zero. -/
theorem iteratedDeriv_three_sincPi_zero :
    iteratedDeriv 3 sincPi 0 = 0 := by
  have h := iterated_identity 3
  norm_num at h
  change iteratedDeriv 4 ((fun z : ℂ => z) * sincPi) 0 = _ at h
  rw [iteratedDeriv_mul (n := 4) (x := (0 : ℂ)) (by fun_prop)
      (contDiffAt_sincPi 4)] at h
  rw [congrFun (iteratedDeriv_comp_const_mul (n := 4)
    Complex.contDiff_sin (Real.pi : ℂ)) 0] at h
  simp [iteratedDeriv_fun_id_zero, Finset.sum_range_succ,
    Complex.iteratedDeriv_even_sin] at h
  exact h

/-- The fourth derivative of complex sinc at zero is `π⁴/5`. -/
theorem iteratedDeriv_four_sincPi_zero :
    iteratedDeriv 4 sincPi 0 = (Real.pi : ℂ) ^ 4 / 5 := by
  have h := iterated_identity 4
  norm_num at h
  change iteratedDeriv 5 ((fun z : ℂ => z) * sincPi) 0 = _ at h
  rw [iteratedDeriv_mul (n := 5) (x := (0 : ℂ)) (by fun_prop)
      (contDiffAt_sincPi 5)] at h
  rw [congrFun (iteratedDeriv_comp_const_mul (n := 5)
    Complex.contDiff_sin (Real.pi : ℂ)) 0] at h
  simp [iteratedDeriv_fun_id_zero, Finset.sum_range_succ,
    Complex.iteratedDeriv_odd_sin] at h
  calc
    iteratedDeriv 4 sincPi 0 = (((Real.pi : ℂ) ^ 5) / (Real.pi : ℂ)) / 5 := by
      linear_combination h / 5
    _ = (Real.pi : ℂ) ^ 4 / 5 := by
      field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]

/-- The analytic extension at zero of `π cot (πz) - 1/z`.  It is the
logarithmic derivative of complex sinc. -/
def regularCot (z : ℂ) : ℂ := logDeriv sincPi z

/-- The regular part of cotangent is analytic at zero. -/
theorem analyticAt_regularCot_zero : AnalyticAt ℂ regularCot 0 := by
  unfold regularCot logDeriv
  exact (differentiable_sincPi.analyticAt 0).deriv.div
    (differentiable_sincPi.analyticAt 0) (by simp)

private theorem eventually_mul_regularCot :
    (fun z => regularCot z * sincPi z) =ᶠ[𝓝 (0 : ℂ)] deriv sincPi := by
  have hs : ∀ᶠ z in 𝓝 (0 : ℂ), sincPi z ≠ 0 :=
    differentiable_sincPi.continuous.continuousAt.eventually_ne (by simp)
  filter_upwards [hs] with z hz
  simp [regularCot, logDeriv_apply, hz]

/-- The regular part is odd, hence has value zero at the origin. -/
@[simp] theorem regularCot_zero : regularCot 0 = 0 := by
  simp [regularCot, logDeriv_apply, deriv_sincPi_zero]

private theorem contDiffAt_regularCot (n : ℕ) : ContDiffAt ℂ n regularCot 0 :=
  analyticAt_regularCot_zero.contDiffAt.of_le (by exact_mod_cast le_top)

/-- The linear Taylor coefficient of `π cot (πz) - 1/z` is `-π²/3`. -/
theorem deriv_regularCot_zero :
    deriv regularCot 0 = -(Real.pi : ℂ) ^ 2 / 3 := by
  have h := eventually_mul_regularCot.iteratedDeriv_eq 1
  change iteratedDeriv 1 (regularCot * sincPi) 0 = _ at h
  rw [iteratedDeriv_mul (n := 1) (x := (0 : ℂ))
      (contDiffAt_regularCot 1) (contDiffAt_sincPi 1)] at h
  rw [← iteratedDeriv_succ'] at h
  simp [Finset.sum_range_succ, deriv_sincPi_zero, iteratedDeriv_two_sincPi_zero,
    iteratedDeriv_succ'] at h
  exact h

/-- The quadratic Taylor coefficient of the odd regular part vanishes. -/
theorem iteratedDeriv_two_regularCot_zero :
    iteratedDeriv 2 regularCot 0 = 0 := by
  have h := eventually_mul_regularCot.iteratedDeriv_eq 2
  change iteratedDeriv 2 (regularCot * sincPi) 0 = _ at h
  rw [iteratedDeriv_mul (n := 2) (x := (0 : ℂ))
      (contDiffAt_regularCot 2) (contDiffAt_sincPi 2)] at h
  rw [← iteratedDeriv_succ'] at h
  simp [Finset.sum_range_succ, deriv_sincPi_zero,
    iteratedDeriv_two_sincPi_zero, iteratedDeriv_three_sincPi_zero,
    deriv_regularCot_zero] at h
  exact h

/-- The cubic Taylor coefficient of `π cot (πz) - 1/z` is `-π⁴/45`:
equivalently its third derivative at zero is `-2π⁴/15`. -/
theorem iteratedDeriv_three_regularCot_zero :
    iteratedDeriv 3 regularCot 0 = -2 * (Real.pi : ℂ) ^ 4 / 15 := by
  have h := eventually_mul_regularCot.iteratedDeriv_eq 3
  change iteratedDeriv 3 (regularCot * sincPi) 0 = _ at h
  rw [iteratedDeriv_mul (n := 3) (x := (0 : ℂ))
      (contDiffAt_regularCot 3) (contDiffAt_sincPi 3)] at h
  rw [← iteratedDeriv_succ'] at h
  simp [Finset.sum_range_succ, deriv_sincPi_zero,
    iteratedDeriv_two_sincPi_zero, iteratedDeriv_three_sincPi_zero,
    iteratedDeriv_four_sincPi_zero, deriv_regularCot_zero] at h
  linear_combination h

/-- The residue coefficient needed by the fourth-power Basel contour. -/
theorem cot_cubic_coefficient :
    iteratedDeriv 3 regularCot 0 / 6 = -(Real.pi : ℂ) ^ 4 / 45 := by
  rw [iteratedDeriv_three_regularCot_zero]
  ring

/-- The numerator left after removing the linear and cubic Taylor terms of
the regular cotangent part.  It has a zero of order at least four at `0`. -/
def cotFourthNumerator (z : ℂ) : ℂ :=
  regularCot z + (Real.pi : ℂ) ^ 2 / 3 * z +
    (Real.pi : ℂ) ^ 4 / 45 * z ^ 3

/-- The first four derivatives of the fourth-order numerator vanish. -/
theorem cotFourthNumerator_vanishes {k : ℕ} (hk : k < 4) :
    iteratedDeriv k cotFourthNumerator 0 = 0 := by
  change iteratedDeriv k
    (fun z : ℂ => (regularCot z + (Real.pi : ℂ) ^ 2 / 3 * z) +
      (Real.pi : ℂ) ^ 4 / 45 * z ^ 3) 0 = 0
  have houter :
      (fun z : ℂ => (regularCot z + (Real.pi : ℂ) ^ 2 / 3 * z) +
        (Real.pi : ℂ) ^ 4 / 45 * z ^ 3) =
      (fun z : ℂ => regularCot z + (Real.pi : ℂ) ^ 2 / 3 * z) +
        (fun z : ℂ => (Real.pi : ℂ) ^ 4 / 45 * z ^ 3) := rfl
  rw [houter]
  rw [iteratedDeriv_add (n := k) (x := (0 : ℂ))
    (f := fun z : ℂ => regularCot z + (Real.pi : ℂ) ^ 2 / 3 * z)
    (g := fun z : ℂ => (Real.pi : ℂ) ^ 4 / 45 * z ^ 3)
    ((contDiffAt_regularCot k).add (by fun_prop)) (by fun_prop)]
  have hinner :
      (fun z : ℂ => regularCot z + (Real.pi : ℂ) ^ 2 / 3 * z) =
      regularCot + (fun z : ℂ => (Real.pi : ℂ) ^ 2 / 3 * z) := rfl
  rw [hinner]
  rw [iteratedDeriv_add (n := k) (x := (0 : ℂ))
    (f := regularCot)
    (g := fun z : ℂ => (Real.pi : ℂ) ^ 2 / 3 * z)
    (contDiffAt_regularCot k) (by fun_prop)]
  rw [iteratedDeriv_const_mul_field
    ((Real.pi : ℂ) ^ 2 / 3) (fun z : ℂ => z)]
  rw [iteratedDeriv_const_mul_field
    ((Real.pi : ℂ) ^ 4 / 45) (fun z : ℂ => z ^ 3)]
  interval_cases k
  · simp
  · simp [iteratedDeriv_succ', deriv_regularCot_zero]
    ring
  · simp [iteratedDeriv_two_regularCot_zero, iteratedDeriv_succ']
  · simp [iteratedDeriv_three_regularCot_zero, iteratedDeriv_succ']
    ring

/-- The analytic extension at zero of the regular cotangent remainder divided
by `z⁴`. -/
def cotFourthRemainder : ℂ → ℂ :=
  ConstructionTargets.AnalyticDivision.dividedByPower 4 0 cotFourthNumerator

/-- The fourth-order remainder is analytic at zero. -/
theorem analyticAt_cotFourthRemainder_zero :
    AnalyticAt ℂ cotFourthRemainder 0 := by
  apply ConstructionTargets.AnalyticDivision.analyticAt_dividedByPower
  unfold cotFourthNumerator
  exact (analyticAt_regularCot_zero.add (by fun_prop)).add (by fun_prop)

/-- Off zero, the analytic remainder is the expected quotient. -/
theorem cotFourthRemainder_eq_div {z : ℂ} (hz : z ≠ 0) :
    cotFourthRemainder z = cotFourthNumerator z / z ^ 4 := by
  simpa [cotFourthRemainder] using
    (ConstructionTargets.AnalyticDivision.dividedByPower_eq_div
      (n := 4) (a := (0 : ℂ)) (z := z)
      (f := cotFourthNumerator) (by
        unfold cotFourthNumerator
        exact (analyticAt_regularCot_zero.add (by fun_prop)).add (by fun_prop))
      (fun k hk => cotFourthNumerator_vanishes hk) hz)

/-- Away from zero, the `dslope` definition is the usual quotient. -/
theorem sincPi_eq_div {z : ℂ} (hz : z ≠ 0) :
    sincPi z = Complex.sin ((Real.pi : ℂ) * z) /
      ((Real.pi : ℂ) * z) := by
  have h := mul_sincPi z
  apply (eq_div_iff (mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) hz)).mpr
  calc
    sincPi z * ((Real.pi : ℂ) * z) =
        (Real.pi : ℂ) * (z * sincPi z) := by ring
    _ = (Real.pi : ℂ) *
        (Complex.sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ)) := by rw [h]
    _ = Complex.sin ((Real.pi : ℂ) * z) := by
      field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]

/-- The extension agrees with `π cot (πz) - 1/z` off the integers. -/
theorem regularCot_eq_cot_sub_inv {z : ℂ} (hz : z ∈ integerComplement) :
    regularCot z = (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) - 1 / z := by
  let q : ℂ → ℂ := fun w => Complex.sin ((Real.pi : ℂ) * w) /
    ((Real.pi : ℂ) * w)
  have hz0 : z ≠ 0 := integerComplement.ne_zero hz
  have heq : sincPi =ᶠ[𝓝 z] q := by
    have hne : ∀ᶠ w in 𝓝 z, w ≠ 0 :=
      continuousAt_id.eventually_ne hz0
    filter_upwards [hne] with w hw
    exact sincPi_eq_div hw
  rw [regularCot, logDeriv_apply, heq.deriv_eq, heq.self_of_nhds]
  exact logDeriv_sin_div_eq_cot hz

end ConstructionTargets.CotangentLocal
