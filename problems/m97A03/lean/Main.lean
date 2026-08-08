import Mathlib

/-!
# APM m97A03: A nonlinear integral equation

## Statement repairs

None.

## Encoding questions

None. The singular kernel is encoded exactly in a Lebesgue integral on
`[0,1]`. Its convention-dependent value at the single endpoint `s = 0` does
not affect the integral.
-/

open MeasureTheory Set

noncomputable section

def apm_m97A03_isSolution (lam : ℝ) (u : ℝ → ℝ) : Prop :=
  ContinuousOn u (Icc 0 1) ∧
  ∀ t ∈ Icc (0 : ℝ) 1,
    u t - lam * (∫ s in Icc (0 : ℝ) 1,
      Real.sqrt ((t + 3) / s) * Real.sin (t * u s)) = Real.exp t

lemma apm_m97A03_t_sqrt_bound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ t * Real.sqrt (t + 3) ∧ t * Real.sqrt (t + 3) ≤ 2 := by
  have ht3 : 0 ≤ t + 3 := by linarith [ht.1]
  have hs0 : 0 ≤ Real.sqrt (t + 3) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (t + 3) ≤ 2 := by
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [ht.2]⟩
  constructor
  · exact mul_nonneg ht.1 hs0
  · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) hs0]

/-- The endpoint singularity used to dominate the Hammerstein kernel is
integrable, with its sharp elementary integral. -/
lemma apm_m97A03_integral_rpow_neg_half :
    (∫ s in Icc (0 : ℝ) 1, s ^ (-1 / 2 : ℝ)) = 2 := by
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [integral_rpow (Or.inl (by norm_num))]
  norm_num

/-- Away from the null endpoint, the singular square-root kernel factors into
its parameter part and the integrable power majorant. -/
lemma apm_m97A03_sqrt_div_factor {t s : ℝ} (ht : 0 ≤ t + 3) (hs : 0 < s) :
    Real.sqrt ((t + 3) / s) =
      Real.sqrt (t + 3) * s ^ (-1 / 2 : ℝ) := by
  rw [Real.sqrt_div ht]
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hs.le]
  rfl

/-- The factor in the Lipschitz estimate is pointwise dominated by the sharp
integrable majorant on the punctured interval. -/
lemma apm_m97A03_kernel_lipschitz_majorant {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : 0 < s) :
    t * Real.sqrt ((t + 3) / s) ≤ 2 * s ^ (-1 / 2 : ℝ) := by
  rw [apm_m97A03_sqrt_div_factor (by linarith [ht.1]) hs]
  have hpow : 0 ≤ s ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hs.le _
  calc
    t * (Real.sqrt (t + 3) * s ^ (-1 / 2 : ℝ)) =
        (t * Real.sqrt (t + 3)) * s ^ (-1 / 2 : ℝ) := by ring
    _ ≤ 2 * s ^ (-1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right (apm_m97A03_t_sqrt_bound ht).2 hpow

/-- Pointwise Lipschitz domination for the nonlinear singular integrand. -/
lemma apm_m97A03_integrand_sub_bound {t s u v : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : 0 < s) :
    |Real.sqrt ((t + 3) / s) * (Real.sin (t * u) - Real.sin (t * v))| ≤
      2 * s ^ (-1 / 2 : ℝ) * |u - v| := by
  have hk0 : 0 ≤ Real.sqrt ((t + 3) / s) := Real.sqrt_nonneg _
  have hsin := Real.abs_sin_sub_sin_le (t * u) (t * v)
  have huv0 : 0 ≤ |u - v| := abs_nonneg _
  calc
    |Real.sqrt ((t + 3) / s) * (Real.sin (t * u) - Real.sin (t * v))| =
        Real.sqrt ((t + 3) / s) * |Real.sin (t * u) - Real.sin (t * v)| := by
          rw [abs_mul, abs_of_nonneg hk0]
    _ ≤ Real.sqrt ((t + 3) / s) * |t * u - t * v| :=
      mul_le_mul_of_nonneg_left hsin hk0
    _ = (t * Real.sqrt ((t + 3) / s)) * |u - v| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg ht.1]
      ring
    _ ≤ (2 * s ^ (-1 / 2 : ℝ)) * |u - v| :=
      mul_le_mul_of_nonneg_right (apm_m97A03_kernel_lipschitz_majorant ht hs) huv0

theorem apm_m97a03
    (lam : ℝ) (hlam : |lam| < (1 / 4 : ℝ)) :
    ∃ u : ℝ → ℝ, apm_m97A03_isSolution lam u := by
  /-
  PARTIAL boundary (codex).  The intended Banach fixed-point route is viable:
  sibling `t91A04` proves the abstract `ContractingWith.fixedPoint` wrapper,
  and Mathlib provides `Real.abs_sin_sub_sin_le`,
  `tendsto_integral_filter_of_dominated_convergence`, and
  `intervalIntegral.integral_rpow`.  However, applying those results here
  still requires a substantial concrete operator construction on
  `ContinuousMap (Icc (0 : ℝ) 1) ℝ`:

  * prove integrability on `Icc 0 1` of the singular majorant
    `s ↦ s ^ (-1 / 2 : ℝ)` and reconcile it a.e. with the statement's
    `Real.sqrt ((t + 3) / s)` (including Lean's value at `s = 0`);
  * use dominated convergence to package the parameterized singular integral
    as a continuous map (the packaged theorem
    `continuous_parametric_integral_of_continuous` does not apply because the
    kernel is not continuous at zero);
  * combine the now-proved load-bearing factor estimate
    `apm_m97A03_t_sqrt_bound` with the singular integral to establish the
    uniform sup-norm estimate with constant `4 * |lam|`, define the self-map,
    and transport the resulting fixed point back to an unrestricted function
    satisfying the frozen set-integral equation.

  Searches of `LEMMA-INDEX.md`, all closed artifacts, the nearby Hammerstein
  artifacts, `ConstructionTargets/`, and `YoungL2.lean` found no compiled
  helper combining these singular-kernel steps.  The abstract fixed-point
  theorem alone therefore does not close the goal within this pass's budget.
  The mathematical statement appears sound.

  Closer hop 1 proves `apm_m97A03_integral_rpow_neg_half`, closing the sharp
  majorant calculation `∫_[0,1] s⁻¹ᐟ² = 2` by converting the set integral to an
  interval integral and applying Mathlib's `integral_rpow`. Together with
  `apm_m97A03_t_sqrt_bound`, the numerical constant `4` is therefore fully
  accounted for. The remaining bridge is dominated parameter continuity for
  the singular kernel and its packaging as a contracting self-map of
  `ContinuousMap (Icc 0 1) ℝ`; the frozen statement is unchanged.

  CLOSER HOP 2 closes the pointwise singular-kernel reconciliation that hop 1
  left open. `apm_m97A03_sqrt_div_factor` proves away from the null endpoint
  that `sqrt ((t+3)/s) = sqrt (t+3) * s^(-1/2)`.
  `apm_m97A03_kernel_lipschitz_majorant` combines this identity with the
  existing `t * sqrt (t+3) ≤ 2` estimate, and
  `apm_m97A03_integrand_sub_bound` applies
  `Real.abs_sin_sub_sin_le` to obtain the exact pointwise domination
  `|K(t,s,u)-K(t,s,v)| ≤ 2*s^(-1/2)*|u-v|`. Thus the a.e. majorant required
  for the contraction estimate is now compiled, including its endpoint-safe
  formulation via the hypothesis `0 < s`.

  What remains is integrating this pointwise inequality while replacing
  `|u s-v s|` by the `ContinuousMap` sup norm, then proving dominated
  continuity in `t` and bundling the self-map. Searches of the parametric
  Bochner-integral and `ContinuousMap` APIs found no theorem that combines
  this a.e.-singular majorant with the required packaged continuity, so that
  final assembly remains honestly open.
  -/
  sorry
