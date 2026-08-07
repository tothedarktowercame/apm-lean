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
  -/
  sorry
