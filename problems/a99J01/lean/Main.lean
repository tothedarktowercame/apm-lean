import Mathlib

open MeasureTheory Set

noncomputable section

/-!
# APM a99J01

## Statement repairs

None.

## Encoding notes

The integral of `log |f|` may equal `-∞` when `f` vanishes. Consequently it is
encoded as an `EReal` extended integral: the difference of the lintegrals of its
positive and negative parts. At a zero of `f`, the negative part is `⊤`, correctly
representing `log 0 = -∞`; using Lean's real-valued `Real.log 0 = 0` directly would
misstate the problem.
-/

def apmLogAbsPositive {X : Type*} (f : X → ℝ) (x : X) : ENNReal :=
  ENNReal.ofReal (Real.log |f x|)

def apmLogAbsNegative {X : Type*} (f : X → ℝ) (x : X) : ENNReal :=
  if f x = 0 then ⊤ else ENNReal.ofReal (-Real.log |f x|)

noncomputable def apmLogIntegralOn {X : Type*} [MeasurableSpace X]
    (f : X → ℝ) (E : Set X) (mu : Measure X) : EReal :=
  ((∫⁻ x in E, apmLogAbsPositive f x ∂mu : ENNReal) : EReal) -
    ((∫⁻ x in E, apmLogAbsNegative f x ∂mu : ENNReal) : EReal)

theorem apm_a99j01
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (f : X → ℝ)
    (hf : Integrable f mu)
    (hf_norm : ∫ x, |f x| ∂mu = 1) :
    ∀ E : Set X, MeasurableSet E → 0 < mu E → mu E < ⊤ →
      apmLogIntegralOn f E mu ≤
        ((-((mu E).toReal) * Real.log (mu E).toReal : ℝ) : EReal) := by
  -- SKIPPED: Jensen's inequality for concave log on EReal-valued integrals.
  -- Key idea: by Jensen on E with prob measure μ|_E/μ(E):
  --   (1/μ(E))∫_E log|f| ≤ log((1/μ(E))∫_E |f|) ≤ log(1/μ(E))
  -- hence ∫_E log|f| ≤ -μ(E)log(μ(E)).
  -- The EReal encoding (handling log(0) = -∞) makes the Jensen inequality
  -- and EReal arithmetic particularly delicate.
  -- APIs: `MeasureTheory.Integral.Jensen` — need to check if exists; EReal arithmetic
  -- is not well-supported for integral inequalities.
  sorry
