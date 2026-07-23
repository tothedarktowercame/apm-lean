import Mathlib/MeasureTheory/Measure/Lebesgue/Basic
import Mathlib/MeasureTheory/Function/AEEqOfIntegral
import Mathlib/MeasureTheory/Function/Deriv

open MeasureTheory Filter

noncomputable section

namespace APM

open scoped Topology

/-- Pointwise sum of the monotone sequence of maps. -/
def pointwiseSum (fns : ℕ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n, fns n x

/-- Pointwise sum of the derivatives. -/
def derivativeSum (fns : ℕ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n, deriv (fun y => fns n y) x

/-- Part (1): the derivative of the series exists a.e. and equals the sum of derivatives. -/
theorem deriv_sum_of_monotone
    (f : ℝ → ℝ) (fns : ℕ → ℝ → ℝ)
    (hmono : ∀ n, Monotone (fns n))
    (hsummable : ∀ x, Summable fun n => fns n x)
    (hf : ∀ x, f x = pointwiseSum fns x) :
    ∀ᵐ x ∂volume, HasDerivAt f (derivativeSum fns x) x := by
  -- Skeleton: use that each monotone function is a.e. differentiable (Lebesgue's theorem)
  -- and exchange derivative with summation via dominated convergence of difference quotients.
  sorry

/-- Part (2): convert the `HasDerivAt` statement into an equality of classical derivatives a.e. -/
theorem deriv_sum_of_monotone_ae
    (f : ℝ → ℝ) (fns : ℕ → ℝ → ℝ)
    (hmono : ∀ n, Monotone (fns n))
    (hsummable : ∀ x, Summable fun n => fns n x)
    (hf : ∀ x, f x = pointwiseSum fns x) :
    deriv f =ᵐ[volume] derivativeSum fns := by
  classical
  have h := deriv_sum_of_monotone f fns hmono hsummable hf
  -- TODO: turn the `HasDerivAt` witness delivered by `h` into a statement about `deriv f`.
  sorry

end APM
