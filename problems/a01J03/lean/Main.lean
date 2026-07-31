import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Analysis.Calculus.Deriv.Basic

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

/-- A pointwise-convergent series of monotone real functions is monotone. -/
lemma pointwiseSum_monotone
    (fns : ℕ → ℝ → ℝ) (hmono : ∀ n, Monotone (fns n))
    (hsummable : ∀ x, Summable fun n => fns n x) :
    Monotone (pointwiseSum fns) := by
  intro x y hxy
  exact (hsummable x).tsum_le_tsum (fun n => hmono n hxy) (hsummable y)

/-- Part (1): the derivative of the series exists a.e. and equals the sum of derivatives. -/
theorem deriv_sum_of_monotone
    (f : ℝ → ℝ) (fns : ℕ → ℝ → ℝ)
    (hmono : ∀ n, Monotone (fns n))
    (hsummable : ∀ x, Summable fun n => fns n x)
    (hf : ∀ x, f x = pointwiseSum fns x) :
    ∀ᵐ x ∂volume, HasDerivAt f (derivativeSum fns x) x := by
  -- Remaining construction: identify the Lebesgue--Stieltjes measure of this
  -- pointwise sum with the countable sum of the summands' Stieltjes measures,
  -- then use `HaveLebesgueDecomposition.sum_left` and
  -- `Monotone.ae_hasDerivAt` to identify their Radon--Nikodym densities a.e.
  sorry

/-- Part (2): convert the `HasDerivAt` statement into an equality of classical derivatives a.e. -/
theorem deriv_sum_of_monotone_ae
    (f : ℝ → ℝ) (fns : ℕ → ℝ → ℝ)
    (hmono : ∀ n, Monotone (fns n))
    (hsummable : ∀ x, Summable fun n => fns n x)
    (hf : ∀ x, f x = pointwiseSum fns x) :
    deriv f =ᵐ[volume] derivativeSum fns := by
  filter_upwards [deriv_sum_of_monotone f fns hmono hsummable hf] with x hx
  exact hx.deriv

end APM
