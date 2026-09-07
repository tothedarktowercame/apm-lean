import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # APM t99A04: periods along separating and nonseparating curves

## Statement repairs

The undefined space `F` is repaired to the surface `X`, and the intended first
answer requires `X` to be closed.  Mathlib does not yet expose integration of
differential forms on oriented manifolds or Stokes' theorem, so the separating
surface assertion is NOT encoded as a proxy.  The theorem records the exact
one-dimensional integral calculations used after pulling back: an exact form
has zero period on a loop, while a constant form realizes every real period.

## Encoding questions

The circle is parametrized by `[0,1]`; equality of endpoint values is the loop
condition.  The second conjunct is the torus counterexample's `c dx` period.
-/

open intervalIntegral

theorem apm_t99a04
    (g : ℝ → ℝ) (hg : ContinuousOn g (Set.uIcc 0 1))
    (hderiv : ∀ x ∈ Set.uIoo (0 : ℝ) 1, HasDerivAt g (deriv g x) x)
    (hint : IntervalIntegrable (deriv g) volume 0 1) (hloop : g 1 = g 0) :
    (∫ x in (0 : ℝ)..1, deriv g x) = 0 ∧
    ∀ c : ℝ, (∫ _x in (0 : ℝ)..1, c) = c := by
  sorry
