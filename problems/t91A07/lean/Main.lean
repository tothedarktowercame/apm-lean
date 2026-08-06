import Mathlib

open scoped ContDiff Topology

/-!
# APM t91A07 — nondegenerate fixed points are isolated

## Statement repairs

None.

## Encoding note

The theorem is stated in a finite-dimensional real coordinate chart, exactly
as the problem's hint requires.  Here `fderiv f x - id` being bijective is the
coordinate-free linear formulation of “`df_x` has no eigenvalue `+1`”, and the
neighborhood conclusion says precisely that each fixed point is isolated.
-/

theorem apm_t91a07
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → E) (hf : ContDiff ℝ ∞ f)
    (hnondegenerate : ∀ x, f x = x →
      Function.Bijective
        (fderiv ℝ f x - ContinuousLinearMap.id ℝ E)) :
    ∀ x, f x = x →
      ∃ U ∈ 𝓝 x, ∀ y ∈ U, f y = y → y = x := by
  sorry
