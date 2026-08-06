import Mathlib

/-!
# APM a97J07

## Statement repairs

None.

## Encoding questions

None. Analyticity on the open disk is encoded as complex differentiability
there, and the two boundary estimates retain the source's strict upper- and
lower-semicircle hypotheses.
-/

open Complex Metric Set

theorem apm_a97j07 (f : ℂ → ℂ) (a b : ℝ)
    (hf_cont : ContinuousOn f (closedBall (0 : ℂ) 1))
    (hf_analytic : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (ha : ∀ z ∈ sphere (0 : ℂ) 1, 0 < z.im → ‖f z‖ ≤ a)
    (hb : ∀ z ∈ sphere (0 : ℂ) 1, z.im < 0 → ‖f z‖ ≤ b) :
    ‖f 0‖ ≤ Real.sqrt (a * b) := by
  sorry
  -- Proof: g(z) = f(z)·f(-z). On the sphere, z↦-z swaps upper/lower arcs,
  -- so |g(z)| ≤ ab everywhere on the sphere. By max modulus, |g(0)| ≤ ab.
  -- Since g(0) = f(0)², |f(0)|² ≤ ab, so |f(0)| ≤ √(ab).
  --
  -- APIs needed:
  -- - `Complex.norm_le_of_forall_mem_frontier_norm_le` (max modulus principle)
  -- - `DiffContOnCl.mk_ball` from DifferentiableOn + ContinuousOn
  -- - `norm_mul`, `Real.le_sqrt`
