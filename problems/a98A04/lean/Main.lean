import Mathlib

/-!
# APM a98A04

## Statement repairs

None.  The source's informal equation `sup = ∞` is represented by its
well-typed real-valued meaning: every real height is exceeded.

## Encoding questions

None.
-/

open MeasureTheory Set

/-- The singular spike `f_{a,b}` defined in the problem. -/
noncomputable def apm_a98a04_spike (a b x : ℝ) : ℝ :=
  if a < x ∧ x < b then 1 / Real.sqrt ((b - a) * (x - a)) else 0

theorem apm_a98a04 :
    (∀ a b : ℝ, a < b →
      Integrable (apm_a98a04_spike a b) volume ∧
      ∫ x : ℝ, apm_a98a04_spike a b x ∂volume = 2) ∧
    (∃ f : ℝ → ℝ,
      Integrable f volume ∧
      ∀ (g : ℝ → ℝ), g =ᵐ[volume] f →
        ∀ α β : ℝ, α < β →
          ∀ M : ℝ, ∃ x ∈ Ioo α β, M < g x) := by
  -- SKIPPED: part (a) needs ∫1/√((b-a)(x-a))dx=2 via u=√(x-a) substitution;
  -- part (b) needs enumerating ℚ-intervals + summing spikes via MCT/convergence theorem.
  -- APIs: `IntegralSubstitution`, `integrableOn_Ioc`, `tendsto_integral_of_dominated_convergence`
  -- -- (Memory: e-codexpilot-refute-essential-boundedness-at-a-singularity-on-a-positive-measure-ball)
  --    confirms: spike functions are locally unbounded but integrable.
  sorry
