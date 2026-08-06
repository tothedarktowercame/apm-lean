import Mathlib

/-!
# APM a98A02

## Statement repairs

None.

## Encoding questions

None. A function defined measurably on `[0,1]` is represented by an ambient
function whose zero extension from `[0,1]` is measurable. Membership in
`L¹[0,1]` is encoded by `IntegrableOn` for Lebesgue measure, and the Kronecker
delta is written as `if n = m then 1 else 0`.
-/

open Filter MeasureTheory Set
open scoped Topology

theorem apm_a98a02 (g : ℕ → ℝ → ℝ) (M : ℝ)
    (hg_meas : ∀ n, Measurable ((Icc (0 : ℝ) 1).indicator (g n)))
    (hg_bound : ∀ n x, x ∈ Icc (0 : ℝ) 1 → |g n x| ≤ M)
    (hg_orthonormal : ∀ n m,
      (∫ x in Icc (0 : ℝ) 1, g n x * g m x ∂volume) =
        if n = m then 1 else 0) :
    ∀ f : ℝ → ℝ, IntegrableOn f (Icc (0 : ℝ) 1) volume →
      Tendsto
        (fun n => ∫ x in Icc (0 : ℝ) 1, f x * g n x ∂volume)
        atTop (𝓝 0) := by
  -- SKIPPED: needs Bessel's inequality (∑|⟨f,g_n⟩|²≤‖f‖₂², NOT in Mathlib)
  -- and L²-dense-in-L¹ approximation argument with uniform functional bound M.
  -- -- (Memory: e-codexpilot-extend-weak-convergence-from-a-dense-linear-span-by-uniform-boundedness)
  --    confirms strategy: Bessel on L² + density + uniform bound propagates to L¹.
  -- APIs searched: `Bessel`, `bessel` — NOT FOUND. `tendsto_atTop_of_summable` — FOUND but
  -- need to build the summability from orthonormality first.
  sorry
