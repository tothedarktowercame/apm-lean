import Mathlib

open Complex Filter Metric Set

noncomputable section

/-!
# APM a94A08

## Statement repairs

None.

## Encoding notes

The source numbers its iterates from `f₁ = f`; consequently the Lean sequence uses
`f^[n + 1]` rather than the zeroth iterate. Uniform convergence on
every compact subset is stated directly with `TendstoUniformlyOn`.
-/

theorem apm_a94a08
    {f : ℂ → ℂ}
    (hf_analytic : DifferentiableOn ℂ f (ball 0 1))
    (hf_selfmap : MapsTo f (ball 0 1) (ball 0 1))
    (hf_zero : f 0 = 0)
    (hf_deriv : ‖deriv f 0‖ < 1) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ ball 0 1 →
      TendstoUniformlyOn
        (fun n ↦ f^[n + 1])
        (fun _ : ℂ ↦ 0) atTop K := by
  sorry
