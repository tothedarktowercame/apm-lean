import Mathlib

/-!
# APM a99J08: A square-root bound at a mixed-boundary corner

## Statement repairs

1. The source writes `D = {z : |z| < 1}` followed by `Im(z) = y > 0`.
   This is interpreted as the open upper half-disk, as required for the two
   stated conditions to be boundary conditions.
2. The quotient `|g(z)| / |z|^(1/2)` is undefined at `z = 0`, although the
   source asks for boundedness on all of `closure D`. We state the equivalent
   global estimate `|g(z)| ≤ C * sqrt |z|`, which is meaningful at the corner.

## Encoding questions

None.
-/

open Set Complex

noncomputable section

/-- The open upper half of the complex unit disk. -/
def apm_a99J08_upperHalfDisk : Set ℂ :=
  Metric.ball 0 1 ∩ {z | 0 < z.im}

theorem apm_a99j08
    (g : ℂ → ℂ)
    (hgcont : ContinuousOn g (closure apm_a99J08_upperHalfDisk))
    (hgholo : DifferentiableOn ℂ g apm_a99J08_upperHalfDisk)
    (hpos : ∀ x : ℝ, 0 < x → x < 1 → (g x).re = 0)
    (hneg : ∀ x : ℝ, -1 < x → x < 0 → (g x).im = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ closure apm_a99J08_upperHalfDisk,
        ‖g z‖ ≤ C * Real.sqrt ‖z‖ := by
  sorry
