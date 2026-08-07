import Mathlib

/-!
# APM a99J10 — boundary uniqueness under square-root growth

## Statement repairs

The displayed bound `|f(x + iy)| ≤ |y|⁻¹ᐟ²` is singular when `y = 0`.
It is therefore imposed when `y ≠ 0`, which is the minimal domain restriction
needed to express the source's intended blow-up bound without assigning it a
spurious finite value on the real diameter.

## Encoding notes

The radial limit is expressed as `r → 1⁻` for every angle in `[0, 2π]`.
-/

open Set Filter
open scoped Topology
open Metric

/-- Imaginary part of the standard radial parametrization. -/
lemma apm_a99J10_polar_im (r θ : ℝ) :
    (((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im) =
      r * Real.sin θ := by
  simp [Complex.mul_im, Complex.exp_re, Complex.exp_im]

/-- A radius in `[0,1)` parametrizes a point of the open unit disk. -/
lemma apm_a99J10_polar_mem_ball {r θ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff]
  rw [norm_mul, Complex.norm_exp]
  simpa [abs_of_nonneg hr0] using hr1

/-- The frozen growth hypothesis becomes an explicit angular majorant on
each circle. This is the input needed for a dominated boundary-limit route. -/
lemma apm_a99J10_polar_bound
    (f : ℂ → ℂ)
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, z.im ≠ 0 →
      ‖f z‖ ≤ Real.rpow |z.im| (-(1 : ℝ) / 2))
    {r θ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hsin : Real.sin θ ≠ 0) :
    ‖f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤
      Real.rpow |r * Real.sin θ| (-(1 : ℝ) / 2) := by
  have hb := hbound ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
    (apm_a99J10_polar_mem_ball hr0.le hr1)
    (by rw [apm_a99J10_polar_im]; exact mul_ne_zero hr0.ne' hsin)
  simpa [apm_a99J10_polar_im] using hb

theorem apm_a99j10 (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, z.im ≠ 0 →
      ‖f z‖ ≤ Real.rpow |z.im| (-(1 : ℝ) / 2))
    (hradial : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
      Tendsto
        (fun r : ℝ => f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
        (𝓝[<] (1 : ℝ)) (𝓝 0)) :
    ∀ z ∈ ball (0 : ℂ) 1, f z = 0 := by
  /-
  PARTIAL boundary (closer hop 1): the geometry of the radial parametrization
  and the exact circlewise majorant are now compiled above. In particular,
  `apm_a99J10_polar_bound` rewrites the frozen hypothesis as
  `‖f (r e^{iθ})‖ ≤ |r sin θ|⁻¹ᐟ²` away from the two real-axis angles.

  I inspected Mathlib's actual `Analysis/Complex/PhragmenLindelof.lean` (the
  original comment understated the available API), but its strip/sector
  theorems expect continuous boundary control and do not consume radial limits
  with this integrable angular singularity. `ConstructionTargets.RadialMajorantAE`
  concerns one-dimensional Poisson/Lebesgue differentiation and is unrelated.
  The remaining bridge is to prove integrability of `|sin θ|⁻¹ᐟ²`, use the
  displayed bound for dominated convergence of circle/Cauchy integrals as
  `r → 1⁻`, and conclude every interior Cauchy integral is zero.
  -/
  sorry
