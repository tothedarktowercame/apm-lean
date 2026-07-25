/-
! # APM a95A08: Length of image curve ≥ 2π, with equality iff Δ ⊆ D

f is analytic near Δ̄, injective on Δ̄, f(0) = 0, |f'(0)| = 1.
(a) The length ℓ(C) of C = f(∂Δ) satisfies ℓ(C) ≥ 2π.
(b) ℓ(C) > 2π only if Δ ⊄ D = f(Δ).

## Proof strategy (from informal proof)

1. **Jensen's inequality**: (1/2π)∫|f'(e^{iθ})| dθ ≥ exp((1/2π)∫log|f'|)
2. **Mean value for harmonic functions**: (1/2π)∫log|f'(e^{iθ})| = log|f'(0)| = 0
3. Combining: ℓ(C) ≥ 2π · exp(0) = 2π.
4. Equality: |f'| ≡ 1 → f is a rotation → Δ ⊆ D.
5. Contrapositive: Δ ⊆ D → Schwarz lemma forces f = rotation → ℓ = 2π.

## Theory boundaries

- Jensen's inequality for integrals with convex functions is available via
  `ConvexOn.le_integral` in Mathlib, but requires measure-theoretic setup.
- The mean value property for log|f'| (subharmonic/harmonic) requires either
  the Poisson integral formula or the fact that log|g| is harmonic when g is
  holomorphic and nonvanishing. Mathlib has harmonic function results but
  the specific mean value formula for log|f'| on the circle is not directly
  available.
- The Schwarz equality case (|f'(0)| = 1 + maps Δ to Δ ⟹ rotation) is not
  in Mathlib's Schwarz.lean — only the inequality `norm_le_norm_of_mapsTo_ball`
  is proved.

## Statement repair

The generated `curveLength` uses interval integral from 0 to 2π of ‖deriv f (exp(I*θ))‖.
This is correct for the arc length formula. We keep it as-is.
The `hf_holo` hypothesis uses `∃ ε > 0, DifferentiableOn ... (closedBall 0 (1+ε))`
which correctly captures "analytic in a neighborhood of Δ̄."
-/

import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open Complex Metric Set Real MeasureTheory

noncomputable section

/-- The length of the image curve: ℓ(C) = ∫₀²π ‖f'(e^{iθ})‖ dθ. -/
def curveLength (f : ℂ → ℂ) : ℝ :=
  ∫ θ in (0:ℝ)..(2 * π), ‖deriv f (exp (I * ↑θ))‖

/-- Part 1: ℓ(C) ≥ 2π.

**Blocker:** The proof requires:
1. Jensen's inequality for the convex function exp, applied to log|f'|.
2. The mean value property for the harmonic function log|f'| on the disk.
3. Combining these with |f'(0)| = 1.

Jensen's inequality for integrals (`ConvexOn.le_integral`) is in Mathlib but
requires setting up the probability measure on [0,2π]. The mean value property
for log|f'| requires that log|f'| is harmonic, which holds when f' ≠ 0
(f is univalent ⟹ f' ≠ 0). Mathlib has the Poisson integral formula but not
the specific mean-value-on-circle result for log|holomorphic function|. -/
theorem curve_length_ge_two_pi
    {f : ℂ → ℂ}
    (hf_holo : ∃ ε > 0, DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_inj : InjOn f (closedBall 0 1))
    (hf_zero : f 0 = 0)
    (hf_deriv : ‖deriv f 0‖ = 1) :
    2 * π ≤ curveLength f := by
  sorry

/-- Part 2: ℓ(C) > 2π ⟹ Δ ⊄ f(Δ).

By contrapositive: if Δ ⊆ f(Δ), then f⁻¹ restricted to Δ is a disk self-map
fixing 0 with |(f⁻¹)'(0)| = 1/|f'(0)| = 1. By Schwarz lemma equality case,
f⁻¹ is a rotation, so f is a rotation, giving |f'| ≡ 1 and ℓ(C) = 2π.

**Blocker:** The Schwarz equality case (|f'(0)| = 1 + disk self-map ⟹ rotation)
is not in Mathlib. Only the inequality `norm_le_norm_of_mapsTo_ball` is proved. -/
theorem disk_not_subset_image_of_length_gt
    {f : ℂ → ℂ}
    (hf_holo : ∃ ε > 0, DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_inj : InjOn f (closedBall 0 1))
    (hf_zero : f 0 = 0)
    (hf_deriv : ‖deriv f 0‖ = 1)
    (hlen : 2 * π < curveLength f) :
    ¬(ball (0 : ℂ) 1 ⊆ f '' ball 0 1) := by
  sorry

/-- If Δ ⊆ D and f(0) = 0, |f'(0)| = 1, then f is a rotation (Schwarz equality).

This is the key step for Part 2's contrapositive. If f maps Δ into a domain
containing Δ, then f|_Δ is a disk self-map with |f'(0)| = 1. By the Schwarz
lemma equality case, f(z) = e^{iα}z.

**Blocker:** The Schwarz equality case is not in Mathlib.
Mathlib has `Complex.norm_le_norm_of_mapsTo_ball` (the inequality) but not
the equality characterization. -/
lemma rotation_of_disk_subset_image
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f (ball 0 1))
    (hf_zero : f 0 = 0) (hf_deriv : ‖deriv f 0‖ = 1)
    (h_subset : ball (0 : ℂ) 1 ⊆ f '' ball 0 1) :
    ∃ α : ℝ, ∀ z ∈ ball (0 : ℂ) 1, f z = exp (I * ↑α) * z := by
  sorry

/-- Jensen's inequality for the exponential on the circle:
(1/2π) ∫ g ≥ exp((1/2π) ∫ log g) when g > 0.

This follows from the convexity of exp applied to the probability measure
(1/2π) dθ on [0, 2π].

**What was tried:**
- `ConvexOn.le_integral` requires a measure and convexity proof.
- The probability measure on [0,2π] with density 1/(2π) needs to be set up.
- Mathlib's convexity results (`Real.convexOn_exp`) exist but the measure-
  theoretic Jensen inequality needs additional setup. -/
lemma jensen_exp_circle
    {g : ℝ → ℝ} (hg_meas : AEStronglyMeasurable g (volume.restrict (Icc 0 (2 * π))))
    (hg_int : IntegrableOn g (Icc 0 (2 * π)) volume)
    (hg_pos : ∀ θ ∈ Icc (0:ℝ) (2 * π), 0 < g θ) :
    Real.exp ((1 / (2 * π)) * ∫ θ in (0:ℝ)..(2 * π), Real.log (g θ)) ≤
      (1 / (2 * π)) * ∫ θ in (0:ℝ)..(2 * π), g θ := by
  sorry

end
