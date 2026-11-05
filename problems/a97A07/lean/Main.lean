import Mathlib

/-!
# a97A07: the Hermite interpolation integral over a Jordan curve

Registered statement (claude-14, 2026-11-05). The earlier proof, for a circle
centred at 0 and an entire `f`, was graded narrower; it is kept in
`holes/labs/out-of-competition/a97A07/CircleEntire.lean` and does not count.

Encoding choices:
* A Jordan curve is a 1-periodic map `γ : ℝ → ℂ`, injective on `[0, 1)`. The
  problem integrates over `γ`, so `γ` is rectifiable; it is taken Lipschitz,
  which every rectifiable curve is after reparametrisation by arc length.
* The interior of `γ` is the set of points off the curve whose connected
  component in the complement is bounded.
* The integral `(1/2πi) ∫_γ` presumes the positive orientation; it is stated as
  winding number 1 about some interior point.
* "Analytic inside and on `γ`" is analyticity at every point of the interior
  and of the curve.
* The printed conclusion "degree `n - 1`" is false (for `f = 1` the integral is
  the constant 1); see `problems/a97A07/PRELIM-DEFECT.md`. The statement asks
  for degree at most `n - 1`.
-/

open Complex Polynomial MeasureTheory Real Set

noncomputable section

/-- The polynomial `p(z) = ∏ (z - z_k)`. -/
def apm_a97A07_p {n : ℕ} (zs : Fin n → ℂ) : Polynomial ℂ :=
  ∏ k, (Polynomial.X - Polynomial.C (zs k))

/-- The divided difference `(p(ζ) - p(z)) / (ζ - z)`, extended by `p'(ζ)` at `z = ζ`. -/
def apm_a97A07_Q {n : ℕ} (zs : Fin n → ℂ) (ζ z : ℂ) : ℂ :=
  if z = ζ then (Polynomial.derivative (apm_a97A07_p zs)).eval ζ
  else ((apm_a97A07_p zs).eval ζ - (apm_a97A07_p zs).eval z) / (ζ - z)

/-- The contour integral `(1/2πi) ∫_γ (f(ζ)/p(ζ)) (p(ζ) - p(z))/(ζ - z) dζ`,
with `γ` parametrised over one period `[0, 1]`. -/
def apm_a97A07_P {n : ℕ} (zs : Fin n → ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ) (z : ℂ) : ℂ :=
  (1 / (2 * π * I)) * ∫ t in (0 : ℝ)..1,
    f (γ t) / (apm_a97A07_p zs).eval (γ t) * apm_a97A07_Q zs (γ t) z * deriv γ t

/-- A rectifiable closed Jordan curve, parametrised with period 1. -/
structure apm_a97A07_IsJordanCurve (γ : ℝ → ℂ) : Prop where
  periodic : Function.Periodic γ 1
  injOn : Set.InjOn γ (Set.Ico 0 1)
  lipschitz : ∃ K, LipschitzWith K γ

/-- The interior of `γ`: points off the curve in a bounded component of the complement. -/
def apm_a97A07_inside (γ : ℝ → ℂ) : Set ℂ :=
  {w | w ∉ range γ ∧ Bornology.IsBounded (connectedComponentIn (range γ)ᶜ w)}

/-- `γ` winds once, positively, around some interior point. -/
def apm_a97A07_PositivelyOriented (γ : ℝ → ℂ) : Prop :=
  ∃ w ∈ apm_a97A07_inside γ,
    (1 / (2 * π * I)) * ∫ t in (0 : ℝ)..1, (γ t - w)⁻¹ * deriv γ t = 1

theorem apm_a97A07 {n : ℕ} (zs : Fin n → ℂ) (hzs : Function.Injective zs)
    (γ : ℝ → ℂ) (hγ : apm_a97A07_IsJordanCurve γ) (hpos : apm_a97A07_PositivelyOriented γ)
    (hin : ∀ k, zs k ∈ apm_a97A07_inside γ)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (apm_a97A07_inside γ ∪ range γ)) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ n - 1 ∧
      (∀ z, apm_a97A07_P zs f γ z = P.eval z) ∧
      ∀ k, apm_a97A07_P zs f γ (zs k) = f (zs k) := by
  sorry

end
