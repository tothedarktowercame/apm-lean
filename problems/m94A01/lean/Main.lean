import Mathlib

/-!
# APM m94A01 — five-point Laplacian error

## Statement repairs

Continuity of the fourth derivatives gives a local bound, not a uniform global
constant on `ℝ²`.  The claimed estimate is therefore stated locally at each
point for sufficiently small `h`.
-/
noncomputable def apm_m94a01_T (u : ℝ × ℝ → ℝ) (h x y : ℝ) : ℝ :=
  (u (x+h,y)+u (x-h,y)+u (x,y+h)+u (x,y-h)-4*u (x,y))/h^2

noncomputable def apm_m94a01_laplacian (u : ℝ × ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (deriv fun s => u (s,y)) x + deriv (deriv fun s => u (x,s)) y

theorem apm_m94a01 (u : ℝ × ℝ → ℝ)
    (hu : ContDiff ℝ 4 u) :
    ∀ x y : ℝ, ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ h : ℝ, 0 < |h| → |h| < δ →
        |apm_m94a01_laplacian u x y - apm_m94a01_T u h x y| ≤ C*h^2 := by
  /-
  Boundary: the intended proof applies fourth-order Taylor bounds separately
  to the coordinate slices `s ↦ u (s, y)` and `s ↦ u (x, s)`, adds the
  `+h` and `-h` formulas to cancel odd terms, and divides the combined
  fourth-order remainder by `h ^ 2`.

  I searched Mathlib's Taylor APIs `taylor_mean_remainder_bound`,
  `exists_taylor_mean_remainder_bound`, and
  `taylor_mean_remainder_lagrange_iteratedDeriv`. They provide the needed
  interval-wise estimates, but I did not complete the bridge from
  `ContDiff ℝ 4 u` to `ContDiffOn` for both coordinate slices, rewrite the
  `taylorWithinEval` coefficients as the nested `deriv` expressions used by
  `apm_m94a01_laplacian`, or combine the two locally chosen derivative bounds
  into the exact `C, δ` conclusion after division by nonzero `h ^ 2`. No
  compiled sibling supplied this slice-Taylor normalization within this pass.
  -/
  sorry
