import Mathlib

noncomputable section

/-!
# APM a94A07

## Statement repairs

None.

## Encoding notes

An entire function is encoded by `Differentiable ℂ f`, and one-to-one by
`Function.Injective f`.
-/

theorem apm_a94a07
    {f : ℂ → ℂ}
    (hf_entire : Differentiable ℂ f)
    (hf_injective : Function.Injective f) :
    ∃ a₀ a₁ : ℂ, a₁ ≠ 0 ∧ ∀ z : ℂ, f z = a₀ + a₁ * z := by
  -- Step 0: f is non-constant (injective on ℂ which has ≥ 2 points).
  have h_nonconst : ∃ z₁ z₂ : ℂ, f z₁ ≠ f z₂ :=
    ⟨0, 1, fun h => absurd (hf_injective h) (by norm_num : (0 : ℂ) ≠ 1)⟩
  -- Step 1 (BLOCKED): f must be a polynomial.
  --
  -- The informal proof classifies the singularity of g(w) = f(1/w) at w = 0:
  --   • Removable ⟹ f bounded ⟹ f constant (Liouville) ⟹ not injective. ✓ (ruled out)
  --   • Essential ⟹ Casorati-Weierstrass/Picard ⟹ f not injective. ✗ (BLOCKED)
  --   • Pole of order n ⟹ f is a degree-n polynomial.
  --
  -- Ruling out the essential case requires Casorati-Weierstrass or Picard's
  -- great theorem, neither of which is in Mathlib (as of v4.29.0-rc8).
  --
  -- APIs searched (all NOT FOUND):
  --   `Casorati*`, `casorati*`, `Picard*`, `picard*`,
  --   `essential_singularity*`, `essentialSing*`,
  --   `winding*`, `WindingNumber*`, `windingNumber*`,
  --   `Rouche*`, `rouche*`, `argument_principle*`
  --
  -- Available but insufficient:
  --   `Differentiable.apply_eq_apply_of_bounded` (Liouville: bounded entire ⟹ constant)
  --   `AnalyticOnNhd.is_constant_or_isOpenMap` (open mapping theorem)
  --   `Differentiable.hasFPowerSeriesOnBall` (Taylor expansion)
  --   `norm_deriv_le_of_forall_mem_sphere_norm_le` (Cauchy estimates)
  --   `analyticOrderAt` (order of vanishing)
  --
  -- Routes tried and why they fail:
  --   1. Growth estimate route: injectivity does not give a polynomial growth
  --      bound on ‖f(z)‖ without already knowing f is a polynomial.
  --   2. Open mapping route: gives f(ℂ) is open, but cannot show f is polynomial
  --      or even that f(ℂ) = ℂ (surjectivity also needs Picard).
  --   3. Cauchy estimate route: ‖f^(n)(0)‖ ≤ C·n!/R^n for all R, but without
  --      a growth bound on C(R) = sup_{|z|=R} ‖f(z)‖, we cannot conclude
  --      f^(n)(0) = 0 for n ≥ 2.
  --   4. Inverse function route: f'(z) ≠ 0 everywhere (provably via analytic
  --      order / local normal form), but this does not imply f is linear.
  sorry
