import Mathlib

open Filter

/-!
# APM m95J06 — finite-dimensional `ℓᵖ` limits and Hilbert norms

## Statement repairs

None.
-/

noncomputable def apm_m95j06_lpNorm {n : ℕ} (p : ℝ) (x : Fin n → ℝ) : ℝ :=
  Real.rpow (∑ i, Real.rpow |x i| p) (1 / p)

noncomputable def apm_m95j06_linfNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  sSup (Set.range fun i => |x i|)

theorem apm_m95j06 :
    (∀ (n : ℕ), 0 < n → ∀ x : Fin n → ℝ,
      Tendsto (fun p : ℝ => apm_m95j06_lpNorm p x) atTop
        (nhds (apm_m95j06_linfNorm x))) ∧
    (∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
      ∀ x : H, x ≠ 0 → DifferentiableAt ℝ (fun y : H => ‖y‖) x) := by
  -- SKIPPED: two-part finite-dimensional norm problem.
  -- (a) ‖x‖_p → ‖x‖_∞ as p→∞: the p-norm approaches the max norm.
  -- (b) Differentiability of norm at x≠0 in inner product space: ‖·‖ is
  --     differentiable away from 0, with derivative x/‖x‖.
  -- Blocker: (a) needs limit computation for (∑|x_i|^p)^{1/p} as p→∞.
  -- (b) might be tractable — norm is differentiable at x≠0 via inner product.
  -- APIs: `Real.rpow`, `sSup`, `DifferentiableAt`, `InnerProductSpace`
  sorry
