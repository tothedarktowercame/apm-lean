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

/-- In a real inner-product space, the norm is differentiable away from the
origin. This is the identity-map specialization of Mathlib's chain rule for
the Hilbert norm. -/
lemma apm_m95J06_differentiableAt_norm
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : H) (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun y : H => ‖y‖) x := by
  exact differentiableAt_id.norm ℝ hx

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
  -- APIs: `Real.rpow`, `sSup`, `DifferentiableAt`, `InnerProductSpace`.
  --
  -- Closer hop 1 closes the second conjunct independently as
  -- `apm_m95J06_differentiableAt_norm`, by specializing Mathlib's
  -- `DifferentiableAt.norm` to the identity map.
  --
  -- For the first conjunct, proved sibling `a93J04` contains the general
  -- finite-measure theorem `tendsto_eLpNorm_atTop`, while `bpm-1-3-1` contains
  -- a direct finite power-mean squeeze for natural exponents. Neither is
  -- importable here in the exact custom encoding: one must identify the
  -- counting-measure `eLpNorm` with this real-exponent finite sum, identify its
  -- essential supremum with the `sSup` of the finite range, and transport the
  -- ENNReal exponent limit back to real `p → atTop`. Searches of
  -- `LEMMA-INDEX.md`, Mathlib, `ConstructionTargets/`, other siblings, and git
  -- history found no compiled bridge performing those conversions. The frozen
  -- statement is unchanged.
  sorry
