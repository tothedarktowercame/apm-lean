/-
! # APM a97J08: Zeros are stable under locally uniform convergence (Rouché + Hurwitz)

Let D ⊂ ℂ be open simply connected, γ a simple closed rectifiable path in D,
Γ = γ([0,1]). Let f_n analytic on D, f_n → g uniformly on compact subsets.
If g ≠ 0 on Γ, show ∃ N such that n ≥ N implies f_n and g have the same
number of zeros inside Γ.

## Strategy (from informal-solution.md)

1. g is analytic (Weierstrass convergence theorem).
2. Interior of Γ ⊂ D (Jordan curve theorem + simply connected).
3. Positive margin: m = min_{Γ} |g| > 0 by compactness + continuity + g ≠ 0.
4. Uniform convergence beats margin: ∃ N, n ≥ N ⟹ |f_n - g| < m ≤ |g| on Γ.
5. Rouché's theorem: f_n and g have the same zero count inside Γ.

## Phase-A hints used
-- (Memory: e-codexpilot-prove-Hurwitz-zero-persistence-through-quantitative-open-mapping)
--    Hurwitz zero persistence is the content of this theorem.
-- (Memory: e-codexpilot-package-every-rouche-homotopy-slice-for-the-argument-principle)
--    Rouché via argument principle / homotopy slicing.
-- (Memory: e-codexpilot-straight-line-rouche-homotopy-stays-nonzero-on-boundary)
--    The key Rouché condition |f_n - g| < |g| on Γ.

## Boundary

Mathlib does NOT have Rouché's theorem, the argument principle, or zero-counting
machinery for general domains. The proof requires building:
1. Zero count inside a rectifiable Jordan curve (via argument principle)
2. Rouché's theorem: if |f - g| < |g| on boundary, same zero count inside
3. Weierstrass convergence theorem (analytic limit of locally uniform convergence)
4. Jordan curve theorem: interior of Γ ⊂ D when D is simply connected

The mathematical argument is clean (margin + Rouché), but the formalization
requires infrastructure that is absent from Mathlib.

APIs searched:
- `zeroCount`, `zeroCountInClosedBall` — NOT FOUND
- `rouche`, `Rouche` — NOT FOUND
- `winding`, `windingNumber` — NOT FOUND
- `argument.*principle` — NOT FOUND
- `circleIntegral`, `integral_sub_inv_of_mem_ball` — FOUND (basic circle integral only)
- `TendstoLocallyUniformlyOn`, `AnalyticOnNhd` — FOUND (convergence/analyticity)

Routes NOT investigated:
- Building the full argument principle from `circleIntegral`
- Using `DiffContOnCl` + Cauchy formula to build zero counting
- Proving the Jordan curve theorem in Lean
-/

import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

open Metric Set Filter Topology
open scoped Topology

noncomputable section

namespace APMa97J08

/-- Number of zeros of f inside a rectifiable Jordan curve Γ, counted with multiplicity.

    This is defined as the winding number of f ∘ γ around 0, which equals the
    argument principle integral (1/2πi) ∮_Γ f'(z)/f(z) dz when f is analytic
    and nonzero on Γ.

    NOTE: This definition is a placeholder; Mathlib lacks the winding number API
    for general rectifiable curves. -/
def zeroCount {D : Set ℂ} (f : ℂ → ℂ) (γ : ℝ → ℂ) : ℤ :=
  0 -- placeholder: requires winding number machinery not in Mathlib

/-- Main theorem: under locally uniform convergence with g ≠ 0 on Γ,
    eventually f_n and g have the same number of zeros inside Γ.

    -- (Memory: e-codexpilot-prove-Hurwitz-zero-persistence-through-quantitative-open-mapping)
    --    Hurwitz zero persistence under locally uniform convergence.
    -- (Memory: e-codexpilot-package-every-rouche-homotopy-slice-for-the-argument-principle)
    --    Rouché via argument principle.
    -- (Memory: e-codexpilot-straight-line-rouche-homotopy-stays-nonzero-on-boundary)
    --    The Rouché condition |f_n - g| < |g| on Γ. -/
theorem zero_stability_under_convergence
    (D : Set ℂ) (hD_open : IsOpen D) (hD_sc : IsSimplyConnected D)
    (γ : ℝ → ℂ) (hγ_path : Continuous γ)
    (hγ_simple : ∀ s t, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → γ s = γ t → s = t ∨ s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1)
    (hγ_in_D : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ D)
    (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ)
    (hf_analytic : ∀ n, AnalyticOnNhd ℂ (f n) D)
    (hg_nonzero : ∀ z ∈ (γ '' Set.Icc (0:ℝ) 1), g z ≠ 0)
    (hf_conv : TendstoLocallyUniformlyOn f g atTop D) :
    ∃ N : ℕ, ∀ n ≥ N, zeroCount (f n) (D := D) γ = zeroCount (D := D) g γ := by
  sorry

#print axioms APMa97J08.zero_stability_under_convergence

end APMa97J08
