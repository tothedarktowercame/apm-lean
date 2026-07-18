import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# APM a93A04: AC functions are exactly BV-limits of Lipschitz functions

**Problem.** f : [0,1] → ℝ is absolutely continuous iff there exist Lipschitz
functions fₙ on [0,1] with V(fₙ - f) → 0, where V is total variation.

## Proof strategy

**(⟸)** Lipschitz ⟹ AC (Mathlib: `LipschitzOnWith.absolutelyContinuousOnInterval`).
If fₙ are AC and V(fₙ - f) → 0, then f is AC (ε-δ argument using the variation
bound).

**(⟹)** If f is AC, then f(x) = f(0) + ∫₀ˣ f'(t) dt with f' ∈ L¹. Truncate:
gₙ = clamp(f', -n, n), fₙ = f(0) + ∫₀ˣ gₙ. Then fₙ is Lipschitz (|gₙ| ≤ n)
and V(fₙ - f) = ∫|gₙ - f'| → 0 by DCT.

## Statement repair note

The informal proof defines `totalVariation` from scratch. Mathlib already has
`eVariationOn` (extended-real-valued variation on a set). We use Mathlib's
`AbsolutelyContinuousOnInterval` for AC and `LipschitzOnWith` for Lipschitz.
The problem reduces to showing the AC functions are the closure of Lipschitz
functions in the `eVariationOn` norm.
-/

set_option linter.unusedVariables false in
noncomputable section

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace ApmCanaries.A93A04

/-- Lipschitz on [0,1]. -/
def LipschitzOn01 (f : ℝ → ℝ) : Prop :=
  ∃ K : ℝ≥0, LipschitzOnWith K f (uIcc (0:ℝ) 1)

/-- Total variation of f on [0,1] as a real number. -/
noncomputable def totalVariation (f : ℝ → ℝ) : ENNReal :=
  eVariationOn f (uIcc (0:ℝ) 1)

/-- Lipschitz ⟹ AC on [0,1].

    Zero-sorry: follows from `LipschitzOnWith.absolutelyContinuousOnInterval`. -/
theorem lipschitz_implies_ac {f : ℝ → ℝ} (h : LipschitzOn01 f) :
    AbsolutelyContinuousOnInterval f 0 1 := by
  obtain ⟨K, hK⟩ := h
  exact hK.absolutelyContinuousOnInterval

/-- **(⟸) Reverse direction:** If fₙ are Lipschitz and V(fₙ - f) → 0,
    then f is AC.

    **SORRY BOUNDARY:** The proof uses: each fₙ is AC (from Lipschitz),
    and V-convergence preserves AC. The ε-δ argument:
    for disjoint intervals with Σ(bᵢ-aᵢ) < δ:
    Σ|f(bᵢ)-f(aᵢ)| ≤ Σ|(f-fₙ)(bᵢ)-(f-fₙ)(aᵢ)| + Σ|fₙ(bᵢ)-fₙ(aᵢ)|
                     ≤ V(f-fₙ) + ε/2 < ε.
    Formalizing this requires connecting `eVariationOn` to the sum of absolute
    differences on disjoint intervals, plus the ε-δ characterization of AC
    from `absolutelyContinuousOnInterval_iff`. -/
theorem lipschitz_V_limit_implies_ac
    {f : ℝ → ℝ} {fₙ : ℕ → ℝ → ℝ}
    (hlip : ∀ n, LipschitzOn01 (fₙ n))
    (hconv : Tendsto (fun n => totalVariation (fun x => fₙ n x - f x)) atTop (𝓝 0)) :
    AbsolutelyContinuousOnInterval f 0 1 := by
  sorry

/-- **(⟹) Forward direction:** If f is AC, there exist Lipschitz fₙ with
    V(fₙ - f) → 0.

    **SORRY BOUNDARY:** The proof constructs fₙ(x) = f(0) + ∫₀ˣ gₙ(t) dt
    where gₙ = clamp(f', -n, n). Key steps:
    (1) f is AC ⟹ f' exists a.e. and is integrable (FTC for AC functions)
    (2) gₙ is bounded ⟹ fₙ is Lipschitz (|∫ₓʸ gₙ| ≤ n|x-y|)
    (3) V(fₙ-f) = ∫|gₙ-f'| → 0 by DCT (|gₙ-f'| ≤ 2|f'|, gₙ → f' a.e.)
    Each step uses deep Mathlib API: `ae_differentiableAt` for (1),
    `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral` for (2),
    and `tendsto_integral_of_dominated_convergence` for (3).
    The identity V(fₙ-f) = ∫|gₙ-f'| for AC functions requires
    `eVariationOn_sub_eq_integral_norm_deriv` or similar. -/
theorem ac_implies_lipschitz_V_approx
    {f : ℝ → ℝ} (hac : AbsolutelyContinuousOnInterval f 0 1) :
    ∃ fₙ : ℕ → ℝ → ℝ,
      (∀ n, LipschitzOn01 (fₙ n)) ∧
      Tendsto (fun n => totalVariation (fun x => fₙ n x - f x)) atTop (𝓝 0) := by
  sorry

/-- **Main theorem:** f is AC on [0,1] iff f is a V-limit of Lipschitz functions. -/
theorem ac_iff_lipschitz_V_approx (f : ℝ → ℝ) :
    AbsolutelyContinuousOnInterval f 0 1 ↔
    ∃ fₙ : ℕ → ℝ → ℝ,
      (∀ n, LipschitzOn01 (fₙ n)) ∧
      Tendsto (fun n => totalVariation (fun x => fₙ n x - f x)) atTop (𝓝 0) := by
  refine ⟨ac_implies_lipschitz_V_approx, ?_⟩
  rintro ⟨fₙ, hlip, hconv⟩
  exact lipschitz_V_limit_implies_ac hlip hconv

end ApmCanaries.A93A04
