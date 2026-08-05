/-
! # APM a97J04: Continuous BV + locally AC ⟹ AC on [0,1]

Let f: [0,1] → ℝ be continuous, of bounded variation, and absolutely continuous
on [δ,1] for every δ > 0. Prove f is absolutely continuous on [0,1].

## Note

The informal solution says this is "essentially the same problem as a93J01."

## Strategy (from informal-solution.md)

Two routes:
- **Direct**: Use variation function V(x) → 0 as x → 0 (Lemma 1), then split
  test intervals at a₀: those in [0,a₀] bounded by V(a₀), those in [a₀,1] by AC.
- **FTC route**: BV gives f' ∈ L¹, AC on [δ,1] gives f(x)-f(δ) = ∫f', continuity
  sends δ→0, and the indefinite integral is AC.

## Phase-A hints used
-- (Memory: e-codexpilot-extend-local-absolute-continuity-to-an-endpoint-via-the-derivative-primitive)
--    Prior attempt at same problem via FTC route.
-- (Memory: e-codexpilot-order-a-disjoint-interval-family-into-a-variation-partition)
--    API guidance for ordering intervals into variation partitions.

## Boundary

Mathlib does NOT have a built-in definition of "absolutely continuous function on
an interval." We define `AbsContOn` ourselves.

APIs searched:
- `eVariationOn`, `BoundedVariationOn` — FOUND: in `Topology/EMetricSpace/BoundedVariation.lean`
- `AbsoluteContinuous` — NOT FOUND for functions (only exists for measures)
- `integral_eq_sub_of_hasDerivAt` — FOUND: FTC in interval integral form
- `BoundedVariationOn.ae_differentiableAt_of_mem_uIcc` — FOUND: BV ⟹ a.e. differentiable
-/

import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.BoundedVariation

open MeasureTheory Filter Set Topology BigOperators
open scoped ENNReal

noncomputable section

namespace APMa97J04

/-- A function f is absolutely continuous on [a,b] if for every ε > 0 there exists
    δ > 0 such that for every finite sequence of pairwise-disjoint open intervals
    contained in [a,b] with total length < δ, the total oscillation of f is < ε.

    We use the standard partition formulation: a sorted sequence of points
    a ≤ t₀ ≤ t₁ ≤ ... ≤ tₙ ≤ b with Σ(t₂ᵢ₊₁ - t₂ᵢ) < δ gives Σ|f(t₂ᵢ₊₁)-f(t₂ᵢ)| < ε. -/
def AbsContOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ (s : List (ℝ × ℝ)),
      (∀ (i : ℕ) (hi : i < s.length),
        a ≤ (s.get ⟨i, hi⟩).1 ∧ (s.get ⟨i, hi⟩).2 ≤ b ∧
        (s.get ⟨i, hi⟩).1 ≤ (s.get ⟨i, hi⟩).2) →
      (∀ (i : ℕ) (hi : i + 1 < s.length),
        (s.get ⟨i, Nat.lt_of_succ_lt hi⟩).2 ≤ (s.get ⟨i + 1, hi⟩).1) →
      (s.map (fun p => p.2 - p.1)).sum < δ →
      (s.map (fun p => |f p.2 - f p.1|)).sum < ε

/-- Main theorem: continuous + BV + AC on every [δ,1] ⟹ AC on [0,1].

    -- (Memory: e-codexpilot-extend-local-absolute-continuity-to-an-endpoint-via-the-derivative-primitive)
    --    Prior attempt via FTC route: BV gives f'∈L¹, AC on [δ,1] gives FTC, continuity sends δ→0.
    -- (Memory: e-codexpilot-order-a-disjoint-interval-family-into-a-variation-partition)
    --    Ordering disjoint intervals into variation partitions for the oscillation bound. -/
theorem continuous_bv_locally_ac_implies_ac
    (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Icc 0 1))
    (hf_bv : BoundedVariationOn f (Icc 0 1))
    (hf_ac : ∀ δ : ℝ, 0 < δ → δ < 1 → AbsContOn f δ 1) :
    AbsContOn f 0 1 := by
  sorry

#print axioms APMa97J04.continuous_bv_locally_ac_implies_ac

end APMa97J04
