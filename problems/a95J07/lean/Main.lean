/-
! # APM a95J07: Vitali covering lemma (5×) and image of critical set has measure zero

(a) Vitali covering lemma: extract disjoint I₁, I₂, ... from A with ∪A ⊆ ∪Iₙ'.
(b) 1D Sard: f(D) has measure zero where D = {x : f'(x) = 0}.

## Proof strategy

(a) Greedy selection by decreasing length. Any unselected interval J is hit
    by a selected Iₖ with |Iₖ| ≥ |J|/2, so J ⊆ Iₖ'.
(b) f'(x) = 0 means f maps small intervals around x to tiny intervals.
    Apply (a) to extract disjoint cover, bound total image measure by 5ε.

## Theory boundaries

- Mathlib has `VitaliFamily` with `exists_disjoint_covering_ae` (abstract
  Vitali covering theorem), but the specific 5× interval formulation is not.
- The 1D Sard theorem (image of critical set has measure zero) is NOT in Mathlib.
- The disjoint total length ≤ 1 bound IS provable from measure theory basics.

## Statement repair

The generated `inflate5` used `sInf`/`sSup` to compute center and radius.
The TeX gives an explicit formula: I' = (3α - 2β, 3β - 2α) where I = (α, β).
We use the TeX formula directly.
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

open Set MeasureTheory

open scoped ENNReal

noncomputable section

/-- The 5× inflation of an open interval (α, β): I' = (3α-2β, 3β-2α).

Note: I and I' have the same center (α+β)/2, and |I'| = 5|I|. -/
def inflate5 (α β : ℝ) : Set ℝ :=
  Ioo (3 * α - 2 * β) (3 * β - 2 * α)

/-- The 5× inflation has the same center as the original interval. -/
lemma inflate5_center (α β : ℝ) (hab : α < β) :
    (3 * α - 2 * β + (3 * β - 2 * α)) / 2 = (α + β) / 2 := by ring

/-- The 5× inflation has 5× the length of the original interval. -/
lemma inflate5_length (α β : ℝ) (hab : α < β) :
    (3 * β - 2 * α) - (3 * α - 2 * β) = 5 * (β - α) := by ring

/-- Disjoint open intervals in (0,1) have total measure ≤ 1. -/
lemma tsum_volume_disjoint_le_one
    {S : ℕ → Set ℝ}
    (hS_sub : ∀ k, S k ⊆ Ioo 0 1)
    (hS_disj : Pairwise (Function.onFun Disjoint S)) :
    ∑' k, volume (S k) ≤ 1 := by
  -- Each S_k ⊆ (0,1), so volume(S_k) ≤ 1.
  -- By countable additivity of disjoint sets: Σ volume(S_k) = volume(∪S_k) ≤ volume((0,1)) = 1.
  -- This requires measurable S_k and measure_iUnion.
  sorry

/-- (a) Vitali covering lemma with factor 5.

Given a collection A of open intervals in (0,1), there exist pairwise disjoint
I₁, I₂, ... ∈ A with ∪A ⊆ ∪Iₙ'.

**Blocker:** Mathlib has `VitaliFamily` with abstract covering theorems but
not the specific 5× formulation for 1D intervals. The greedy selection
algorithm needs to be formalized from scratch. -/
theorem vitali_covering_5
    {A : Set (Set ℝ)}
    (hA : ∀ I ∈ A, ∃ a b, a < b ∧ I = Ioo a b)
    (hA_sub : ∀ I ∈ A, I ⊆ Ioo 0 1) :
    ∃ S : ℕ → Set ℝ,
      (∀ k, S k ∈ A ∨ S k = ∅) ∧
      Pairwise (Function.onFun Disjoint S) ∧
      ⋃₀ A ⊆ ⋃ k, {y : ℝ | ∃ a b, S k = Ioo a b ∧ y ∈ inflate5 a b} := by
  sorry

/-- The critical set: points where f is differentiable with f' = 0. -/
def criticalSet (f : ℝ → ℝ) : Set ℝ :=
  {x ∈ Ioo 0 1 | DifferentiableAt ℝ f x ∧ deriv f x = 0}

/-- (b) The image of the critical set has measure zero.

**Blocker:** Requires the Vitali covering lemma (part a) plus the fact
that f'(x) = 0 means f maps small intervals to tiny intervals.
The 1D Sard theorem is NOT in Mathlib. -/
theorem measure_image_criticalSet_eq_zero
    {f : ℝ → ℝ} :
    volume (f '' criticalSet f) = 0 := by
  sorry

end
