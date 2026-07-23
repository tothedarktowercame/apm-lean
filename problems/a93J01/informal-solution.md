

# APM a93J01: Continuity + BV + AC on [a,1] for all a > 0 implies AC on [0,1]

## 1. Informal proof

**Why it's hard.** Absolute continuity on every [a,1] does not automatically extend to [0,1] — the AC constant δ could degenerate as a → 0. The additional hypotheses of continuity at 0 and bounded variation on [0,1] are both needed to control what happens near the endpoint, and it's not immediately obvious how they combine.

**The key insight.** Bounded variation means the total variation V(f, [0, a]) → 0 as a → 0⁺ (since V(f, [0,1]) = V(f, [0,a]) + V(f, [a,1]) and V(f, [0,1]) < ∞). So any collection of disjoint intervals with small total length can be split: those near 0 contribute at most V(f, [0, a]) (which is small), and those in [a,1] are handled by the AC property on [a,1].

**Proof.**

Fix ε > 0. We need δ > 0 such that for any finite collection of disjoint intervals (aᵢ, bᵢ) ⊂ [0,1] with Σ(bᵢ - aᵢ) < δ, we have Σ|f(bᵢ) - f(aᵢ)| < ε.

*Step 1: Control the variation near 0.* Since f has bounded variation on [0,1], V(f, [0,1]) < ∞. The function a ↦ V(f, [0,a]) is monotone increasing with V(f, [0,0]) = 0 and is right-continuous (from the definition of variation). So there exists a₀ > 0 with V(f, [0, a₀]) < ε/2.

*Step 2: Use AC on [a₀, 1].* Since f is AC on [a₀, 1], there exists δ > 0 such that for any disjoint intervals (aᵢ, bᵢ) ⊂ [a₀, 1] with Σ(bᵢ - aᵢ) < δ, Σ|f(bᵢ) - f(aᵢ)| < ε/2. We may assume δ < a₀.

*Step 3: Combine.* Take any disjoint intervals (aᵢ, bᵢ) ⊂ [0,1] with Σ(bᵢ - aᵢ) < δ. Split them into two groups:

- Group A: intervals with aᵢ < a₀ (those touching [0, a₀)).
- Group B: intervals with aᵢ ≥ a₀ (entirely within [a₀, 1]).

For Group B: all intervals are in [a₀, 1] and Σ_B(bᵢ - aᵢ) < δ, so Σ_B |f(bᵢ) - f(aᵢ)| < ε/2 by AC on [a₀, 1].

For Group A: since δ < a₀, any interval (aᵢ, bᵢ) with aᵢ < a₀ satisfies bᵢ < aᵢ + δ < a₀ + a₀ = 2a₀... hmm, this doesn't directly force bᵢ ≤ a₀.

Better: the intervals in Group A are all contained in [0, 1] and some may extend past a₀. But the sum Σ_A |f(bᵢ) - f(aᵢ)| can be bounded by the total variation of f on the union of these intervals, which is at most V(f, [0, c]) where c = max{bᵢ : interval in Group A}.

Actually, since the intervals are disjoint and all have aᵢ < a₀, and Σ(bᵢ - aᵢ) < δ < a₀, the interval farthest right has bᵢ < a₀ + δ < 2a₀. But we need a cleaner bound.

Cleanest approach: redefine the split. For any collection of disjoint intervals in [0,1], those that intersect [0, a₀] have their total oscillation bounded by V(f, [0, max bᵢ]). Since all of them start before a₀ and their total length is < δ < a₀, max bᵢ ≤ a₀ + Σ(bᵢ - aᵢ) < 2a₀ (crude bound). Choose a₀ so that V(f, [0, 2a₀]) < ε/2 (possible since V(f, [0,t]) → 0).

So: Σ_A |f(bᵢ) - f(aᵢ)| ≤ V(f, [0, 2a₀]) < ε/2.

Total: Σ|f(bᵢ) - f(aᵢ)| ≤ Σ_A + Σ_B < ε/2 + ε/2 = ε. ✓ ∎

**What connects.** This result shows that absolute continuity, unlike mere continuity, is determined by local behaviour on (0,1] plus global regularity (BV + continuity at 0). The BV condition prevents the variation from "piling up" at the endpoint — without it, a continuous function could oscillate infinitely near 0 in a way that is AC on every [a,1] but not on [0,1]. The standard counterexample without BV is f(x) = x sin(1/x) (continuous, AC on [a,1] for all a > 0, but not BV hence not AC on [0,1]). The same result holds at both endpoints and generalises to functions that are AC on every compact subinterval of an open interval.

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.BoundedVariation
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Topology.ContinuousOn

open Set MeasureTheory

noncomputable section

/-- Absolute continuity on an interval [a,b]. -/
def AbsolutelyContinuousOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (n : ℕ) (a b : Fin n → ℝ),
    (∀ i, a i ∈ s) → (∀ i, b i ∈ s) →
    (∀ i, a i ≤ b i) →
    (∀ i j, i < j → b i ≤ a j) →
    ∑ i, (b i - a i) < δ →
    ∑ i, |f (b i) - f (a i)| < ε

/-- The total variation on [0, a] tends to 0 as a → 0⁺
    for a BV function. -/
lemma eVariationOn_Icc_tendsto_zero
    {f : ℝ → ℝ} (hBV : HasBoundedVariationOn f (Icc 0 1)) :
    Tendsto (fun a => eVariationOn f (Icc 0 a)) (𝓝[>] 0) (𝓝 0) := by
  sorry

/-- Main theorem: continuous + BV on [0,1] + AC on [a,1] for all a > 0
    implies AC on [0,1]. -/
theorem ac_on_01_of_continuous_bv_ac_from_a
    {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Icc 0 1))
    (hBV : HasBoundedVariationOn f (Icc 0 1))
    (hAC : ∀ a : ℝ, 0 < a → a < 1 → AbsolutelyContinuousOn f (Icc a 1)) :
    AbsolutelyContinuousOn f (Icc 0 1) := by
  sorry

/-- Helper: the sum of oscillations over intervals in [0,c] is bounded
    by the total variation on [0,c]. -/
lemma sum_abs_le_eVariationOn
    {f : ℝ → ℝ} {n : ℕ} {a b : Fin n → ℝ}
    {c : ℝ} (hc : 0 ≤ c)
    (ha : ∀ i, a i ∈ Icc 0 c)
    (hb : ∀ i, b i ∈ Icc 0 c)
    (hab : ∀ i, a i ≤ b i)
    (hdisj : ∀ i j, i < j → b i ≤ a j) :
    (∑ i, |f (b i) - f (a i)| : ℝ) ≤
      (eVariationOn f (Icc 0 c)).toReal := by
  sorry

/-- Splitting lemma: disjoint intervals in [0,1] can be partitioned
    into those with left endpoint < a and those with left endpoint ≥ a. -/
lemma intervals_split
    {n : ℕ} {a_i b_i : Fin n → ℝ} {a₀ : ℝ}
    (ha0 : 0 < a₀) :
    ∃ (A B : Finset (Fin n)),
      A ∪ B = Finset.univ ∧ Disjoint A B ∧
      (∀ i ∈ A, a_i i < a₀) ∧
      (∀ i ∈ B, a₀ ≤ a_i i) := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `HasBoundedVariationOn f s` — bounded variation on a set (in `Mathlib.Analysis.BoundedVariation`)
- `eVariationOn f s` — total variation as an ℝ≥0∞ value
- `ContinuousOn f (Icc 0 1)` — continuity on [0,1]
- `Set.Icc a b` — closed interval
- `Filter.𝓝[>] 0` — right-neighbourhood filter of 0

**Key lemmas:**
- `eVariationOn.add` / `eVariationOn_Icc_le_add` — additivity of variation: V([0,1]) = V([0,a]) + V([a,1]) (or inequality version)
- `eVariationOn.mono` — variation is monotone in the set: S ⊆ T ⟹ V(f, S) ≤ V(f, T)
- `eVariationOn_Icc_le` — bounding sums of oscillations by variation
- `HasBoundedVariationOn.eVariationOn_ne_top` — BV means V < ∞
- `ENNReal.tendsto_nhds_zero` — convergence to 0 in ℝ≥0∞
- `ENNReal.toReal_mono` — monotonicity of toReal
- `ContinuousOn.comp` — not directly used but continuity is needed
- `Finset.sum_le_sum` — bounding sums termwise
- `Finset.filter` / `Finset.sum_filter_add_sum_filter_not` — splitting a sum by a predicate

**Tactic hints:**
- `intro ε hε` — starting the AC proof
- `obtain ⟨a₀, ha₀_pos, ha₀_var⟩ := ...` — finding a₀ with small variation near 0
- `obtain ⟨δ, hδ_pos, hδ_ac⟩ := hAC a₀ ha₀_pos ... ε/2 ...` — getting δ from AC on [a₀, 1]
- `refine ⟨min δ a₀, by positivity, ?_⟩` — choosing δ = min(δ_AC, a₀)
- `calc Σ |f(bᵢ)-f(aᵢ)| = Σ_A + Σ_B ≤ ε/2 + ε/2` — the splitting argument
- `gcongr` — for variation monotonicity bounds
- `linarith` — combining the ε/2 bounds
- `simp [Finset.sum_filter_add_sum_filter_not]` — splitting the finite sum
- `exact?` — finding the variation additivity lemma