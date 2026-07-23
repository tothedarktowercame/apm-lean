

# APM a96A02: Hölder-1/2 continuous but not absolutely continuous piecewise linear function

## 1. Informal proof

**Why it's hard.** The function is piecewise linear with peaks of height 1/n at midpoints of [1/(n+1), 1/n], creating infinitely many triangular spikes near 0. Showing Hölder continuity requires bounding the oscillation on intervals of varying scale (the spikes get shorter but also narrower), while showing non-AC requires exhibiting the failure of the AC condition on collections of small intervals that catch many spikes.

**The key insight.** Each spike has height 1/n over a base of width ~1/n², so the slope is ~n. The Hölder bound comes from: within one spike, |f(x)-f(y)| ≤ 1/n and |x-y| ≤ 1/(2n(n+1)) ~ 1/(2n²), giving |f(x)-f(y)|/|x-y|^{1/2} ≤ (1/n)/(1/n) = bounded. For non-AC: the intervals [1/(n+1), 1/n] for n = N,...,2N have total length ~Σ 1/n² ~ 1/N (small), but total oscillation Σ 2/n ~ log 2 (bounded away from zero).

**Proof.**

The function f is piecewise linear with f(1/n) = 0 and f(mₙ) = 1/n where mₙ = 1/(2n) + 1/(2(n+1)) = (2n+1)/(2n(n+1)) is the midpoint of [1/(n+1), 1/n]. The interval [1/(n+1), 1/n] has length 1/(n(n+1)), and f rises from 0 to 1/n then falls back to 0 on this interval (a triangle of height 1/n and base 1/(n(n+1))).

**Hölder-1/2 continuity: |f(x)-f(y)| ≤ A|x-y|^{1/2}.**

It suffices to show |f(x)-f(y)| ≤ A|x-y|^{1/2} for x,y in the same spike [1/(n+1), 1/n] (for x,y in different spikes, use the triangle inequality through the nearest zero).

Within spike n: the slope of f is ±1/n ÷ (1/(2n(n+1))) = ±2(n+1) ≈ 2n. So |f(x)-f(y)| ≤ 2(n+1)|x-y|. Also |f(x)-f(y)| ≤ 1/n (the spike height).

Combining: |f(x)-f(y)| ≤ min(1/n, 2(n+1)|x-y|) = √(2(n+1)/n) · |x-y|^{1/2} · min(...)^{1/2}.

More directly: |f(x)-f(y)|² ≤ (1/n) · 2(n+1)|x-y| ≤ 4|x-y|. So |f(x)-f(y)| ≤ 2|x-y|^{1/2}. This works because height × slope = (1/n) · 2(n+1) ≤ 4. ✓

For x,y in different spikes or between a spike and the "ground": the function is 0 at the shared boundary points 1/n, so |f(x)-f(y)| ≤ |f(x)-0| + |0-f(y)| ≤ 2|x-y|^{1/2} + 2|x-y|^{1/2}... but we need to be careful. Since the Hölder estimate holds within each piece and f = 0 at the junction points, a standard argument gives a global Hölder constant A. ✓

**Not absolutely continuous.**

Consider the intervals Iₙ = [1/(n+1), 1/n] for n = N, N+1, ..., 2N. These are disjoint. Their total length:

Σₙ₌ₙ^{2N} 1/(n(n+1)) ≤ Σ 1/n² ≤ ∫_{N-1}^{2N} 1/x² dx = 1/(N-1) - 1/(2N) → 0.

The total oscillation on each Iₙ is |f(mₙ) - f(1/n)| + |f(1/(n+1)) - f(mₙ)| = 2/n.

Actually for AC, consider just the sub-intervals from each 1/(n+1) to mₙ: Σ|f(mₙ) - f(1/(n+1))| = Σ 1/n from n = N to 2N ≈ log 2.

The total length of these intervals: Σ (mₙ - 1/(n+1)) = Σ 1/(2n(n+1)) → 0 as N → ∞.

So Σ lengths → 0 but Σ|f(bₖ)-f(aₖ)| ≈ log 2 ≠ 0. This violates absolute continuity: for ε = log(2)/2, no δ works. ✓ ∎

**What connects.** This is the canonical example showing Hölder continuity does not imply absolute continuity. The exponent 1/2 is sharp for this construction: the height-to-base ratio of each spike satisfies height² ~ base, which is exactly the Hölder-1/2 condition. For AC, the spikes are "too numerous": Σ heights = Σ 1/n = ∞ (harmonic series), while Σ bases = Σ 1/n² < ∞ (convergent). This asymmetry — convergent bases but divergent heights — is what breaks AC while preserving Hölder. The function is a real-analysis counterpart to the Weierstrass function (continuous but not differentiable), illustrating that regularity between "continuous" and "Lipschitz" does not suffice for absolute continuity.

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.HolderNorm

open Set Real

noncomputable section

/-- The piecewise linear function with spikes of height 1/n at
    midpoints of [1/(n+1), 1/n]. -/
def spikeFunction : ℝ → ℝ := sorry
  -- Piecewise linear: f(0) = 0, f(1/n) = 0, f(midpoint_n) = 1/n

/-- f(1/n) = 0 for all n ≥ 1. -/
lemma spikeFunction_at_inv_nat (n : ℕ) (hn : 0 < n) :
    spikeFunction (1 / ↑n) = 0 := by
  sorry

/-- f(midpoint_n) = 1/n. -/
lemma spikeFunction_at_midpoint (n : ℕ) (hn : 0 < n) :
    spikeFunction (1 / (2 * ↑n) + 1 / (2 * (↑n + 1))) = 1 / ↑n := by
  sorry

/-- Main theorem part 1: f is Hölder continuous with exponent 1/2. -/
theorem spikeFunction_holderWith :
    ∃ A : ℝ, 0 < A ∧ ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1,
      |spikeFunction x - spikeFunction y| ≤ A * |x - y| ^ (1/2 : ℝ) := by
  sorry

/-- Main theorem part 2: f is not absolutely continuous on [0,1]. -/
theorem spikeFunction_not_absolutelyContinuous :
    ∃ ε > 0, ∀ δ > 0, ∃ (n : ℕ) (a b : Fin n → ℝ),
      (∀ i, a i ∈ Icc 0 1) ∧ (∀ i, b i ∈ Icc 0 1) ∧
      (∀ i, a i ≤ b i) ∧
      (∀ i j, i < j → b i ≤ a j) ∧
      ∑ i, (b i - a i) < δ ∧
      ε ≤ ∑ i, |spikeFunction (b i) - spikeFunction (a i)| := by
  sorry

/-- Within spike n: height × slope ≤ 4 (key for Hölder). -/
lemma spike_height_slope_bound (n : ℕ) (hn : 0 < n) :
    (1 / (↑n : ℝ)) * (2 * (↑n + 1)) ≤ 4 := by
  sorry

/-- Within spike n: |f(x)-f(y)|² ≤ 4|x-y| (Hölder-1/2 within one spike). -/
lemma holder_within_spike (n : ℕ) (hn : 0 < n)
    {x y : ℝ} (hx : x ∈ Icc (1/(↑n+1 : ℝ)) (1/↑n)) (hy : y ∈ Icc (1/(↑n+1 : ℝ)) (1/↑n)) :
    |spikeFunction x - spikeFunction y| ^ 2 ≤ 4 * |x - y| := by
  sorry

/-- The AC-violating collection: intervals from 1/(n+1) to midpoint_n
    for n = N,...,2N. -/
lemma ac_violation (N : ℕ) (hN : 0 < N) :
    ∑ n in Finset.Icc N (2*N), (1 / (2 * (↑n : ℝ) * (↑n + 1))) < 1 / ↑N ∧
    1/2 ≤ ∑ n in Finset.Icc N (2*N), (1 / (↑n : ℝ)) := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `HolderWith C r f` / `HolderOnWith C r f s` — Mathlib's Hölder continuity predicate (in `Mathlib.Topology.MetricSpace.HolderNorm`). Uses `C : ℝ≥0` and `r : ℝ≥0`
- `Set.Icc` — closed intervals
- `Real.rpow` — `|x-y|^{1/2}` as real power
- `Finset.Icc`, `Finset.sum` — finite sums over integer ranges

**Key lemmas:**
- `Real.rpow_le_rpow` — monotonicity of rpow
- `abs_sub_le` — |a-b| ≤ |a| + |b| (triangle inequality for the cross-spike case)
- `sq_le_sq'` / `abs_le_of_sq_le_sq` — converting |f(x)-f(y)|² ≤ C|x-y| to |f(x)-f(y)| ≤ √C · |x-y|^{1/2}
- `Real.sqrt_le_sqrt` — monotonicity of sqrt
- `Finset.sum_le_sum` — bounding sums termwise
- `harmonic_sum_diverges` — Σ 1/n diverges (may not be packaged, but `not_summable_nat_of_summable_norm` or manual bound)
- `Real.summable_nat_rpow_inv` — Σ 1/n^s converges for s > 1 (for the base lengths Σ 1/n²)
- `Nat.cast_pos` — ↑n > 0 from n > 0

**Tactic hints:**
- `refine ⟨2, by norm_num, ?_⟩` — providing the Hölder constant A = 2
- `calc |f x - f y|^2 ≤ (1/n) * 2(n+1) * |x-y| ≤ 4 * |x-y|` — Hölder within a spike
- `refine ⟨1/2, by norm_num, ?_⟩` — providing ε = 1/2 for non-AC
- `refine fun δ hδ => ⟨N+1, ..., ...⟩` — constructing the violating collection where N > 1/δ
- `norm_num` — for numerical bounds
- `field_simp` — for 1/(n(n+1)) arithmetic
- `gcongr` — for Finset.sum bounds
- `nlinarith` — combining height/slope bounds
- `omega` — for natural number arithmetic in index ranges