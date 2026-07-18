

# APM a94A05: Vitali covering lemma and f(C) has measure zero when f'=0

## 1. Informal proof

**Why it's hard.** Part (a) is the Vitali covering lemma, which requires a greedy selection algorithm from an arbitrary (possibly uncountable) collection of intervals — the challenge is ensuring the selected disjoint subcollection, after inflation by factor 5, still covers the union. Part (b) uses (a) to show the image of the critical set has measure zero for an *arbitrary* function (no continuity assumed!), which is surprising.

**The key insight.** (a) Greedily pick the largest available interval, remove everything it intersects, repeat. Any interval not selected is intersected by a selected one of at least its length, so it's covered by the 5× inflation. (b) At each point x ∈ C, f'(x) = 0 means f maps small intervals around x to tiny intervals. Cover C by such small intervals, apply Vitali to extract a disjoint subcollection, and the total measure of f(C) is bounded by ε times the total length.

**Proof.**

**(a) Vitali covering lemma.** Let A be a collection of open subintervals of a bounded interval I, U = ∪A.

Greedily select: let d₁ = sup{|J| : J ∈ A}. Choose I₁ ∈ A with |I₁| > d₁/2. Having chosen I₁,...,Iₖ, let A_k = {J ∈ A : J ∩ Iⱼ = ∅ for all j ≤ k}. If A_k = ∅, stop. Otherwise let dₖ₊₁ = sup{|J| : J ∈ A_k} and choose Iₖ₊₁ ∈ A_k with |Iₖ₊₁| > dₖ₊₁/2.

The I_j are pairwise disjoint by construction. Claim: U ⊆ ∪_j I'_j.

Let x ∈ U. Then x ∈ J for some J ∈ A. If J = some I_j, done (x ∈ I_j ⊂ I'_j). If J was not selected, then at some step k, J was eliminated because J ∩ Iₖ ≠ ∅ and |Iₖ| ≥ dₖ/2 ≥ |J|/2. Since J and Iₖ intersect and |Iₖ| ≥ |J|/2, J is contained in the 5× inflation I'ₖ (the center of Iₖ is within |Iₖ|/2 + |J| ≤ |Iₖ|/2 + 2|Iₖ| = 5|Iₖ|/2 of any point in J). So x ∈ I'ₖ.

**(b) f(C) has measure zero.** Fix ε > 0. For each x ∈ C, f'(x) = 0 means: for every η > 0, there exists δ_x > 0 such that |f(y) - f(x)| < η|y-x| for |y-x| < δ_x.

Choose η = ε. For each x ∈ C, let J_x = (x - δ_x, x + δ_x). Then f(J_x ∩ I) is contained in an interval of length < 2ε · δ_x = ε · |J_x|.

The collection {J_x : x ∈ C} covers C. By part (a), extract pairwise disjoint J₁, J₂,... with C ⊆ ∪ J'ₖ.

Then f(C) ⊆ f(∪ J'ₖ) = ∪ f(J'ₖ). Each J'ₖ is concentric with Jₖ with |J'ₖ| = 5|Jₖ|, and f maps J'ₖ into an interval of length < ε · |J'ₖ| = 5ε · |Jₖ| (using f'=0 at the center with a slightly larger δ, or adjusting η).

So m*(f(C)) ≤ Σ 5ε|Jₖ| = 5ε Σ|Jₖ| ≤ 5ε|I| (since the Jₖ are disjoint in I).

Since ε was arbitrary, m*(f(C)) = 0. ∎

**What connects.** Part (a) is the classical Vitali covering lemma (the "simple" or "finite-dimensional" version with factor 5, not the measure-theoretic Vitali covering theorem). It's one of the most important tools in geometric measure theory. Part (b) is a baby version of Sard's theorem for functions of one variable: the image of the critical set has measure zero. The full Sard's theorem (for smooth maps ℝⁿ → ℝᵐ) requires much more sophisticated covering arguments and is one of the deepest results in differential topology. The factor 5 in the Vitali lemma is not optimal (3 suffices with a slightly different algorithm) but is the standard textbook constant.

## 2. Lean 4 theorem statement

```lean
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Covering.VitaliFamily
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Basic

open Set Metric MeasureTheory Filter

noncomputable section

/-- The 5× inflation of an open interval: same center, 5× length. -/
def inflate5 (a b : ℝ) : Set ℝ :=
  let c := (a + b) / 2
  let r := (b - a) / 2
  Ioo (c - 5 * r / 2) (c + 5 * r / 2)

/-- Part (a): Vitali covering lemma with factor 5.
    From any collection of open subintervals of a bounded interval,
    extract a disjoint subcollection whose 5× inflations cover the union. -/
theorem vitali_covering_lemma_5
    {I_bd : Set ℝ} (hI : Bornology.IsBounded I_bd)
    {A : Set (Set ℝ)}
    (hA_open : ∀ J ∈ A, ∃ a b, a < b ∧ J = Ioo a b)
    (hA_sub : ∀ J ∈ A, J ⊆ I_bd) :
    ∃ S : ℕ → Set ℝ,
      (∀ k, S k ∈ A ∨ S k = ∅) ∧
      (Pairwise fun i j => Disjoint (S i) (S j)) ∧
      ⋃₀ A ⊆ ⋃ k, (inflate5
        (sInf (S k)) (sSup (S k))) := by
  sorry

/-- Part (b): Image of the critical set has measure zero.
    If f'(x) = 0 for all x ∈ C, then m*(f(C)) = 0. -/
theorem measure_image_critical_set_eq_zero
    {I : Set ℝ} (hI : IsOpen I)
    {f : ℝ → ℝ}
    {C : Set ℝ} (hC : C ⊆ I)
    (hf_diff : ∀ x ∈ C, DifferentiableAt ℝ f x)
    (hf_crit : ∀ x ∈ C, deriv f x = 0) :
    volume (f '' C) = 0 := by
  sorry

/-- At a critical point, f maps small intervals to tiny intervals. -/
lemma image_small_of_deriv_zero
    {f : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hcrit : deriv f x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y, |y - x| < δ →
      |f y - f x| < ε * |y - x| := by
  sorry

/-- The disjoint subcollection has total length ≤ length of I. -/
lemma sum_lengths_le_of_disjoint_in_bounded
    {S : ℕ → Set ℝ} {I_bd : Set ℝ}
    (hI : Bornology.IsBounded I_bd)
    (hS_sub : ∀ k, S k ⊆ I_bd)
    (hS_disj : Pairwise fun i j => Disjoint (S i) (S j)) :
    ∑' k, volume (S k) ≤ volume I_bd := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `MeasureTheory.volume` — Lebesgue measure
- `MeasureTheory.OuterMeasure` — outer measure (for m*(f(C)))
- `Set.Ioo a b` — open intervals
- `DifferentiableAt ℝ f x` — differentiability
- `deriv f x` — derivative
- `Bornology.IsBounded` — bounded sets
- `Pairwise ... Disjoint` — pairwise disjointness

**Key lemmas:**
- `Vitali.exists_disjoint_subfamily_covering_enlargment` — Mathlib's Vitali covering lemma. In `Mathlib.MeasureTheory.Covering.VitaliFamily` or `Mathlib.MeasureTheory.Covering.Vitali`. This is the core of part (a)
- `hasDerivAt_iff_tendsto_slope` — f'(x) = 0 means the slope (f(y)-f(x))/(y-x) → 0
- `Metric.tendsto_nhds` — ε-δ characterisation of limit (for extracting δ from f'=0)
- `MeasureTheory.measure_iUnion_le` — σ-subadditivity: m(∪ Eₖ) ≤ Σ m(Eₖ)
- `MeasureTheory.measure_mono` — monotonicity
- `Real.volume_Ioo` — m(Ioo a b) = b - a
- `MeasureTheory.measure_image_le_of_lipschitzOnWith` — not directly, but related to bounding image measure
- `tsum_le_tsum` — comparing infinite sums
- `ENNReal.tsum_le_of_sum_le` — bounding tsum by a bound on partial sums

**Tactic hints:**
- `intro ε hε` — starting the measure-zero argument
- `choose δ hδ_pos hδ_bound using fun x hx => image_small_of_deriv_zero ...` — extracting covering intervals
- `obtain ⟨S, hS_mem, hS_disj, hS_cover⟩ := vitali_covering_lemma_5 ...` — applying Vitali
- `calc volume (f '' C) ≤ Σ volume (f '' inflate5 ...) ≤ 5ε · Σ volume (S k) ≤ 5ε · volume I` — chain
- `gcongr` — monotonicity steps
- `positivity` — for ε > 0, δ > 0
- `linarith` — arithmetic with interval lengths
- `simp [inflate5]` — unfolding the inflation definition