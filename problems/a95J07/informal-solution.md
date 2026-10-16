# APM a95J07: Vitali covering lemma ($5\times$) and image of critical set has measure zero

This is essentially the same as a94A05. I'll give the statements with the specific formulation used here.

## 1. Informal proof

**Why it's hard.** Part (a) requires extracting a disjoint subcollection from an arbitrary (possibly uncountable) collection of intervals such that the $5\times$ inflations still cover the union — a greedy algorithm with a careful domination argument. Part (b) applies (a) to show $f(D)$ has measure zero for an *arbitrary* function $f$, which is surprising since no regularity of $f$ is assumed beyond differentiability at points of $D$.

**The key insight.** (a) Greedily select intervals by decreasing length; any unselected interval is intersected by a selected one of at least half its length, placing it inside the $5\times$ inflation. (b) At each $x \in D$, $f'(x) = 0$ means $f$ maps a small interval around $x$ to a tiny interval; cover $D$ with such intervals, apply (a) to extract a disjoint subcollection, and the total image measure is bounded by $\varepsilon$ times the total length.

**Proof.**

**(a) Vitali covering lemma.** Order intervals by length. Let $d_{1} = \sup\{|I| : I \in A\}$. Pick $I_{1} \in A$ with $|I_{1}| > d_{1}/2$. Remove all intervals meeting $I_{1}$. Let $d_{2} =$ sup of remaining lengths, pick $I_{2}$ with $|I_{2}| > d_{2}/2$. Continue inductively.

The $I_{k}$ are pairwise disjoint by construction. If the process terminates ($d_{k} = 0$ or $A$ is exhausted), done. Otherwise, $\sum|I_{k}| \leq 1$ (disjoint in $(0,1)$), so $|I_{k}| \to 0$.

Claim: $\cup A \subseteq \cup I_{k}'$. Let $x \in J$ for some $J \in A$. If $J = I_{k}$ for some $k$, done. Otherwise $J$ was excluded at some step $k$ because $J \cap I_{k} \neq \emptyset$ and $|I_{k}| \geq d_{k}/2 \geq |J|/2$. Since $J$ and $I_{k}$ overlap and $|I_{k}| \geq |J|/2$, every point of $J$ is within $|J|/2 + |I_{k}| \leq |I_{k}| + |I_{k}| + |I_{k}|/2 = 5|I_{k}|/2$ of the center of $I_{k}$. So $J \subseteq I_{k}'$. ✓

**(b) $f(D)$ has measure zero.** Fix $\varepsilon > 0$. For each $x \in D$, $f'(x) = 0$ gives: $\exists\delta_{x} > 0$ such that $|f(y) - f(x)| < \varepsilon|y - x|$ for $|y - x| < \delta_{x}$. Let $J_{x} = (x - \delta_{x}, x + \delta_{x}) \cap (0,1)$. Then $f(J_{x})$ is contained in an interval of length $< 2\varepsilon\delta_{x} = \varepsilon|J_{x}|$.

Apply (a) to $\{J_{x} : x \in D\}$: extract disjoint $J_{1}, J_{2}, \ldots$ with $D \subseteq \cup J_{k}'$. Since $f$ is differentiable (hence continuous) at $x$, the image $f(J_{k}')$ is contained in an interval of length $\leq 5\varepsilon|J_{k}|$ (the $5\times$ interval has length $5|J_{k}|$, and $f$ maps it with slope $< \varepsilon$).

$m^*(f(D)) \leq \sum m^*(f(J_{k}')) \leq \sum 5\varepsilon|J_{k}| \leq 5\varepsilon \cdot 1 = 5\varepsilon$.

Since $\varepsilon > 0$ was arbitrary, $m^*(f(D)) = 0$. ✓ ∎

**What connects.** Same as a94A05: the Vitali covering lemma is the geometric engine, and part (b) is the 1D Sard theorem for $C^{0}$ functions. The result says the image of the critical set has measure zero without assuming any global regularity — only pointwise differentiability with zero derivative. This is sharp: the assumption $f'(x) = 0$ (not just $f'(x)$ exists) is essential, as a Lipschitz function with $f' \neq 0$ can have $f(D)$ with positive measure for a different definition of "critical."

## 2. Lean 4 theorem statement

```lean
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

open Set MeasureTheory Metric

noncomputable section

/-- The 5× inflation of an open interval (α,β): same center, 5× length. -/
def inflate5 (I : Set ℝ) : Set ℝ :=
  let α := sInf I
  let β := sSup I
  let c := (α + β) / 2
  let r := (β - α) / 2
  Ioo (c - 5 * r / 2) (c + 5 * r / 2)

/-- (a) Vitali covering lemma with factor 5. -/
theorem vitali_covering_5
    {A : Set (Set ℝ)}
    (hA : ∀ I ∈ A, ∃ a b, a < b ∧ I = Ioo a b)
    (hA_sub : ∀ I ∈ A, I ⊆ Ioo 0 1) :
    ∃ S : ℕ → Set ℝ,
      (∀ k, S k ∈ A ∨ S k = ∅) ∧
      Pairwise (Disjoint on S) ∧
      ⋃₀ A ⊆ ⋃ k, inflate5 (S k) := by
  sorry

/-- The critical set: points where f is differentiable with f' = 0. -/
def criticalSet (f : ℝ → ℝ) : Set ℝ :=
  {x ∈ Ioo 0 1 | DifferentiableAt ℝ f x ∧ deriv f x = 0}

/-- (b) The image of the critical set has measure zero. -/
theorem measure_image_criticalSet_eq_zero
    {f : ℝ → ℝ} :
    volume (f '' criticalSet f) = 0 := by
  sorry

/-- At a critical point, f maps small intervals to tiny intervals. -/
lemma image_small_near_critical
    {f : ℝ → ℝ} {x : ℝ}
    (hx : x ∈ criticalSet f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, diam (f '' (Ioo (x - δ) (x + δ) ∩ Ioo 0 1)) ≤ ε * (2 * δ) := by
  sorry

/-- Disjoint intervals in (0,1) have total length ≤ 1. -/
lemma sum_length_disjoint_le_one
    {S : ℕ → Set ℝ}
    (hS_sub : ∀ k, S k ⊆ Ioo 0 1)
    (hS_disj : Pairwise (Disjoint on S)) :
    ∑' k, volume (S k) ≤ 1 := by
  sorry

/-- Outer measure of the image is bounded by ε times total length
    via the covering. -/
lemma measure_image_le_eps_of_covering
    {f : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    {S : ℕ → Set ℝ}
    (hS_disj : Pairwise (Disjoint on S))
    (hS_sub : ∀ k, S k ⊆ Ioo 0 1)
    (hcover : criticalSet f ⊆ ⋃ k, inflate5 (S k))
    (himage : ∀ k, diam (f '' inflate5 (S k)) ≤ 5 * ε * volume (S k) |>.toReal) :
    volume (f '' criticalSet f) ≤ ENNReal.ofReal (5 * ε) := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `MeasureTheory.volume` — Lebesgue measure / outer measure
- `DifferentiableAt ℝ f x` — differentiability at a point
- `deriv f x` — derivative value
- `Set.Ioo a b` — open intervals
- `Metric.diam` — diameter of a set
- `Pairwise (Disjoint on S)` — pairwise disjointness

**Key lemmas:**
- `Vitali.exists_disjoint_subfamily_covering_enlargment` — Mathlib's Vitali covering lemma (if available). In `Mathlib.MeasureTheory.Covering.Vitali`
- `HasDerivAt.tendsto_slope_zero` — $f'(x) = 0$ means $(f(y)-f(x))/(y-x) \to 0$ (for the small-image lemma)
- `Metric.tendsto_nhds` — $\varepsilon$-$\delta$ from derivative $= 0$
- `MeasureTheory.measure_iUnion_le` — $\sigma$-subadditivity
- `MeasureTheory.measure_mono` — monotonicity
- `Real.volume_Ioo` — $m(\mathrm{Ioo}\ a\ b) = b - a$
- `ENNReal.tsum_le_of_sum_le` — bounding infinite sums
- `Metric.diam_mono` — diam of subset $\leq$ diam of superset
- `Set.image_subset` — $f(A) \subseteq f(B)$ when $A \subseteq B$

**Tactic hints:**
- `intro ε hε` — starting the measure-zero $\varepsilon$ argument
- `choose δ hδ_pos hδ_bound using fun x hx => image_small_near_critical hx hε` — covering intervals
- `obtain ⟨S, hS_mem, hS_disj, hS_cover⟩ := vitali_covering_5 ...` — apply Vitali
- `calc volume (f '' criticalSet f) ≤ Σ volume (f '' inflate5 (S k)) ≤ 5ε · Σ volume (S k) ≤ 5ε` — chain
- `gcongr` — for monotonicity
- `positivity` — for $\varepsilon > 0$, $\delta > 0$
- `linarith` — for interval length arithmetic
- `simp [inflate5]` — unfolding the inflation