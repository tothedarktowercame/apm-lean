# APM a94A05: Vitali covering lemma and $f(C)$ has measure zero when $f'=0$

## 1. Informal proof

**Why it's hard.** Part (a) is the Vitali covering lemma, which requires a greedy selection algorithm from an arbitrary (possibly uncountable) collection of intervals — the challenge is ensuring the selected disjoint subcollection, after inflation by factor 5, still covers the union. Part (b) uses (a) to show the image of the critical set has measure zero for an *arbitrary* function (no continuity assumed!), which is surprising.

**The key insight.** (a) Greedily pick the largest available interval, remove everything it intersects, repeat. Any interval not selected is intersected by a selected one of at least its length, so it's covered by the $5\times$ inflation. (b) At each point $x \in C$, $f'(x) = 0$ means $f$ maps small intervals around $x$ to tiny intervals. Cover $C$ by such small intervals, apply Vitali to extract a disjoint subcollection, and the total measure of $f(C)$ is bounded by $\varepsilon$ times the total length.

**Proof.**

**(a) Vitali covering lemma.** Let $A$ be a collection of open subintervals of a bounded interval $I$, $U = \cup A$.

Greedily select: let $d_{1} = \sup\{|J| : J \in A\}$. Choose $I_{1} \in A$ with $|I_{1}| > d_{1}/2$. Having chosen $I_{1},\ldots,I_{k}$, let $A_k = \{J \in A : J \cap I_{j} = \emptyset$ for all $j \leq k\}$. If $A_k = \emptyset$, stop. Otherwise let $d_{k+1} = \sup\{|J| : J \in A_k\}$ and choose $I_{k+1} \in A_k$ with $|I_{k+1}| > d_{k+1}/2$.

The $I_j$ are pairwise disjoint by construction. Claim: $U \subseteq \cup_j I'_j$.

Let $x \in U$. Then $x \in J$ for some $J \in A$. If $J =$ some $I_j$, done ($x \in I_j \subset I'_j$). If $J$ was not selected, then at some step $k$, $J$ was eliminated because $J \cap I_{k} \neq \emptyset$ and $|I_{k}| \geq d_{k}/2 \geq |J|/2$. Since $J$ and $I_{k}$ intersect and $|I_{k}| \geq |J|/2$, $J$ is contained in the $5\times$ inflation $I'_{k}$ (the center of $I_{k}$ is within $|I_{k}|/2 + |J| \leq |I_{k}|/2 + 2|I_{k}| = 5|I_{k}|/2$ of any point in $J$). So $x \in I'_{k}$.

**(b) $f(C)$ has measure zero.** Fix $\varepsilon > 0$. For each $x \in C$, $f'(x) = 0$ means: for every $\eta > 0$, there exists $\delta_x > 0$ such that $|f(y) - f(x)| < \eta|y-x|$ for $|y-x| < \delta_x$.

Choose $\eta = \varepsilon$. For each $x \in C$, let $J_x = (x - \delta_x, x + \delta_x)$. Then $f(J_x \cap I)$ is contained in an interval of length $< 2\varepsilon \cdot \delta_x = \varepsilon \cdot |J_x|$.

The collection $\{J_x : x \in C\}$ covers $C$. By part (a), extract pairwise disjoint $J_{1}, J_{2},\ldots$ with $C \subseteq \cup J'_{k}$.

Then $f(C) \subseteq f(\cup J'_{k}) = \cup f(J'_{k})$. Each $J'_{k}$ is concentric with $J_{k}$ with $|J'_{k}| = 5|J_{k}|$, and $f$ maps $J'_{k}$ into an interval of length $< \varepsilon \cdot |J'_{k}| = 5\varepsilon \cdot |J_{k}|$ (using $f'=0$ at the center with a slightly larger $\delta$, or adjusting $\eta$).

So $m^*(f(C)) \leq \sum 5\varepsilon|J_{k}| = 5\varepsilon \sum|J_{k}| \leq 5\varepsilon|I|$ (since the $J_{k}$ are disjoint in $I$).

Since $\varepsilon$ was arbitrary, $m^*(f(C)) = 0$. ∎

**What connects.** Part (a) is the classical Vitali covering lemma (the "simple" or "finite-dimensional" version with factor 5, not the measure-theoretic Vitali covering theorem). It's one of the most important tools in geometric measure theory. Part (b) is a baby version of Sard's theorem for functions of one variable: the image of the critical set has measure zero. The full Sard's theorem (for smooth maps $\mathbb{R}^{n} \to \mathbb{R}^{m}$) requires much more sophisticated covering arguments and is one of the deepest results in differential topology. The factor 5 in the Vitali lemma is not optimal (3 suffices with a slightly different algorithm) but is the standard textbook constant.

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
- `MeasureTheory.OuterMeasure` — outer measure (for $m^*(f(C))$)
- `Set.Ioo a b` — open intervals
- `DifferentiableAt ℝ f x` — differentiability
- `deriv f x` — derivative
- `Bornology.IsBounded` — bounded sets
- `Pairwise ... Disjoint` — pairwise disjointness

**Key lemmas:**
- `Vitali.exists_disjoint_subfamily_covering_enlargment` — Mathlib's Vitali covering lemma. In `Mathlib.MeasureTheory.Covering.VitaliFamily` or `Mathlib.MeasureTheory.Covering.Vitali`. This is the core of part (a)
- `hasDerivAt_iff_tendsto_slope` — $f'(x) = 0$ means the slope $(f(y)-f(x))/(y-x) \to 0$
- `Metric.tendsto_nhds` — $\varepsilon$-$\delta$ characterisation of limit (for extracting $\delta$ from $f'=0$)
- `MeasureTheory.measure_iUnion_le` — $\sigma$-subadditivity: $m(\cup E_{k}) \leq \sum m(E_{k})$
- `MeasureTheory.measure_mono` — monotonicity
- `Real.volume_Ioo` — $m(\mathrm{Ioo}\ a\ b) = b - a$
- `MeasureTheory.measure_image_le_of_lipschitzOnWith` — not directly, but related to bounding image measure
- `tsum_le_tsum` — comparing infinite sums
- `ENNReal.tsum_le_of_sum_le` — bounding tsum by a bound on partial sums

**Tactic hints:**
- `intro ε hε` — starting the measure-zero argument
- `choose δ hδ_pos hδ_bound using fun x hx => image_small_of_deriv_zero ...` — extracting covering intervals
- `obtain ⟨S, hS_mem, hS_disj, hS_cover⟩ := vitali_covering_lemma_5 ...` — applying Vitali
- `calc volume (f '' C) ≤ Σ volume (f '' inflate5 ...) ≤ 5ε · Σ volume (S k) ≤ 5ε · volume I` — chain
- `gcongr` — monotonicity steps
- `positivity` — for $\varepsilon > 0$, $\delta > 0$
- `linarith` — arithmetic with interval lengths
- `simp [inflate5]` — unfolding the inflation definition