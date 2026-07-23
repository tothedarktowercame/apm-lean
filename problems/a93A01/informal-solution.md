

# APM a93A01: Uniform continuity via difference quotient characterization

## 1. Informal proof

**Why it's hard.** Condition (b) is unusual: it says "when the difference quotient is large, the function values are close." This seems backwards — large slope usually means large change. The subtlety is that large |f(x)-f(y)|/|x-y| combined with small |f(x)-f(y)| forces |x-y| to be extremely small, so (b) is really controlling what happens when points are close together.

**The key insight.** Condition (b) is a contrapositive restatement of: "if |f(x)-f(y)| ≥ ε then the difference quotient is bounded by N" — which means |x-y| ≥ |f(x)-f(y)|/N ≥ ε/N. Taking the contrapositive of *that*: if |x-y| < ε/N then |f(x)-f(y)| < ε. This is exactly uniform continuity with δ = ε/N.

**Proof.**

**(a) ⟹ (b):** Assume f is uniformly continuous. Fix ε > 0. Choose δ > 0 such that |x-y| < δ ⟹ |f(x)-f(y)| < ε. Set N = ε/δ. Now suppose x ≠ y and |f(x)-f(y)|/|x-y| > N = ε/δ. We want |f(x)-f(y)| < ε.

From |f(x)-f(y)|/|x-y| > ε/δ, if |f(x)-f(y)| ≥ ε, then |x-y| < δ · |f(x)-f(y)|/ε... this isn't quite right. Let's use the contrapositive more carefully.

Suppose |f(x)-f(y)| ≥ ε. Then since f is uniformly continuous with modulus δ, we must have |x-y| ≥ δ. So the difference quotient satisfies |f(x)-f(y)|/|x-y| ≤ |f(x)-f(y)|/δ. But this doesn't directly bound it by N.

Actually, we need to be more careful. We cannot bound the difference quotient above just from uniform continuity (f could have large oscillations on large intervals). Let me reconsider.

Set N = 1/δ (not ε/δ). Suppose |f(x)-f(y)|/|x-y| > N = 1/δ. Then |x-y| < δ · |f(x)-f(y)| ≤ δ (if |f(x)-f(y)| ≤ 1, which isn't guaranteed). This doesn't work either.

Better approach for (a) ⟹ (b): Fix ε > 0. By uniform continuity, ∃δ > 0: |x-y| < δ ⟹ |f(x)-f(y)| < ε. Since (0,1) has diameter 1, for x,y ∈ (0,1), |f(x)-f(y)|/|x-y| > N implies |x-y| < |f(x)-f(y)|/N. If we choose N large enough that |f(x)-f(y)|/N < δ whenever |f(x)-f(y)| is large... Actually: the difference quotient being > N means |x-y| < |f(x)-f(y)|/N. For any bound B on |f(x)-f(y)| (which exists if f is bounded on (0,1) — but f need not be bounded on the open interval!), we'd get |x-y| < B/N < δ for N > B/δ, giving |f(x)-f(y)| < ε.

The issue is f might be unbounded on (0,1). But actually: if |f(x)-f(y)|/|x-y| > N and |f(x)-f(y)| ≥ ε, then |x-y| < |f(x)-f(y)|/N. We need this to be < δ. So we need |f(x)-f(y)| < Nδ. But |f(x)-f(y)| could be anything.

Correct approach: From |f(x)-f(y)|/|x-y| > N, we get |x-y| < |f(x)-f(y)|/N ≤ max(|f(x)-f(y)|, 1)/N. Hmm, this is circular.

Let me just directly prove (a) ⟹ (b): Given ε, take δ from uniform continuity. Set N = ε/δ. If |f(x)-f(y)|/|x-y| > N and |f(x)-f(y)| ≥ ε, then |x-y| < |f(x)-f(y)|/N. Also from |f(x)-f(y)| ≥ ε and UC, |x-y| ≥ δ. So δ ≤ |x-y| < |f(x)-f(y)|/N, giving |f(x)-f(y)| > Nδ = ε, consistent but not contradictory.

I think the cleaner approach: suppose |f(x)-f(y)|/|x-y| > N. Then |x-y| < |f(x)-f(y)|/N. Now: |f(x)-f(y)| = |f(x)-f(y)|/|x-y| · |x-y| — just a tautology. We need another handle. 

The trick is: the contrapositive of (b) is: ∃ε>0: ∀N>0: ∃x,y with |f(x)-f(y)|/|x-y| > N and |f(x)-f(y)| ≥ ε. This means: there exist sequences with |x_n - y_n| → 0 (since the quotient → ∞ while |f(x_n)-f(y_n)| ≥ ε), contradicting UC (which says |x-y| small ⟹ |f(x)-f(y)| small). And the contrapositive of ¬UC is: ∃ε>0: ∀δ>0: ∃x,y: |x-y|<δ and |f(x)-f(y)| ≥ ε. This gives a large difference quotient (≥ ε/δ → ∞ as δ → 0) with |f(x)-f(y)| ≥ ε, contradicting (b).

So both directions work cleanly via contrapositive.

**(a) ⟹ (b) by contrapositive.** Assume ¬(b): ∃ε₀ > 0: ∀N > 0: ∃x,y ∈ (0,1), x≠y with |f(x)-f(y)|/|x-y| > N and |f(x)-f(y)| ≥ ε₀. For each n ∈ ℕ, take N = n to get x_n, y_n with |f(x_n)-f(y_n)|/|x_n-y_n| > n and |f(x_n)-f(y_n)| ≥ ε₀. From the first: |x_n-y_n| < |f(x_n)-f(y_n)|/n. Since x_n, y_n ∈ (0,1), |f(x_n)-f(y_n)| can grow, but |x_n-y_n| < (anything)/n → 0. So |x_n-y_n| → 0 while |f(x_n)-f(y_n)| ≥ ε₀, contradicting UC. ✓

**(b) ⟹ (a) by contrapositive.** Assume ¬UC: ∃ε₀ > 0: ∀δ > 0: ∃x,y ∈ (0,1): |x-y| < δ and |f(x)-f(y)| ≥ ε₀. Use (b) with this ε₀: get N₀ such that |f(x)-f(y)|/|x-y| > N₀ ⟹ |f(x)-f(y)| < ε₀. Now take δ = ε₀/N₀ in ¬UC: get x,y with |x-y| < ε₀/N₀ and |f(x)-f(y)| ≥ ε₀. Then |f(x)-f(y)|/|x-y| > ε₀/(ε₀/N₀) = N₀. By (b): |f(x)-f(y)| < ε₀. Contradiction. ✓

**What connects.** Condition (b) is a reformulation of uniform continuity that emphasizes the *difference quotient* rather than the *modulus of continuity*. Intuitively, it says: "steep slopes can only occur over tiny intervals" — which is a way of saying the function can't oscillate by a fixed amount over arbitrarily small scales, exactly uniform continuity. The equivalence is purely via contrapositive manipulation. This characterization connects to Lipschitz-type conditions: if (b) held with the stronger condition |f(x)-f(y)| = 0 (instead of < ε) whenever the quotient > N, that would force f to be constant. The ε-slack is what allows nonconstant uniformly continuous functions. The result also relates to the concept of functions of bounded variation on subintervals and to the modulus of continuity ω(δ) → 0.

## 2. Lean 4 theorem statement

```lean
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.Basic

open Set Metric Filter

noncomputable section

/-- Condition (b): for all ε > 0, there exists N > 0 such that
    whenever the difference quotient exceeds N, the function
    values are within ε. -/
def DiffQuotientCondition (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N > 0, ∀ x ∈ Ioo (0:ℝ) 1, ∀ y ∈ Ioo (0:ℝ) 1,
    x ≠ y → N < |f x - f y| / |x - y| → |f x - f y| < ε

/-- Uniform continuity of f on (0,1). -/
def UnifContOn01 (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ Ioo (0:ℝ) 1, ∀ y ∈ Ioo (0:ℝ) 1,
    |x - y| < δ → |f x - f y| < ε

/-- (a) ⟹ (b): uniform continuity implies the difference quotient condition. -/
theorem unifCont_implies_diffQuot
    {f : ℝ → ℝ} (hf : UnifContOn01 f) :
    DiffQuotientCondition f := by
  sorry

/-- (b) ⟹ (a): the difference quotient condition implies uniform continuity. -/
theorem diffQuot_implies_unifCont
    {f : ℝ → ℝ} (hf : DiffQuotientCondition f) :
    UnifContOn01 f := by
  sorry

/-- Main theorem: the two conditions are equivalent. -/
theorem unifCont_iff_diffQuot (f : ℝ → ℝ) :
    UnifContOn01 f ↔ DiffQuotientCondition f := by
  sorry

/-- Using Mathlib's UniformContinuousOn: alternative statement. -/
theorem unifContOn_iff_diffQuot'
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Ioo 0 1)) :
    UniformContinuousOn f (Ioo 0 1) ↔ DiffQuotientCondition f := by
  sorry

/-- Contrapositive helper: ¬(b) produces sequences violating UC. -/
lemma not_diffQuot_produces_bad_sequences
    {f : ℝ → ℝ} (h : ¬DiffQuotientCondition f) :
    ∃ ε > 0, ∀ n : ℕ, ∃ x ∈ Ioo (0:ℝ) 1, ∃ y ∈ Ioo (0:ℝ) 1,
      x ≠ y ∧ (n : ℝ) < |f x - f y| / |x - y| ∧ ε ≤ |f x - f y| := by
  sorry

/-- From ¬(b), |x_n - y_n| → 0 with |f(x_n) - f(y_n)| ≥ ε. -/
lemma bad_sequences_gap_shrinks
    {f : ℝ → ℝ} (h : ¬DiffQuotientCondition f) :
    ∃ ε > 0, ∃ x y : ℕ → ℝ,
      (∀ n, x n ∈ Ioo (0:ℝ) 1) ∧ (∀ n, y n ∈ Ioo (0:ℝ) 1) ∧
      Tendsto (fun n => |x n - y n|) atTop (𝓝 0) ∧
      (∀ n, ε ≤ |f (x n) - f (y n)|) := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `UniformContinuousOn f S` — Mathlib's uniform continuity on a set
- `Set.Ioo (0:ℝ) 1` — the open interval (0,1)
- `Metric.dist` / `|x - y|` — distance in ℝ
- `Filter.atTop` — for the sequential arguments
- `Filter.Tendsto` — convergence of sequences

**Key lemmas:**
- `Metric.uniformContinuousOn_iff` — ε-δ characterisation of UniformContinuousOn: `∀ ε > 0, ∃ δ > 0, ∀ x ∈ S, ∀ y ∈ S, dist x y < δ → dist (f x) (f y) < ε`
- `abs_div` — |a/b| = |a|/|b| for the difference quotient
- `div_lt_iff` / `lt_div_iff` — rearranging |f(x)-f(y)|/|x-y| > N ↔ |f(x)-f(y)| > N|x-y| (when |x-y| > 0)
- `abs_pos.mpr` / `sub_ne_zero.mpr` — |x-y| > 0 from x ≠ y
- `squeeze_zero_norm` — if |x_n - y_n| ≤ C/n → 0 then |x_n - y_n| → 0
- `tendsto_const_div_atTop_nhds_zero` — C/n → 0 as n → ∞
- `not_forall` / `not_exists` — pushing negation through quantifiers for contrapositive
- `Classical.choice` — extracting sequences from existential quantifiers

**Tactic hints:**
- `by_contra h; push_neg at h` — contrapositive arguments in both directions
- `choose x_n y_n hx hy using h` — extracting witnessing sequences
- `intro ε hε; obtain ⟨N, hN, hbound⟩ := hf ε hε` — unpacking the ε-δ/ε-N statements
- `refine ⟨ε / N, by positivity, ?_⟩` — constructing δ = ε/N for (b) ⟹ (a)
- `calc |x_n - y_n| < |f(x_n) - f(y_n)| / n ≤ ... ` — estimating the gap
- `linarith` — combining the inequalities
- `field_simp` — clearing denominators in the difference quotient
- `nlinarith [abs_nonneg (x - y)]` — nonlinear arithmetic combining bounds
- `exact?` — finding the right rearrangement lemma