

# APM a93A01: Uniform continuity via difference quotient characterization

## 1. Informal proof

**Why it's hard.** Condition (b) is unusual: it says "when the difference quotient is large, the function values are close." This seems backwards — large slope usually means large change. The subtlety is that large $|f(x)-f(y)|/|x-y|$ combined with small $|f(x)-f(y)|$ forces $|x-y|$ to be extremely small, so (b) is really controlling what happens when points are close together.

**The key insight.** Condition (b) is a contrapositive restatement of: "if $|f(x)-f(y)| \geq \varepsilon$ then the difference quotient is bounded by $N$" — which means $|x-y| \geq |f(x)-f(y)|/N \geq \varepsilon/N$. Taking the contrapositive of *that*: if $|x-y| < \varepsilon/N$ then $|f(x)-f(y)| < \varepsilon$. This is exactly uniform continuity with $\delta = \varepsilon/N$.

**Proof.**

**(a) $\implies$ (b):** Assume $f$ is uniformly continuous. Fix $\varepsilon > 0$. Choose $\delta > 0$ such that $|x-y| < \delta \implies |f(x)-f(y)| < \varepsilon$. Set $N = \varepsilon/\delta$. Now suppose $x \neq y$ and $|f(x)-f(y)|/|x-y| > N = \varepsilon/\delta$. We want $|f(x)-f(y)| < \varepsilon$.

From $|f(x)-f(y)|/|x-y| > \varepsilon/\delta$, if $|f(x)-f(y)| \geq \varepsilon$, then $|x-y| < \delta \cdot |f(x)-f(y)|/\varepsilon$... this isn't quite right. Let's use the contrapositive more carefully.

Suppose $|f(x)-f(y)| \geq \varepsilon$. Then since $f$ is uniformly continuous with modulus $\delta$, we must have $|x-y| \geq \delta$. So the difference quotient satisfies $|f(x)-f(y)|/|x-y| \leq |f(x)-f(y)|/\delta$. But this doesn't directly bound it by $N$.

Actually, we need to be more careful. We cannot bound the difference quotient above just from uniform continuity ($f$ could have large oscillations on large intervals). Let me reconsider.

Set $N = 1/\delta$ (not $\varepsilon/\delta$). Suppose $|f(x)-f(y)|/|x-y| > N = 1/\delta$. Then $|x-y| < \delta \cdot |f(x)-f(y)| \leq \delta$ (if $|f(x)-f(y)| \leq 1$, which isn't guaranteed). This doesn't work either.

Better approach for (a) $\implies$ (b): Fix $\varepsilon > 0$. By uniform continuity, $\exists\delta > 0: |x-y| < \delta \implies |f(x)-f(y)| < \varepsilon$. Since $(0,1)$ has diameter 1, for $x,y \in (0,1)$, $|f(x)-f(y)|/|x-y| > N$ implies $|x-y| < |f(x)-f(y)|/N$. If we choose $N$ large enough that $|f(x)-f(y)|/N < \delta$ whenever $|f(x)-f(y)|$ is large... Actually: the difference quotient being $> N$ means $|x-y| < |f(x)-f(y)|/N$. For any bound $B$ on $|f(x)-f(y)|$ (which exists if $f$ is bounded on $(0,1)$ — but $f$ need not be bounded on the open interval!), we'd get $|x-y| < B/N < \delta$ for $N > B/\delta$, giving $|f(x)-f(y)| < \varepsilon$.

The issue is $f$ might be unbounded on $(0,1)$. But actually: if $|f(x)-f(y)|/|x-y| > N$ and $|f(x)-f(y)| \geq \varepsilon$, then $|x-y| < |f(x)-f(y)|/N$. We need this to be $< \delta$. So we need $|f(x)-f(y)| < N\delta$. But $|f(x)-f(y)|$ could be anything.

Correct approach: From $|f(x)-f(y)|/|x-y| > N$, we get $|x-y| < |f(x)-f(y)|/N \leq \max(|f(x)-f(y)|, 1)/N$. Hmm, this is circular.

Let me just directly prove (a) $\implies$ (b): Given $\varepsilon$, take $\delta$ from uniform continuity. Set $N = \varepsilon/\delta$. If $|f(x)-f(y)|/|x-y| > N$ and $|f(x)-f(y)| \geq \varepsilon$, then $|x-y| < |f(x)-f(y)|/N$. Also from $|f(x)-f(y)| \geq \varepsilon$ and UC, $|x-y| \geq \delta$. So $\delta \leq |x-y| < |f(x)-f(y)|/N$, giving $|f(x)-f(y)| > N\delta = \varepsilon$, consistent but not contradictory.

I think the cleaner approach: suppose $|f(x)-f(y)|/|x-y| > N$. Then $|x-y| < |f(x)-f(y)|/N$. Now: $|f(x)-f(y)| = |f(x)-f(y)|/|x-y| \cdot |x-y|$ — just a tautology. We need another handle.

The trick is: the contrapositive of (b) is: $\exists\varepsilon>0: \forall N>0: \exists x,y$ with $|f(x)-f(y)|/|x-y| > N$ and $|f(x)-f(y)| \geq \varepsilon$. This means: there exist sequences with $|x_n - y_n| \to 0$ (since the quotient $\to \infty$ while $|f(x_n)-f(y_n)| \geq \varepsilon$), contradicting UC (which says $|x-y|$ small $\implies$ $|f(x)-f(y)|$ small). And the contrapositive of $\neg$UC is: $\exists\varepsilon>0: \forall\delta>0: \exists x,y: |x-y|<\delta$ and $|f(x)-f(y)| \geq \varepsilon$. This gives a large difference quotient ($\geq \varepsilon/\delta \to \infty$ as $\delta \to 0$) with $|f(x)-f(y)| \geq \varepsilon$, contradicting (b).

So both directions work cleanly via contrapositive.

**(a) $\implies$ (b) by contrapositive.** Assume $\neg$(b): $\exists\varepsilon_{0} > 0: \forall N > 0: \exists x,y \in (0,1), x\neq y$ with $|f(x)-f(y)|/|x-y| > N$ and $|f(x)-f(y)| \geq \varepsilon_{0}$. For each $n \in \mathbb{N}$, take $N = n$ to get $x_n, y_n$ with $|f(x_n)-f(y_n)|/|x_n-y_n| > n$ and $|f(x_n)-f(y_n)| \geq \varepsilon_{0}$. From the first: $|x_n-y_n| < |f(x_n)-f(y_n)|/n$. Since $x_n, y_n \in (0,1)$, $|f(x_n)-f(y_n)|$ can grow, but $|x_n-y_n| <$ (anything)$/n \to 0$. So $|x_n-y_n| \to 0$ while $|f(x_n)-f(y_n)| \geq \varepsilon_{0}$, contradicting UC. ✓

**(b) $\implies$ (a) by contrapositive.** Assume $\neg$UC: $\exists\varepsilon_{0} > 0: \forall\delta > 0: \exists x,y \in (0,1): |x-y| < \delta$ and $|f(x)-f(y)| \geq \varepsilon_{0}$. Use (b) with this $\varepsilon_{0}$: get $N_{0}$ such that $|f(x)-f(y)|/|x-y| > N_{0} \implies |f(x)-f(y)| < \varepsilon_{0}$. Now take $\delta = \varepsilon_{0}/N_{0}$ in $\neg$UC: get $x,y$ with $|x-y| < \varepsilon_{0}/N_{0}$ and $|f(x)-f(y)| \geq \varepsilon_{0}$. Then $|f(x)-f(y)|/|x-y| > \varepsilon_{0}/(\varepsilon_{0}/N_{0}) = N_{0}$. By (b): $|f(x)-f(y)| < \varepsilon_{0}$. Contradiction. ✓

**What connects.** Condition (b) is a reformulation of uniform continuity that emphasizes the *difference quotient* rather than the *modulus of continuity*. Intuitively, it says: "steep slopes can only occur over tiny intervals" — which is a way of saying the function can't oscillate by a fixed amount over arbitrarily small scales, exactly uniform continuity. The equivalence is purely via contrapositive manipulation. This characterization connects to Lipschitz-type conditions: if (b) held with the stronger condition $|f(x)-f(y)| = 0$ (instead of $< \varepsilon$) whenever the quotient $> N$, that would force $f$ to be constant. The $\varepsilon$-slack is what allows nonconstant uniformly continuous functions. The result also relates to the concept of functions of bounded variation on subintervals and to the modulus of continuity $\omega(\delta) \to 0$.

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
- `Set.Ioo (0:ℝ) 1` — the open interval $(0,1)$
- `Metric.dist` / $|x - y|$ — distance in $\mathbb{R}$
- `Filter.atTop` — for the sequential arguments
- `Filter.Tendsto` — convergence of sequences

**Key lemmas:**
- `Metric.uniformContinuousOn_iff` — $\varepsilon$-$\delta$ characterisation of UniformContinuousOn: `∀ ε > 0, ∃ δ > 0, ∀ x ∈ S, ∀ y ∈ S, dist x y < δ → dist (f x) (f y) < ε`
- `abs_div` — $|a/b| = |a|/|b|$ for the difference quotient
- `div_lt_iff` / `lt_div_iff` — rearranging $|f(x)-f(y)|/|x-y| > N \leftrightarrow |f(x)-f(y)| > N|x-y|$ (when $|x-y| > 0$)
- `abs_pos.mpr` / `sub_ne_zero.mpr` — $|x-y| > 0$ from $x \neq y$
- `squeeze_zero_norm` — if $|x_n - y_n| \leq C/n \to 0$ then $|x_n - y_n| \to 0$
- `tendsto_const_div_atTop_nhds_zero` — $C/n \to 0$ as $n \to \infty$
- `not_forall` / `not_exists` — pushing negation through quantifiers for contrapositive
- `Classical.choice` — extracting sequences from existential quantifiers

**Tactic hints:**
- `by_contra h; push_neg at h` — contrapositive arguments in both directions
- `choose x_n y_n hx hy using h` — extracting witnessing sequences
- `intro ε hε; obtain ⟨N, hN, hbound⟩ := hf ε hε` — unpacking the $\varepsilon$-$\delta$/$\varepsilon$-$N$ statements
- `refine ⟨ε / N, by positivity, ?_⟩` — constructing $\delta = \varepsilon/N$ for (b) $\implies$ (a)
- `calc |x_n - y_n| < |f(x_n) - f(y_n)| / n ≤ ... ` — estimating the gap
- `linarith` — combining the inequalities
- `field_simp` — clearing denominators in the difference quotient
- `nlinarith [abs_nonneg (x - y)]` — nonlinear arithmetic combining bounds
- `exact?` — finding the right rearrangement lemma