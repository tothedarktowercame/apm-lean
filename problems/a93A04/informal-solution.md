

# APM a93A04: Absolutely continuous functions are exactly the BV-limits of Lipschitz functions

## 1. Informal proof

**Why it's hard.** The total variation norm $V(f)$ is a very strong topology — convergence in $V$ means convergence of the function *and* its derivative in $L^{1}$. Showing that absolutely continuous functions are exactly the closure of Lipschitz functions in this norm requires constructing explicit Lipschitz approximations (forward direction) and showing the limit inherits absolute continuity (reverse direction).

**The key insight.** An absolutely continuous function satisfies $f(x) = f(0) + \int_{0}^{x} f'(t) dt$ with $f' \in L^{1}$, and $V(f) = \int_{0}^{1} |f'|$. Truncating $f'$ at height $n$ gives Lipschitz functions $f_{n}(x) = f(0) + \int_{0}^{x} g_{n}(t) dt$ where $g_{n} = \max(-n, \min(n, f'))$, and $V(f_{n} - f) = \int|f' - g_{n}| \to 0$ by DCT. Conversely, BV-limits of Lipschitz (hence AC) functions are AC because AC functions form a closed subspace under the BV norm.

**Proof.**

**($\Longleftarrow$) Lipschitz functions approximate in $V$ $\Longrightarrow$ $f$ is AC.**

Each Lipschitz function on $[0,1]$ is absolutely continuous. We show that if $f_{n}$ are AC and $V(f_{n} - f) \to 0$, then $f$ is AC.

Fix $\varepsilon > 0$. Choose $N$ with $V(f_{n} - f) < \varepsilon/2$ for $n \geq N$. Since $f_{n}$ is AC, $\exists\delta > 0$: for any finite collection of disjoint intervals $(a_{i}, b_{i})$ with $\sum(b_{i} - a_{i}) < \delta$, $\sum|f_{n}(b_{i}) - f_{n}(a_{i})| < \varepsilon/2$.

For any such collection:

$\sum|f(b_{i}) - f(a_{i})| \leq \sum|f(b_{i}) - f_{n}(b_{i}) - (f(a_{i}) - f_{n}(a_{i}))| + \sum|f_{n}(b_{i}) - f_{n}(a_{i})|$
$\leq \sum|(f_{n}-f)(b_{i}) - (f_{n}-f)(a_{i})| + \varepsilon/2$
$\leq V(f_{n} - f) + \varepsilon/2 < \varepsilon/2 + \varepsilon/2 = \varepsilon$.

So $f$ is AC. ✓

**($\Longrightarrow$) $f$ is AC $\Longrightarrow$ Lipschitz functions approximate in $V$.**

Since $f$ is AC on $[0,1]$, $f'$ exists a.e. and $f(x) = f(0) + \int_{0}^{x} f'(t) dt$, with $V(f) = \int_{0}^{1} |f'(t)| dt < \infty$.

Define truncations $g_{n}(t) = \max(-n, \min(n, f'(t)))$. Then $|g_{n}| \leq n$, so $g_{n}$ is bounded.

Define $f_{n}(x) = f(0) + \int_{0}^{x} g_{n}(t) dt$. Then $f_{n}$ is Lipschitz with constant $n$ (since $|f_{n}(x) - f_{n}(y)| = |\int_{x}^{y} g_{n}| \leq n|x-y|$).

The variation of the difference:

$V(f_{n} - f) = \int_{0}^{1} |g_{n}(t) - f'(t)| dt$

(since $f_{n} - f$ is AC with derivative $g_{n} - f'$, and for AC functions $V$ equals the $L^{1}$ norm of the derivative).

Now $|g_{n}(t) - f'(t)| \leq 2|f'(t)|$ (integrable dominator), and $g_{n}(t) \to f'(t)$ pointwise a.e. (since $f'(t)$ is finite a.e. and the truncation converges to $f'$ where $f'$ is finite). By the dominated convergence theorem:

$V(f_{n} - f) = \int_{0}^{1} |g_{n} - f'| \to 0$. ✓ ∎

**What connects.** This problem characterises absolutely continuous functions as the closure of Lipschitz functions in the total variation norm. It places AC functions in a hierarchy: Lip $\subset$ AC $\subset$ BV, where Lip is dense in AC under $V$ but not in BV (the Cantor function is BV but not AC, and no Lipschitz sequence can approximate it in $V$). The key identity $V(f) = \int|f'|$ for AC functions converts the variation-norm problem into an $L^{1}$ approximation problem for derivatives. This connects to the Sobolev space $W^{1,1}([0,1])$: AC functions on $[0,1]$ are exactly $W^{1,1}$ functions (after choosing the right representative), and Lipschitz = $W^{1,\infty}$. The density of $W^{1,\infty}$ in $W^{1,1}$ is a standard Sobolev space fact (smooth/Lipschitz functions are dense in $W^{1,p}$ for $p < \infty$).

## 2. Lean 4 theorem statement

```lean
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

open MeasureTheory Set Filter

noncomputable section

/-- Total variation of f on [0,1]. -/
def totalVariation (f : ℝ → ℝ) : ℝ :=
  sSup {s : ℝ | ∃ (n : ℕ) (t : Fin (n+1) → ℝ),
    (∀ i, t i ∈ Icc 0 1) ∧
    (∀ i : Fin n, t i.castSucc < t i.succ) ∧
    s = ∑ i : Fin n, |f (t i.succ) - f (t i.castSucc)|}

/-- f is absolutely continuous on [0,1]. -/
def AbsolutelyContinuousOn01 (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (n : ℕ) (a b : Fin n → ℝ),
    (∀ i, a i ∈ Icc 0 1) → (∀ i, b i ∈ Icc 0 1) →
    (∀ i, a i < b i) →
    (∀ i j, i ≠ j → Ioo (a i) (b i) ∩ Ioo (a j) (b j) = ∅) →
    ∑ i, (b i - a i) < δ →
    ∑ i, |f (b i) - f (a i)| < ε

/-- f is Lipschitz on [0,1]. -/
def LipschitzOn01 (f : ℝ → ℝ) : Prop :=
  ∃ K, ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, |f x - f y| ≤ K * |x - y|

/-- (⟹) AC functions are V-limits of Lipschitz functions. -/
theorem ac_implies_lipschitz_V_approx
    {f : ℝ → ℝ} (hac : AbsolutelyContinuousOn01 f) :
    ∃ fₙ : ℕ → ℝ → ℝ,
      (∀ n, LipschitzOn01 (fₙ n)) ∧
      Tendsto (fun n => totalVariation (fun x => fₙ n x - f x)) atTop (𝓝 0) := by
  sorry

/-- (⟸) V-limits of Lipschitz functions are AC. -/
theorem lipschitz_V_limit_implies_ac
    {f : ℝ → ℝ} {fₙ : ℕ → ℝ → ℝ}
    (hlip : ∀ n, LipschitzOn01 (fₙ n))
    (hconv : Tendsto (fun n => totalVariation (fun x => fₙ n x - f x)) atTop (𝓝 0)) :
    AbsolutelyContinuousOn01 f := by
  sorry

/-- Main theorem: equivalence. -/
theorem ac_iff_lipschitz_V_approx (f : ℝ → ℝ) :
    AbsolutelyContinuousOn01 f ↔
    ∃ fₙ : ℕ → ℝ → ℝ,
      (∀ n, LipschitzOn01 (fₙ n)) ∧
      Tendsto (fun n => totalVariation (fun x => fₙ n x - f x)) atTop (𝓝 0) := by
  sorry

/-- For AC functions, V(f) = ∫₀¹ |f'|. -/
lemma totalVariation_eq_integral_deriv
    {f : ℝ → ℝ} (hac : AbsolutelyContinuousOn01 f) :
    totalVariation f = ∫ x in Icc (0:ℝ) 1, ‖deriv f x‖ ∂volume := by
  sorry

/-- Truncation of an L¹ function at height n converges in L¹. -/
lemma truncation_tendsto_L1
    {g : ℝ → ℝ} (hg : IntegrableOn g (Icc 0 1) volume) :
    Tendsto (fun n : ℕ =>
      ∫ x in Icc (0:ℝ) 1, ‖max (-↑n) (min (↑n) (g x)) - g x‖ ∂volume)
      atTop (𝓝 0) := by
  sorry

/-- The antiderivative of a bounded function is Lipschitz. -/
lemma lipschitz_of_bounded_antideriv
    {g : ℝ → ℝ} {n : ℝ} (hbound : ∀ x ∈ Icc (0:ℝ) 1, |g x| ≤ n) :
    LipschitzOn01 (fun x => ∫ t in Icc (0:ℝ) x, g t ∂volume) := by
  sorry

/-- Lipschitz on [0,1] implies AC on [0,1]. -/
lemma lipschitz_implies_ac
    {f : ℝ → ℝ} (hlip : LipschitzOn01 f) :
    AbsolutelyContinuousOn01 f := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `LipschitzOnWith K f s` / `LipschitzWith K f` — Mathlib's Lipschitz predicate (in `Mathlib.Topology.MetricSpace.Lipschitz`)
- `MeasureTheory.IntegrableOn g (Icc 0 1) volume` — integrability on $[0,1]$
- `eVariationOn f s` — Mathlib's variation function (in `Mathlib.Analysis.BoundedVariation`). Uses extended reals
- `HasBoundedVariationOn f s` — BV predicate
- `Set.Icc (0:ℝ) 1` — the interval $[0,1]$
- `deriv f x` — derivative of $f$

**Key lemmas:**
- `eVariationOn.eq_of_eq_ae` / variation properties — relating $V(f)$ to the $L^{1}$ norm of the derivative for AC functions
- `MeasureTheory.integral_deriv_eq_sub` — FTC: $\int_{a}^{b} f' = f(b) - f(a)$ for AC functions
- `MeasureTheory.tendsto_integral_of_dominated_convergence` — DCT for the truncation argument
- `IntegrableOn.norm` — $|f'|$ is integrable when $f'$ is
- `min_le_of_left_le` / `max_le` — for truncation bounds
- `LipschitzOnWith.absolutelyContinuousOn` — Lip $\Longrightarrow$ AC (may not be in Mathlib by this name)
- `intervalIntegral.norm_integral_le_of_norm_le` — $|\int_{a}^{b} g| \leq \int_{a}^{b} |g| \leq n|b-a|$ for bounded $g$

**Tactic hints:**
- `intro ε hε` — starting the $\varepsilon$-$\delta$ arguments
- `obtain ⟨N, hN⟩ := (hconv.eventually (gt_mem_nhds hε)).exists` — extracting $N$ from $V$-convergence
- `refine ⟨fun n x => f 0 + ∫ t in Icc 0 x, max (-↑n) (min ↑n (deriv f t)), ?_, ?_⟩` — constructing the Lipschitz approximations
- `calc Σ |f(bᵢ)-f(aᵢ)| ≤ ...` — for the triangle inequality in the reverse direction
- `gcongr` — for variation monotonicity
- `exact tendsto_integral_of_dominated_convergence ...` — applying DCT
- `positivity` — for $\varepsilon > 0$, $\delta > 0$
- `linarith` — combining the $\varepsilon/2$ bounds