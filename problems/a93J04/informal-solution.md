# APM a93J04: Lp norms converge to L∞ norm (duplicate of a00J01)

## 1. Informal proof

**Why it's hard.** The Lp norm involves an integral (a global averaging operation) while the L∞ norm is an essential supremum (a local extremal operation). As $p$ grows, the integral increasingly "concentrates" on the set where $|f|$ is near its maximum, but making this precise requires working the bound from both sides with different tools for each direction.

**The key insight.** Upper bound: $|f| \leq ||f||\infty$ a.e. $\Longrightarrow ||f||p \leq ||f||\infty \cdot m([0,1])^{1/p} = ||f||\infty$. Lower bound: for any $c < ||f||\infty$, the set $\{|f| > c\}$ has positive measure, so $||f||p \geq c \cdot m(\{|f|>c\})^{1/p} \to c$ as $p \to \infty$.

**Proof.**

**Upper bound.** Since $|f(x)| \leq ||f||\infty$ for a.e. $x$:

$||f||p = (\int_{0}^{1} |f|^p)^{1/p} \leq (\int_{0}^{1} ||f||\infty^p)^{1/p} = ||f||\infty \cdot m([0,1])^{1/p} = ||f||\infty$.

So $\limsup_{p\to\infty} ||f||p \leq ||f||\infty$.

**Lower bound.** Let $c < ||f||\infty$. By definition of essential supremum, $E_c = \{x \in [0,1] : |f(x)| > c\}$ has $m(E_c) > 0$. Then:

$||f||p^p = \int_{0}^{1} |f|^p \geq \int_{E_c} |f|^p \geq c^p \cdot m(E_c)$.

Taking $p$-th roots: $||f||p \geq c \cdot m(E_c)^{1/p}$. As $p \to \infty$, $m(E_c)^{1/p} \to 1$ (since $m(E_c) > 0$ is a fixed positive constant). So $\liminf ||f||p \geq c$. Since $c < ||f||\infty$ was arbitrary, $\liminf ||f||p \geq ||f||\infty$.

**Combining.** $||f||\infty \leq \liminf ||f||p \leq \limsup ||f||p \leq ||f||\infty$, so the limit exists and equals $||f||\infty$. ∎

**What connects.** This is problem a00J01 revisited. The result underpins the fact that L∞ is the "limit" of the Lp scale — both in the norm sense and in the interpolation sense. The upper bound is the Hölder embedding $Lp \hookrightarrow Lq$ for $p > q$ on finite measure spaces. The lower bound uses the positivity of level sets, which is the defining property of the essential supremum. The proof technique (squeeze between lim inf and lim sup) is standard for proving that limits exist. The result extends to $\sigma$-finite measure spaces with the appropriate normalisation, and connects to the Marcinkiewicz interpolation theorem and the theory of Lorentz spaces.

## 2. Lean 4 theorem statement

```lean
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Order.Filter.Basic

open MeasureTheory ENNReal Filter Set

noncomputable section

variable {f : ℝ → ℝ}

/-- Upper bound: ‖f‖_p ≤ ‖f‖_∞ on a probability/finite measure space. -/
lemma eLpNorm_le_eLpNorm_top
    (hf : AEStronglyMeasurable f (volume.restrict (Icc 0 1)))
    {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ⊤) :
    eLpNorm f p (volume.restrict (Icc 0 1)) ≤
      eLpNorm f ⊤ (volume.restrict (Icc 0 1)) := by
  sorry

/-- Lower bound: for c < ‖f‖_∞, ‖f‖_p ≥ c · m({|f|>c})^{1/p}. -/
lemma eLpNorm_ge_of_essSup
    (hf : AEStronglyMeasurable f (volume.restrict (Icc 0 1)))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {c : ℝ≥0} (hc : (c : ℝ≥0∞) < eLpNorm f ⊤ (volume.restrict (Icc 0 1))) :
    (c : ℝ≥0∞) * ((volume.restrict (Icc 0 1))
      {x | (c : ℝ) < ‖f x‖}) ^ (1 / p.toReal) ≤
      eLpNorm f p (volume.restrict (Icc 0 1)) := by
  sorry

/-- Positive measure of superlevel set when c < ‖f‖_∞. -/
lemma meas_superlevel_pos
    (hf : AEStronglyMeasurable f (volume.restrict (Icc 0 1)))
    {c : ℝ≥0} (hc : (c : ℝ≥0∞) < eLpNorm f ⊤ (volume.restrict (Icc 0 1))) :
    0 < (volume.restrict (Icc 0 1)) {x | (c : ℝ) < ‖f x‖} := by
  sorry

/-- a^{1/p} → 1 as p → ∞ for fixed a > 0, a < ∞. -/
lemma rpow_inv_tendsto_one
    {a : ℝ≥0∞} (ha : 0 < a) (ha' : a ≠ ⊤) :
    Tendsto (fun p : ℝ => a ^ (1 / p)) atTop (𝓝 1) := by
  sorry

/-- Main theorem: ‖f‖_p → ‖f‖_∞ as p → ∞.
    Stated for real-valued exponent p → ∞. -/
theorem tendsto_eLpNorm_atTop
    (hf : AEStronglyMeasurable f (volume.restrict (Icc 0 1)))
    (hf_bdd : eLpNorm f ⊤ (volume.restrict (Icc 0 1)) ≠ ⊤) :
    Tendsto (fun p : ℝ => eLpNorm f (ENNReal.ofReal p)
      (volume.restrict (Icc 0 1)))
      atTop (𝓝 (eLpNorm f ⊤ (volume.restrict (Icc 0 1)))) := by
  sorry

/-- Real-valued version for readability. -/
theorem tendsto_Lp_norm_to_Linfty_norm
    (hf : AEStronglyMeasurable f (volume.restrict (Icc 0 1)))
    (hf_bdd : EssSup (fun x => (‖f x‖₊ : ℝ≥0∞))
      (volume.restrict (Icc 0 1)) ≠ ⊤) :
    Tendsto (fun p : ℝ =>
      (∫ x in Icc (0:ℝ) 1, ‖f x‖ ^ p ∂volume) ^ (1 / p))
      atTop (𝓝 (eLpNorm f ⊤ (volume.restrict (Icc 0 1))).toReal) := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `MeasureTheory.eLpNorm f p μ` — the Lp seminorm (formerly `snorm`)
- `MeasureTheory.essSup` — essential supremum (eLpNorm at $p = \top$ equals essSup $\Vert f\Vert_{+}$)
- `ENNReal.ofReal p` — coercing the real exponent to ℝ≥0∞
- `AEStronglyMeasurable` — measurability hypothesis
- `Measure.restrict (Icc 0 1)` — Lebesgue measure on $[0,1]$
- `Filter.atTop` — filter for $p \to \infty$
- `NNNorm` / `‖·‖₊` — nonneg norm

**Key lemmas:**
- `eLpNorm_le_eLpNorm_mul_rpow_measure_univ` — Hölder embedding: $||f||_p \leq ||f||_q \cdot \mu(X)^{1/p-1/q}$. For $q = \top$ this gives the upper bound. In `Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp`
- `eLpNorm_top_eq_essSup` — $||f||_\infty = essSup \Vert f\Vert_{+}$
- `MeasureTheory.meas_essSup_lt` — $m(\{|f| > c\}) > 0$ when $c < essSup |f|$ (definition of essSup)
- `ENNReal.rpow_natCast` / `ENNReal.rpow_le_rpow` — power function properties
- `ENNReal.tendsto_rpow_nhds_zero_atTop` — $a^{1/p} \to 1$ as $p \to \infty$ for fixed $a \in (0,\infty)$
- `Filter.Tendsto.squeeze` / `tendsto_of_tendsto_of_tendsto_of_le_of_le` — squeeze theorem for the final combination
- `Real.volume_Icc` — $m([0,1]) = 1$
- `Measure.restrict_apply_univ` — $\mu.restrict S univ = \mu S$

**Tactic hints:**
- `apply tendsto_of_tendsto_of_tendsto_of_le_of_le` — squeeze between upper and lower bounds
- `intro p hp` — for $\epsilon$-$\delta$ arguments with the filter
- `calc eLpNorm f p μ ≤ ...` — for the upper bound chain
- `gcongr` — for monotonicity of integrals and powers
- `simp [eLpNorm_top_eq_essSup]` — relating $||f||_\infty$ to essSup
- `positivity` — for $m(E_c) > 0$ and exponent positivity
- `exact?` — finding the Hölder embedding lemma
- `nlinarith` — combining the $\epsilon$ bounds in the squeeze
- `filter_upwards` — for "for $p$ large enough" arguments