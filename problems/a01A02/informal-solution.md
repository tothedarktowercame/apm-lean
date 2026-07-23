

# APM a01A02: Weak-L² implies local L¹ with the right bound

## Why It's Hard

The hypothesis is a *distributional* (weak-type) bound on f — it controls how much measure lives above each height λ — and the conclusion is an *integral* bound on arbitrary Borel sets. The difficulty is converting a tail-decay condition into an integral estimate, with the correct dependence on m(E). The exponent 1/2 in √m(E) is not obvious and emerges from optimizing a free parameter in a truncation argument. This is the same circle of ideas as a03J04 (b)/(c) — weak-Lp implies local Lq for q < p — specialized to p = 2, q = 1.

## The Key Insight

Split |f| at a height λ₀ (to be optimized): the part below λ₀ is bounded, so its integral over E is at most λ₀ · m(E). The part above λ₀ is handled by the layer cake formula + the weak-L² bound, giving an integral of order C/λ₀. Choose λ₀ = √(C/m(E)) to balance the two terms, yielding ∫_E |f| ≤ const · √(C · m(E)).

## Complete Proof

**Theorem.** Let f : ℝⁿ → ℝ be measurable with m({|f| > λ}) ≤ C λ⁻² for all λ > 0 (weak-L² condition). Then for any Borel set E with 0 < m(E) < ∞:

$$\int_E |f|\,dx \leq C_1\sqrt{m(E)},$$

where C₁ = 2√C.

**Proof.**

Fix a Borel set E with 0 < m(E) < ∞, and fix a parameter λ₀ > 0 (to be chosen later). Write:

$$|f(x)| = |f(x)|\mathbf{1}_{|f(x)| \leq \lambda_0} + |f(x)|\mathbf{1}_{|f(x)| > \lambda_0} =: g(x) + h(x).$$

**Low part.** On E, g(x) ≤ λ₀ pointwise, so:

$$\int_E g\,dx \leq \lambda_0 \cdot m(E).$$

**High part.** Use the layer cake (Cavalieri) formula:

$$\int_E h\,dx = \int_E |f|\mathbf{1}_{|f| > \lambda_0}\,dx.$$

We bound this by integrating over all of ℝⁿ (since h ≥ 0):

$$\int_E h\,dx \leq \int_{\mathbb{R}^n} h\,dx = \int_0^\infty m(\{x : h(x) > \lambda\})\,d\lambda.$$

Now {h(x) > λ} = {|f(x)| · 1\_{|f|>λ₀} > λ}. For λ ≥ 0:

- If λ ≥ λ₀: {h > λ} = {|f| > λ}, so m({h > λ}) ≤ C λ⁻².
- If 0 ≤ λ < λ₀: {h > λ} ⊆ {|f| > λ₀}, so m({h > λ}) ≤ C λ₀⁻².

But we can be tighter. Actually:

$$\int_{\mathbb{R}^n} h\,dx = \int_{\lambda_0}^{\infty} m(\{|f| > \lambda\})\,d\lambda$$

This follows because h(x) = (|f(x)| - λ₀)⁺ ... no, h(x) = |f(x)| · 1\_{|f| > λ₀}, which is not the same as (|f| - λ₀)⁺. Let me use a cleaner calculation.

Apply the layer cake directly to ∫\_E |f|:

$$\int_E |f|\,dx = \int_0^{\infty} m(E \cap \{|f| > \lambda\})\,d\lambda.$$

Split at λ₀:

$$= \int_0^{\lambda_0} m(E \cap \{|f| > \lambda\})\,d\lambda + \int_{\lambda_0}^{\infty} m(E \cap \{|f| > \lambda\})\,d\lambda.$$

**First integral:** m(E ∩ {|f| > λ}) ≤ m(E) for all λ, so:

$$\int_0^{\lambda_0} m(E \cap \{|f| > \lambda\})\,d\lambda \leq \lambda_0 \cdot m(E).$$

**Second integral:** m(E ∩ {|f| > λ}) ≤ m({|f| > λ}) ≤ C λ⁻² for all λ > 0, so:

$$\int_{\lambda_0}^{\infty} m(E \cap \{|f| > \lambda\})\,d\lambda \leq \int_{\lambda_0}^{\infty} C\lambda^{-2}\,d\lambda = C\left[-\lambda^{-1}\right]_{\lambda_0}^{\infty} = \frac{C}{\lambda_0}.$$

**Combining:**

$$\int_E |f|\,dx \leq \lambda_0 \cdot m(E) + \frac{C}{\lambda_0}.$$

**Optimize over λ₀.** Set the derivative to zero: m(E) - C/λ₀² = 0, giving λ₀ = √(C/m(E)). Substituting:

$$\int_E |f|\,dx \leq \sqrt{\frac{C}{m(E)}} \cdot m(E) + \frac{C}{\sqrt{C/m(E)}} = \sqrt{C \cdot m(E)} + \sqrt{C \cdot m(E)} = 2\sqrt{C \cdot m(E)}.$$

So C₁ = 2√C, and:

$$\boxed{\int_E |f|\,dx \leq 2\sqrt{C}\,\sqrt{m(E)}.} \qquad \blacksquare$$

## What Connects

**To weak-Lp spaces and interpolation.** This is a special case of the general principle: weak-Lp on a σ-finite measure space implies Lq on sets of finite measure for any q < p. The exponent in √m(E) = m(E)^{1/1 - 1/2 + 1/1}... more precisely, for weak-Lp, the bound is ∫_E |f|^q ≤ C(p,q) · m(E)^{1 - q/p} for 0 < q < p. Here p = 2, q = 1: exponent = 1 - 1/2 = 1/2. This was problem a03J04(b)/(c) in general form.

**To the Marcinkiewicz interpolation theorem.** The splitting trick (truncate at a height, bound each piece differently) is the core of the Marcinkiewicz interpolation argument. The optimization over the truncation level is what produces the sharp constant and the correct exponent.

**To Chebyshev's inequality and its converse.** The weak-L² condition m({|f| > λ}) ≤ C/λ² is Chebyshev's inequality applied to |f|² if f ∈ L². But the hypothesis here is weaker: f need not be in L². The conclusion shows that despite not being globally L¹, f is locally L¹ with a specific rate.

**To real-variable harmonic analysis.** The Calderón-Zygmund decomposition and the good-λ inequality both rely on exactly this kind of distributional → integral conversion, with optimization over a free parameter.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory Set ENNReal Filter

noncomputable section

variable {n : ℕ}

/-- The weak-L² condition: m({|f| > λ}) ≤ C/λ² for all λ > 0. -/
def WeakL2 (f : (Fin n → ℝ) → ℝ) (μ : Measure (Fin n → ℝ)) (C : ℝ≥0) : Prop :=
  ∀ λ : ℝ, 0 < λ → μ {x | λ < ‖f x‖} ≤ ENNReal.ofReal (C / λ ^ 2)

/-- Layer cake for the low part: ∫₀^{λ₀} m(E ∩ {|f|>λ}) dλ ≤ λ₀ · m(E). -/
lemma layer_cake_low_bound
    {μ : Measure (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    {E : Set (Fin n → ℝ)} (hE : MeasurableSet E)
    {λ₀ : ℝ} (hλ₀ : 0 < λ₀) :
    ∫⁻ λ in Ioc 0 λ₀,
      μ (E ∩ {x | (λ : ℝ) < ‖f x‖}) ≤
    ENNReal.ofReal λ₀ * μ E := by
  sorry

/-- Layer cake for the high part: ∫_{λ₀}^∞ m(E ∩ {|f|>λ}) dλ ≤ C/λ₀
    under the weak-L² hypothesis. -/
lemma layer_cake_high_bound
    {μ : Measure (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    {C : ℝ≥0} (hf : WeakL2 f μ C)
    {E : Set (Fin n → ℝ)} (hE : MeasurableSet E)
    {λ₀ : ℝ} (hλ₀ : 0 < λ₀) :
    ∫⁻ λ in Ioi λ₀,
      μ (E ∩ {x | (λ : ℝ) < ‖f x‖}) ≤
    ENNReal.ofReal (C / λ₀) := by
  sorry

/-- Combined bound before optimization:
    ∫_E |f| ≤ λ₀ · m(E) + C/λ₀ for any λ₀ > 0. -/
lemma integral_le_split
    {μ : Measure (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hf_meas : Measurable f)
    {C : ℝ≥0} (hf_weak : WeakL2 f μ C)
    {E : Set (Fin n → ℝ)} (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤)
    {λ₀ : ℝ} (hλ₀ : 0 < λ₀) :
    ∫⁻ x in E, ENNReal.ofReal ‖f x‖ ∂μ ≤
      ENNReal.ofReal λ₀ * μ E + ENNReal.ofReal (C / λ₀) := by
  sorry

/-- Optimized bound: choosing λ₀ = √(C/m(E)) gives ∫_E |f| ≤ 2√C · √m(E). -/
lemma integral_le_optimized
    {μ : Measure (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hf_meas : Measurable f)
    {C : ℝ≥0} (hf_weak : WeakL2 f μ C)
    {E : Set (Fin n → ℝ)} (hE : MeasurableSet E)
    (hEfin : μ E ≠ ⊤) (hEpos : 0 < μ E) :
    ∫⁻ x in E, ENNReal.ofReal ‖f x‖ ∂μ ≤
      ENNReal.ofReal (2 * Real.sqrt C) *
        ENNReal.ofReal (Real.sqrt (μ E).toReal) := by
  sorry

/-- Main theorem: weak-L² implies ∫_E |f| ≤ C₁ √m(E)
    for all Borel sets E of finite positive measure. -/
theorem weakL2_integral_bound
    {μ : Measure (Fin n → ℝ)} [SigmaFinite μ]
    {f : (Fin n → ℝ) → ℝ} (hf_meas : Measurable f)
    {C : ℝ≥0} (hf_weak : WeakL2 f μ C)
    {E : Set (Fin n → ℝ)} (hE : MeasurableSet E)
    (hEfin : μ E ≠ ⊤) (hEpos : 0 < μ E) :
    (∫ x in E, ‖f x‖ ∂μ) ≤ 2 * Real.sqrt C * Real.sqrt (μ E).toReal := by
  sorry

/-- Integrability on E follows from the bound. -/
theorem weakL2_integrableOn
    {μ : Measure (Fin n → ℝ)} [SigmaFinite μ]
    {f : (Fin n → ℝ) → ℝ} (hf_meas : Measurable f)
    {C : ℝ≥0} (hf_weak : WeakL2 f μ C)
    {E : Set (Fin n → ℝ)} (hE : MeasurableSet E) (hEfin : μ E ≠ ⊤) :
    IntegrableOn f E μ := by
  sorry

end
```

**Mathlib notes:**

- `WeakL2` encodes the distributional bound m({|f| > λ}) ≤ C/λ² using `ENNReal.ofReal` for the real-to-ennreal coercion. The level set uses `‖f x‖` (which equals `|f x|` for real-valued functions).
- The layer cake decomposition `∫_E |f| = ∫₀^∞ m(E ∩ {|f|>λ}) dλ` is available via `MeasureTheory.lintegral_norm_eq_lintegral_meas_lt` or the Layercake file.
- The main theorem `weakL2_integral_bound` uses the Bochner integral `∫ x in E, ‖f x‖ ∂μ` (real-valued) rather than the lintegral, since the conclusion is a real inequality. The lintegral version `integral_le_optimized` is the intermediate step.
- `(μ E).toReal` coerces the measure from `ℝ≥0∞` to `ℝ`, which is valid since `hEfin : μ E ≠ ⊤`.
- The constant `C₁ = 2√C` is explicit. The proof chain is: layer cake split → bound each piece → optimize λ₀ = √(C/m(E)) → simplify.
