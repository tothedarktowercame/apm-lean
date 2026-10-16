

# APM a01A02: Weak-$L^{2}$ implies local $L^{1}$ with the right bound

## Why It's Hard

The hypothesis is a *distributional* (weak-type) bound on $f$ — it controls how much measure lives above each height $\lambda$ — and the conclusion is an *integral* bound on arbitrary Borel sets. The difficulty is converting a tail-decay condition into an integral estimate, with the correct dependence on $m(E)$. The exponent $1/2$ in $\sqrt{m(E)}$ is not obvious and emerges from optimizing a free parameter in a truncation argument. This is the same circle of ideas as a03J04 (b)/(c) — weak-$L^p$ implies local $L^q$ for $q < p$ — specialized to $p = 2$, $q = 1$.

## The Key Insight

Split $|f|$ at a height $\lambda_{0}$ (to be optimized): the part below $\lambda_{0}$ is bounded, so its integral over $E$ is at most $\lambda_{0} \cdot m(E)$. The part above $\lambda_{0}$ is handled by the layer cake formula + the weak-$L^{2}$ bound, giving an integral of order $C/\lambda_{0}$. Choose $\lambda_{0} = \sqrt{C/m(E)}$ to balance the two terms, yielding $\int_E |f| \leq \text{const} \cdot \sqrt{C \cdot m(E)}$.

## Complete Proof

**Theorem.** Let $f : \mathbb{R}^{n} \to \mathbb{R}$ be measurable with $m(\{|f| > \lambda\}) \leq C \lambda^{-2}$ for all $\lambda > 0$ (weak-$L^{2}$ condition). Then for any Borel set $E$ with $0 < m(E) < \infty$:

$$\int_E |f|\,dx \leq C_1\sqrt{m(E)},$$

where $C_{1} = 2\sqrt{C}$.

**Proof.**

Fix a Borel set $E$ with $0 < m(E) < \infty$, and fix a parameter $\lambda_{0} > 0$ (to be chosen later). Write:

$$|f(x)| = |f(x)|\mathbf{1}_{|f(x)| \leq \lambda_0} + |f(x)|\mathbf{1}_{|f(x)| > \lambda_0} =: g(x) + h(x).$$

**Low part.** On $E$, $g(x) \leq \lambda_{0}$ pointwise, so:

$$\int_E g\,dx \leq \lambda_0 \cdot m(E).$$

**High part.** Use the layer cake (Cavalieri) formula:

$$\int_E h\,dx = \int_E |f|\mathbf{1}_{|f| > \lambda_0}\,dx.$$

We bound this by integrating over all of $\mathbb{R}^{n}$ (since $h \geq 0$):

$$\int_E h\,dx \leq \int_{\mathbb{R}^n} h\,dx = \int_0^\infty m(\{x : h(x) > \lambda\})\,d\lambda.$$

Now $\{h(x) > \lambda\} = \{|f(x)| \cdot 1_{|f|>\lambda_{0}} > \lambda\}$. For $\lambda \geq 0$:

- If $\lambda \geq \lambda_{0}$: $\{h > \lambda\} = \{|f| > \lambda\}$, so $m(\{h > \lambda\}) \leq C \lambda^{-2}$.
- If $0 \leq \lambda < \lambda_{0}$: $\{h > \lambda\} \subseteq \{|f| > \lambda_{0}\}$, so $m(\{h > \lambda\}) \leq C \lambda_{0}^{-2}$.

But we can be tighter. Actually:

$$\int_{\mathbb{R}^n} h\,dx = \int_{\lambda_0}^{\infty} m(\{|f| > \lambda\})\,d\lambda$$

This follows because $h(x) = (|f(x)| - \lambda_{0})^{+}$ ... no, $h(x) = |f(x)| \cdot 1_{|f| > \lambda_{0}}$, which is not the same as $(|f| - \lambda_{0})^{+}$. Let me use a cleaner calculation.

Apply the layer cake directly to $\int_E |f|$:

$$\int_E |f|\,dx = \int_0^{\infty} m(E \cap \{|f| > \lambda\})\,d\lambda.$$

Split at $\lambda_{0}$:

$$= \int_0^{\lambda_0} m(E \cap \{|f| > \lambda\})\,d\lambda + \int_{\lambda_0}^{\infty} m(E \cap \{|f| > \lambda\})\,d\lambda.$$

**First integral:** $m(E \cap \{|f| > \lambda\}) \leq m(E)$ for all $\lambda$, so:

$$\int_0^{\lambda_0} m(E \cap \{|f| > \lambda\})\,d\lambda \leq \lambda_0 \cdot m(E).$$

**Second integral:** $m(E \cap \{|f| > \lambda\}) \leq m(\{|f| > \lambda\}) \leq C \lambda^{-2}$ for all $\lambda > 0$, so:

$$\int_{\lambda_0}^{\infty} m(E \cap \{|f| > \lambda\})\,d\lambda \leq \int_{\lambda_0}^{\infty} C\lambda^{-2}\,d\lambda = C\left[-\lambda^{-1}\right]_{\lambda_0}^{\infty} = \frac{C}{\lambda_0}.$$

**Combining:**

$$\int_E |f|\,dx \leq \lambda_0 \cdot m(E) + \frac{C}{\lambda_0}.$$

**Optimize over $\lambda_{0}$.** Set the derivative to zero: $m(E) - C/\lambda_{0}^{2} = 0$, giving $\lambda_{0} = \sqrt{C/m(E)}$. Substituting:

$$\int_E |f|\,dx \leq \sqrt{\frac{C}{m(E)}} \cdot m(E) + \frac{C}{\sqrt{C/m(E)}} = \sqrt{C \cdot m(E)} + \sqrt{C \cdot m(E)} = 2\sqrt{C \cdot m(E)}.$$

So $C_{1} = 2\sqrt{C}$, and:

$$\boxed{\int_E |f|\,dx \leq 2\sqrt{C}\,\sqrt{m(E)}.} \qquad \blacksquare$$

## What Connects

**To weak-$L^p$ spaces and interpolation.** This is a special case of the general principle: weak-$L^p$ on a $\sigma$-finite measure space implies $L^q$ on sets of finite measure for any $q < p$. The exponent in $\sqrt{m(E)} = m(E)^{1/1 - 1/2 + 1/1}$... more precisely, for weak-$L^p$, the bound is $\int_E |f|^q \leq C(p,q) \cdot m(E)^{1 - q/p}$ for $0 < q < p$. Here $p = 2$, $q = 1$: exponent $= 1 - 1/2 = 1/2$. This was problem a03J04(b)/(c) in general form.

**To the Marcinkiewicz interpolation theorem.** The splitting trick (truncate at a height, bound each piece differently) is the core of the Marcinkiewicz interpolation argument. The optimization over the truncation level is what produces the sharp constant and the correct exponent.

**To Chebyshev's inequality and its converse.** The weak-$L^{2}$ condition $m(\{|f| > \lambda\}) \leq C/\lambda^{2}$ is Chebyshev's inequality applied to $|f|^{2}$ if $f \in L^{2}$. But the hypothesis here is weaker: $f$ need not be in $L^{2}$. The conclusion shows that despite not being globally $L^{1}$, $f$ is locally $L^{1}$ with a specific rate.

**To real-variable harmonic analysis.** The Calderón-Zygmund decomposition and the good-$\lambda$ inequality both rely on exactly this kind of distributional → integral conversion, with optimization over a free parameter.

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

- `WeakL2` encodes the distributional bound $m(\{|f| > \lambda\}) \leq C/\lambda^{2}$ using `ENNReal.ofReal` for the real-to-ennreal coercion. The level set uses `‖f x‖` (which equals `|f x|` for real-valued functions).
- The layer cake decomposition $\int_E |f| = \int_{0}^\infty m(E \cap \{|f|>\lambda\})\, d\lambda$ is available via `MeasureTheory.lintegral_norm_eq_lintegral_meas_lt` or the Layercake file.
- The main theorem `weakL2_integral_bound` uses the Bochner integral `∫ x in E, ‖f x‖ ∂μ` (real-valued) rather than the lintegral, since the conclusion is a real inequality. The lintegral version `integral_le_optimized` is the intermediate step.
- `(μ E).toReal` coerces the measure from `ℝ≥0∞` to `ℝ`, which is valid since `hEfin : μ E ≠ ⊤`.
- The constant $C_{1} = 2\sqrt{C}$ is explicit. The proof chain is: layer cake split → bound each piece → optimize $\lambda_{0} = \sqrt{C/m(E)}$ → simplify.
