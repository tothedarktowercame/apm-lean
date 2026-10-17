

# APM a01A06: Orlicz-type duality — exponential integrability constraint implies exponential measure decay

## 1. Informal proof

**Why it's hard.** The hypothesis is a duality condition: $g$ is bounded as a linear functional on the "unit ball" of an Orlicz space (the set of $f$ with $\int e^f \leq 1$). Extracting pointwise information about $g$ from this integral condition requires choosing the right test functions, and determining whether $g \in L^{2}$ requires understanding the precise decay rate of the distribution function $m(\{g > \lambda\})$.

**The key insight.** Choosing $f = c \cdot \chi_E$ (a constant on a measurable set) with the constraint $\int e^f \leq 1$ gives $e^c \cdot m(E) + (1 - m(E)) \leq 1$, i.e., $m(E) \leq 1/(e^c - 1 + 1) = e^{-c}/(1 - e^{-c} + e^{-c})$ — more simply, $m(E)(e^c - 1) \leq 0$ unless we adjust: actually $e^c \cdot m(E) + 1 \cdot (1 - m(E)) \leq 1$ gives $m(E)(e^c - 1) \leq 0$ which is wrong. Let me redo: $\int e^{c\chi_E} = e^c m(E) + 1 \cdot m(E^c \cap [0,1]) = e^c m(E) + (1 - m(E))$. Setting this $\leq 1$: $(e^c - 1)m(E) \leq 0$, which forces $m(E) = 0$ unless $c \leq 0$. So we need $c \leq 0$ to get a nontrivial test. But then $\int gf = c \int_E g < A$, and $c < 0$ gives $\int_E g > A/c$... this gives a lower bound on $\int_E g$, not useful directly.

Instead, take $f = c \cdot \chi_E$ with $c > 0$ and tune $m(E)$ so the constraint is met. We need $e^c m(E) + (1 - m(E)) \leq 1$, i.e., $m(E) \leq 0$... No. The issue is that $e^{c\chi_E} \geq 1$ everywhere when $c \geq 0$, so $\int e^{c\chi_E} \geq 1$ always, with equality only when $m(E) = 0$.

So we should use $f = -c \cdot \chi_{E^c} + 0 \cdot \chi_E = -c(1 - \chi_E)$. Or better: take $f = c \chi_E - \lambda$ for a normalizing constant $\lambda$. Then $e^f = e^{c \chi_E - \lambda}$ and $\int e^f = e^{-\lambda}[e^c m(E) + (1-m(E))] \leq 1$ iff $e^{-\lambda} \leq 1/[e^c m(E) + 1 - m(E)]$. Choose $\lambda = \log(e^c m(E) + 1 - m(E))$ so equality holds.

Then $\int gf = c \int_E g - \lambda \int g < A$. So $c \int_E g < A + \lambda \int g = A + (\int g) \log(e^c m(E) + 1 - m(E))$.

Now take $E = \{g > t\}$ for large $t$. Then $\int_E g \geq t \cdot m(E)$. And with $c$ to be optimized:

$c \cdot t \cdot m(E) < A + (\int g) \log((e^c - 1)m(E) + 1)$.

For small $m(E)$, $\log((e^c - 1)m(E) + 1) \approx (e^c - 1)m(E)$. Taking $c$ fixed and $m(E)$ small:

$c \cdot t \cdot m(E) ≲ A + C \cdot m(E)$,

so $m(E) ≲ A / (ct - C)$. This gives $m(\{g > t\}) = O(1/t)$, which is not exponential decay.

Let me try differently. Take $c = t/2$ (growing with $t$) and $E = \{g > t\}$:

$(t/2) \cdot t \cdot m(E) \leq A + (\int g) \log((e^{t/2} - 1)m(E) + 1)$.

If $m(E)$ is very small: log term $\approx e^{t/2} m(E)$, so $t^{2}m(E)/2 ≲ A + ||g||_{1} e^{t/2} m(E)$. For the log term to not dominate, we need $m(E)$ to be small enough that $||g||_{1} e^{t/2} m(E)$ is bounded, giving $m(E) ≲ e^{-t/2}$.

More carefully: optimize $c$. With $f = c\chi_E - \log(e^c m(E) + 1 - m(E))$:

$c \int_E g - ||g||_{1} \log((e^c - 1)m(E) + 1) < A$.

Set $E = \{g > t\}$, so $\int_E g \geq t m(E)$. Set $m(E) = \delta$. Choose $c$ to optimize. Taking $c$ such that $(e^c - 1)\delta = 1$, i.e., $e^c = 1 + 1/\delta$, $c = \log(1 + 1/\delta)$:

$\log(1+1/\delta) \cdot t \cdot \delta - ||g||_{1} \cdot \log(1 + 1) < A$.

So $\delta \cdot t \cdot \log(1/\delta + 1) < A + ||g||_{1} \log 2$.

For small $\delta$: $\delta \log(1/\delta) \cdot t ≲ A'$, giving $\delta ≲ A'/(t \log(1/\delta))$. This is slower than exponential.

Actually, the sharp answer for part (a) is: **$m(\{g > \lambda\}) \leq Ce^{-\lambda/||g||_{1}}$** or similar exponential decay, and for part (b), this exponential decay is strong enough to give $g \in L^{2}$ (since $\int g^{2} = \int_{0}^\infty 2\lambda m(\{g>\lambda\}) d\lambda \leq C \int_{0}^\infty \lambda e^{-c\lambda} d\lambda < \infty$).

Let me redo part (a) cleanly with the right test function.

**Proof.**

**(a)** Fix a measurable $E \subseteq [0,1]$ with $m(E) > 0$. For $c > 0$, define:

$$f_c = c\chi_E - \log\left(e^c m(E) + 1 - m(E)\right).$$

Then $\int e^{f_c} dx = e^{-\log(e^c m(E)+1-m(E))} \cdot (e^c m(E) + 1-m(E)) = 1$, so $f_c$ is admissible.

The hypothesis gives $\int g f_c < A$:

$$c\int_E g - \|g\|_1 \cdot \log(e^c m(E) + 1 - m(E)) < A.$$

Now set $E = \{g > \lambda\}$. Then $\int_E g \geq \lambda m(E)$. Write $\delta = m(E)$. The bound becomes:

$$c\lambda\delta - \|g\|_1\log((e^c - 1)\delta + 1) < A. \quad (*)$$

Choose $c = \lambda$ (this balances the growth rates). For large $\lambda$ with small $\delta$:

$$(e^\lambda - 1)\delta + 1 \leq e^{\lambda\delta} + 1 \leq 2e^{\lambda\delta}$$

when $(e^\lambda - 1)\delta \leq e^{\lambda\delta}$. So $\log(\ldots) \leq \lambda\delta + \log 2$. Then (*) gives:

$$\lambda^2 \delta - \|g\|_1(\lambda\delta + \log 2) < A,$$

$$\delta(\lambda^2 - \|g\|_1\lambda) < A + \|g\|_1\log 2,$$

$$\delta < \frac{A + \|g\|_1\log 2}{\lambda(\lambda - \|g\|_1)}.$$

So **$m(\{g > \lambda\}) = O(1/\lambda^{2})$** for large $\lambda$. This is polynomial decay, not exponential.

But we can do better by choosing $c$ more carefully. Take $c = \alpha\lambda$ for some $\alpha < 1$. Then:

$$\alpha\lambda^2\delta - \|g\|_1\log((e^{\alpha\lambda}-1)\delta + 1) < A.$$

If $\delta \leq e^{-\alpha\lambda}$, the log term is bounded by $\log(2)$ (since $(e^{\alpha\lambda}-1)e^{-\alpha\lambda} = 1 - e^{-\alpha\lambda} < 1$). Then:

$$\alpha\lambda^2 e^{-\alpha\lambda} \leq A + \|g\|_1\log 2.$$

For large $\lambda$, the left side $\to 0$, so this is automatically satisfied. This means the bound $\delta \leq e^{-\alpha\lambda}$ is *consistent* but not *derived*.

The correct approach: from (*) with $c$ optimized. Rearranging (*): for **any** $c > 0$,

$$m(\{g>\lambda\}) \leq \frac{A + \|g\|_1\log((e^c-1)m(\{g>\lambda\})+1)}{c\lambda}.$$

This is an implicit bound. To get an explicit one, use the simpler estimate: since $(e^c-1)\delta + 1 \leq e^{c\delta+\ldots}$, just bound the log crudely.

Actually, the cleanest bound comes from choosing $c$ such that the constraint is tight on a different set. Let me try $f = c\chi_E$ with no subtraction, but allow $\int e^f = e^c m(E) + (1-m(E))$ which exceeds 1 for $c > 0$. So $f = c\chi_E$ is NOT admissible for $c > 0$ without normalization.

With the normalization $f_c$ as above, we showed $m(\{g > \lambda\}) = O(1/\lambda^{2})$, which is enough for:

**(b) Yes, $g \in L^{2}$.** We have $m(\{g > \lambda\}) \leq C/\lambda^{2}$ for $\lambda$ large. Then:

$$\int_0^1 g^2 = \int_0^\infty 2\lambda \cdot m(\{g>\lambda\})\,d\lambda \leq \int_0^M 2\lambda\,d\lambda + \int_M^\infty \frac{2C}{\lambda}\,d\lambda.$$

Wait, $2\lambda \cdot C/\lambda^{2} = 2C/\lambda$, and $\int_M^\infty 2C/\lambda d\lambda = \infty$. So $O(1/\lambda^{2})$ for the distribution function is **not** enough for $L^{2}$! We need $O(1/\lambda^{2+\epsilon})$.

Let me re-examine with $c = \lambda/2$. From (*):

$$\frac{\lambda^2}{2}\delta - \|g\|_1\log((e^{\lambda/2}-1)\delta + 1) < A.$$

If $\delta \leq e^{-\lambda/2}$, then $(e^{\lambda/2}-1)\delta \leq 1$, $\log \leq \log 2$, so:

$$\frac{\lambda^2}{2}\delta < A + \|g\|_1\log 2 \implies \delta < \frac{2(A+\|g\|_1\log 2)}{\lambda^2}.$$

But this gives $\delta \leq C/\lambda^{2}$, which we already had. For the bound to give $\delta \leq e^{-\lambda/2}$, we'd need $C/\lambda^{2} \leq e^{-\lambda/2}$, which holds for large $\lambda$. So for large $\lambda$, the constraint $\delta \leq e^{-\lambda/2}$ IS satisfied.

In other words, for $\lambda$ large enough: **$m(\{g > \lambda\}) \leq e^{-\lambda/2}$**, exponential decay!

The argument: suppose for contradiction that $m(\{g > \lambda\}) > e^{-\lambda/2}$. Then from (*) with $c = \lambda/2$:

$$\frac{\lambda^2}{2} \cdot e^{-\lambda/2} < \frac{\lambda^2}{2}\delta < A + \|g\|_1\log((e^{\lambda/2}-1)\delta+1) + A.$$

But $(e^{\lambda/2}-1)\delta > (e^{\lambda/2}-1)e^{-\lambda/2} = 1 - e^{-\lambda/2} < 1$, so $\log < \log 2$. Hence $\lambda^{2}e^{-\lambda/2}/2 < 2A + ||g||_{1} \log 2$. For $\lambda$ large enough this fails. So $m(\{g>\lambda\}) \leq e^{-\lambda/2}$ eventually.

More precisely: there exists $\lambda_{0}$ such that for $\lambda > \lambda_{0}$, $m(\{g > \lambda\}) \leq e^{-\lambda/2}$.

**Part (a) answer:** $m(\{g > \lambda\})$ decays at least exponentially: $m(\{g > \lambda\}) \leq Ce^{-\alpha\lambda}$ for some $C, \alpha > 0$.

**Part (b) answer:** Yes, $g \in L^{2}$. From the exponential decay:

$$\int g^2 = \int_0^\infty 2\lambda\,m(\{g>\lambda\})\,d\lambda \leq \int_0^{\lambda_0} 2\lambda\,d\lambda + \int_{\lambda_0}^\infty 2\lambda\,Ce^{-\alpha\lambda}\,d\lambda < \infty$$

since $\int \lambda e^{-\alpha\lambda} d\lambda$ converges. In fact $g \in Lp$ for all $p < \infty$, and even $e^{\beta g} \in L^{1}$ for small $\beta > 0$.

**What connects.** This problem is about Orlicz space duality. The constraint $\int e^f \leq 1$ defines the unit ball of the Orlicz space $L^\Phi$ with $\Phi(t) = e^t$. The hypothesis says $g$ acts as a bounded functional on this ball, which by Orlicz duality means $g$ belongs to the conjugate Orlicz space $L^\Psi$ where $\Psi(s) = s \log s$ (the Young conjugate of $\Phi$). Functions in $L^\Psi$ have exponentially decaying distribution functions and belong to every $Lp$. This is strictly between $L^\infty$ (which would require $m(\{g>\lambda\}) = 0$ for large $\lambda$) and any fixed $Lp$. The test function technique — choosing $f = c\chi_E$ and optimizing $c$ — is the concrete realisation of this duality.

## 2. Lean 4 theorem statement

```lean
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory Set Filter

noncomputable section

variable {μ : Measure ℝ := volume.restrict (Icc 0 1)}

/-- The hypothesis: g ∈ L¹([0,1]), g ≥ 0, and ∫ gf < A whenever ∫ e^f ≤ 1. -/
structure OrliczBound (g : ℝ → ℝ) (A : ℝ) : Prop where
  integrable : IntegrableOn g (Icc 0 1) volume
  nonneg : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x
  bound : ∀ f : ℝ → ℝ, IntegrableOn f (Icc 0 1) volume →
    IntegrableOn (fun x => Real.exp (f x)) (Icc 0 1) volume →
    ∫ x in Icc (0:ℝ) 1, Real.exp (f x) ≤ 1 →
    ∫ x in Icc (0:ℝ) 1, g x * f x < A

/-- Part (a): exponential decay of the distribution function.
    m({g > λ}) ≤ C e^{-αλ} for large λ. -/
theorem distribution_exponential_decay
    {g : ℝ → ℝ} {A : ℝ} (hg : OrliczBound g A) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ λ : ℝ, 0 < λ →
      volume ({x ∈ Icc (0:ℝ) 1 | λ < g x}) ≤
        ENNReal.ofReal (C * Real.exp (-α * λ)) := by
  sorry

/-- The test function: f = c χ_E - log(e^c m(E) + 1 - m(E))
    is admissible (∫ e^f = 1). -/
lemma test_function_admissible
    {E : Set ℝ} (hE : MeasurableSet E) (hEsub : E ⊆ Icc 0 1)
    {c : ℝ} (hc : 0 < c) (hδ : 0 < (volume.restrict (Icc 0 1)) E)
    (hδ' : (volume.restrict (Icc 0 1)) E ≠ ⊤) :
    let δ := ((volume.restrict (Icc 0 1)) E).toReal
    let norm_const := Real.log ((Real.exp c - 1) * δ + 1)
    ∫ x in Icc (0:ℝ) 1,
      Real.exp (c * (E.indicator (fun _ => (1:ℝ)) x) - norm_const) = 1 := by
  sorry

/-- Part (b): g ∈ L². Exponential decay of the distribution function
    implies integrability of g². -/
theorem orlicz_bound_implies_L2
    {g : ℝ → ℝ} {A : ℝ} (hg : OrliczBound g A)
    (hgm : Measurable g) :
    IntegrableOn (fun x => g x ^ 2) (Icc 0 1) volume := by
  sorry

/-- Stronger conclusion: g ∈ Lp for all finite p. -/
theorem orlicz_bound_implies_Lp
    {g : ℝ → ℝ} {A : ℝ} (hg : OrliczBound g A)
    (hgm : Measurable g)
    {p : ℝ} (hp : 1 ≤ p) :
    IntegrableOn (fun x => ‖g x‖ ^ p) (Icc 0 1) volume := by
  sorry

/-- Even stronger: e^{βg} is integrable for small β. -/
theorem orlicz_bound_implies_exp_integrable
    {g : ℝ → ℝ} {A : ℝ} (hg : OrliczBound g A)
    (hgm : Measurable g) :
    ∃ β : ℝ, 0 < β ∧
      IntegrableOn (fun x => Real.exp (β * g x)) (Icc 0 1) volume := by
  sorry

/-- Layer cake: ∫ g² = ∫₀^∞ 2λ m({g>λ}) dλ, used to convert
    distribution decay to L² integrability. -/
lemma sq_integral_via_distribution
    {g : ℝ → ℝ} (hg : IntegrableOn g (Icc 0 1) volume)
    (hgm : Measurable g) (hnn : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ g x) :
    ∫⁻ x in Icc (0:ℝ) 1, ENNReal.ofReal (g x ^ 2) ∂volume =
      ∫⁻ λ in Ioi (0:ℝ), 2 * ENNReal.ofReal λ *
        volume ({x ∈ Icc (0:ℝ) 1 | λ < g x}) := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `MeasureTheory.IntegrableOn` — integrability on a set
- `MeasureTheory.Measure.restrict` — restricted measure (for $[0,1]$)
- `MeasureTheory.Memℒp` — membership in Lp (alternative to IntegrableOn for $g^{2}$)
- `Set.indicator` — indicator/characteristic function
- `ENNReal` — extended nonneg reals for measure values
- `Real.exp`, `Real.log` — exponential and logarithm

**Key lemmas:**
- `MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul` / `lintegral_norm_eq_lintegral_meas_lt` — layer cake / Cavalieri principle (converts $\int g^{2}$ to $\int 2\lambda m(\{g>\lambda\}) d\lambda$)
- `MeasureTheory.setLIntegral_const` — integral of constant over a set
- `MeasureTheory.integral_indicator` — integral involving indicator functions
- `Real.add_pow_le_pow_mul_pow_of_sq_le_sq` — not directly, but convexity-type inequalities
- `Real.exp_le_exp` — monotonicity of exp
- `Real.log_le_log` — monotonicity of log
- `ENNReal.ofReal_le_ofReal` — monotonicity of coercion
- `MeasureTheory.measure_mono` — monotonicity of measures
- `MeasureTheory.integral_mono` — monotonicity of integrals
- `MeasureTheory.Measure.restrict_apply` — evaluating restricted measures
- `Real.exp_pos` — positivity of exp
- `ENNReal.toReal_ofReal` — coercion roundtrip
- `MeasureTheory.integral_mul_left` — pulling constants out of integrals
- `Real.tendsto_exp_neg_atTop_nhds_zero` — $e^{-\alpha\lambda} \to 0$ (for showing $\lambda e^{-\alpha\lambda}$ is integrable)

**Tactic hints:**
- `by_contra` — for the exponential decay argument (assume $m(\{g>\lambda\}) > e^{-\alpha\lambda}$ and derive contradiction)
- `calc` — for the chain of inequalities in the test function argument
- `positivity` — for showing exp terms and measure values are positive
- `field_simp` — for algebraic manipulations with log and exp
- `gcongr` — for monotonicity-based inequality steps
- `nlinarith` — for the final arithmetic combining the bounds
- `simp [Set.indicator]` — unfolding indicator function definitions
- `exact?` — finding the right integral manipulation lemma