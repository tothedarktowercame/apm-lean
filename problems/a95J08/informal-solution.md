# APM a95J08: Young's convolution inequality — $f \in L^{1}$, $g \in Lp$ implies $f*g \in Lp$

## 1. Informal proof

**Why it's hard.** Part (a) requires showing that the integrand $f(x-y)g(y)$ is in $L^{1}(dy)$ for a.e. $x$ — this is a Fubini-type statement that requires establishing joint measurability and integrability in the product. Part (b) is Young's inequality for the case $(1, p, p)$, which requires either Minkowski's integral inequality or a Hölder/Fubini argument.

**The key insight.** Write $|f(x-y)g(y)| = |f(x-y)|^{1/q} \cdot (|f(x-y)|^{1/p} |g(y)|)$ where $1/p + 1/q = 1$. Apply Hölder in $y$: the first factor has $Lq$ norm $= ||f||_{1}^{1/q}$, the second factor has $Lp$ norm controlled by $||f||_{1}^{1/p} ||g||_p$. This gives the pointwise bound and, after integrating in $x$, Young's inequality.

Alternatively, use Minkowski's integral inequality directly.

**Proof.**

**(a) $f(x-\cdot)g(\cdot) \in L^{1}$ for a.e. $x$.**

By Tonelli's theorem (applied to the nonneg function $|f(x-y)||g(y)|$):

$\int\int |f(x-y)||g(y)| dy dx = \int |g(y)| (\int |f(x-y)| dx) dy = \int |g(y)| \cdot ||f||_{1} dy = ||f||_{1} \cdot ||g||_{1}$.

Wait — this gives $L^{1}$ integrability but we need $g \in Lp$, not $L^{1}$. Let me redo.

Actually, for part (a) we just need to show $\int |f(x-y)g(y)| dy < \infty$ for a.e. $x$. Apply Hölder in $y$:

$\int |f(x-y)g(y)| dy \leq (\int |f(x-y)| dy)^{1/q} \cdot (\int |f(x-y)||g(y)|^p dy)^{1/p}$

$= ||f||_{1}^{1/q} \cdot (\int |f(x-y)||g(y)|^p dy)^{1/p}$.

The second factor is finite for a.e. $x$ by Tonelli:

$\int (\int |f(x-y)||g(y)|^p dy) dx = \int |g(y)|^p (\int |f(x-y)| dx) dy = ||f||_{1} \cdot ||g||_p^p < \infty$.

So $\int |f(x-y)||g(y)|^p dy < \infty$ for a.e. $x$, making the Hölder bound finite. ✓

**(b) $||h||_p \leq ||f||_{1} \cdot ||g||_p$.**

From part (a): $|h(x)| \leq ||f||_{1}^{1/q} \cdot (\int |f(x-y)||g(y)|^p dy)^{1/p}$.

Raising to the $p$-th power and integrating:

$\int |h(x)|^p dx \leq ||f||_{1}^{p/q} \cdot \int (\int |f(x-y)||g(y)|^p dy) dx$

$= ||f||_{1}^{p/q} \cdot ||f||_{1} \cdot ||g||_p^p$ (by Tonelli, as above)

$= ||f||_{1}^{p/q + 1} \cdot ||g||_p^p$

$= ||f||_{1}^p \cdot ||g||_p^p$ (since $p/q + 1 = p(1-1/p) + 1 = p-1+1 = p$).

Taking $p$-th roots: $||h||_p \leq ||f||_{1} \cdot ||g||_p$. ✓ ∎

**What connects.** This is Young's convolution inequality in the special case $||f*g||_p \leq ||f||_{1} \cdot ||g||_p$ (the exponents satisfy $1 + 1/p = 1/1 + 1/p$). The general form is $||f*g||_r \leq ||f||_p \cdot ||g||_q$ where $1/p + 1/q = 1 + 1/r$. The proof technique — splitting the integrand via Hölder with a carefully chosen factorisation $|f|^{1/q} \cdot |f|^{1/p}|g|$, then applying Tonelli to the "heavy" factor — is the standard Minkowski/Young argument. Part (a) is the "well-definedness" step that is often swept under the rug but is essential: the convolution is only defined a.e., and Fubini/Tonelli justifies this. The result is fundamental to harmonic analysis (approximate identities, mollifiers) and PDE (solution operators via convolution with fundamental solutions).

## 2. Lean 4 theorem statement

```lean
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.MeanInequalities

open MeasureTheory Set Filter

noncomputable section

/-- The convolution h = f * g. -/
def convolution (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, f (x - y) * g y ∂volume

/-- (a) The integrand f(x-·)g(·) is in L¹ for a.e. x. -/
theorem convolution_integrand_integrableAE
    {f g : ℝ → ℝ}
    {p : ℝ≥0∞} (hp : 1 < p) (hp' : p ≠ ⊤)
    (hf : Integrable f volume)
    (hg : Memℒp g p volume) :
    ∀ᵐ x ∂volume,
      Integrable (fun y => f (x - y) * g y) volume := by
  sorry

/-- (b) Young's inequality: ‖f * g‖_p ≤ ‖f‖₁ · ‖g‖_p. -/
theorem young_convolution_inequality
    {f g : ℝ → ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hf : Integrable f volume)
    (hfm : AEStronglyMeasurable f volume)
    (hg : Memℒp g p volume)
    (hgm : AEStronglyMeasurable g volume) :
    eLpNorm (convolution f g) p volume ≤
      eLpNorm f 1 volume * eLpNorm g p volume := by
  sorry

/-- The convolution is in Lp. -/
theorem convolution_memLp
    {f g : ℝ → ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hf : Integrable f volume)
    (hfm : AEStronglyMeasurable f volume)
    (hg : Memℒp g p volume)
    (hgm : AEStronglyMeasurable g volume) :
    Memℒp (convolution f g) p volume := by
  sorry

/-- Hölder step: |h(x)| ≤ ‖f‖₁^{1/q} · (∫|f(x-y)||g(y)|^p dy)^{1/p}. -/
lemma convolution_pointwise_holder_bound
    {f g : ℝ → ℝ}
    {p : ℝ≥0∞} (hp : 1 < p) (hp' : p ≠ ⊤)
    (hf : Integrable f volume) (hfnn : ∀ x, 0 ≤ f x)
    (x : ℝ)
    (hx : Integrable (fun y => f (x - y) * g y) volume) :
    ‖convolution f g x‖ ≤
      (∫ y, ‖f (x - y)‖ ∂volume) ^ (1 - 1 / p.toReal) *
      (∫ y, ‖f (x - y)‖ * ‖g y‖ ^ p.toReal ∂volume) ^ (1 / p.toReal) := by
  sorry

/-- Tonelli/Fubini step: ∫∫|f(x-y)||g(y)|^p dy dx = ‖f‖₁ · ‖g‖_p^p. -/
lemma tonelli_convolution_step
    {f g : ℝ → ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hf : Integrable f volume) (hfm : Measurable f)
    (hg : Memℒp g p volume) (hgm : Measurable g) :
    ∫ x, (∫ y, ‖f (x - y)‖ * ‖g y‖ ^ p.toReal ∂volume) ∂volume =
      (∫ y, ‖f y‖ ∂volume) * ∫ y, ‖g y‖ ^ p.toReal ∂volume := by
  sorry

/-- Translation invariance: ∫|f(x-y)| dx = ‖f‖₁ for all y. -/
lemma integral_translate_norm
    {f : ℝ → ℝ} (hf : Integrable f volume) (y : ℝ) :
    ∫ x, ‖f (x - y)‖ ∂volume = ∫ x, ‖f x‖ ∂volume := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `MeasureTheory.Integrable f volume` — $f \in L^{1}$
- `MeasureTheory.Memℒp g p volume` — $g \in Lp$
- `MeasureTheory.eLpNorm f p volume` — Lp seminorm
- `AEStronglyMeasurable` — measurability
- `ENNReal.toReal` — converting exponent to $\mathbb{R}$

**Key lemmas:**
- `MeasureTheory.integral_mul_le_Lp_mul_Lq` — Hölder's inequality: $\int|fg| \leq ||f||_p \cdot ||g||_q$. Used in the pointwise bound
- `MeasureTheory.lintegral_lintegral_swap` / `MeasureTheory.Measure.integral_prod` — Fubini/Tonelli for swapping integrals
- `MeasureTheory.integral_sub_left_eq_self` — translation invariance of Lebesgue integral: $\int f(x-y)dx = \int f(x)dx$
- `MeasureTheory.norm_integral_le_integral_norm` — $|\int fg| \leq \int|fg|$
- `MeasureTheory.integral_nonneg` — nonneg integrands give nonneg integrals
- `ENNReal.toReal_add` / `ENNReal.one_toReal` — arithmetic with the Lp exponent
- `Real.rpow_add`, `Real.rpow_mul` — power function arithmetic for $p/q+1=p$

**Tactic hints:**
- `calc ‖convolution f g x‖ ≤ ...` — Hölder pointwise bound chain
- `rw [integral_mul_le_Lp_mul_Lq]` — applying Hölder
- `rw [lintegral_lintegral_swap]` — swapping order of integration
- `simp [integral_translate_norm hf]` — translation invariance
- `gcongr` — monotonicity steps
- `positivity` — for exponents
- `field_simp` — for $p/q + 1 = p$ arithmetic
- `nlinarith [ENNReal.toReal_pos hp.ne' hp']` — exponent relations
- `exact?` — finding Hölder or Fubini in Mathlib