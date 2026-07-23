

# APM a03J03: Convolution of Lp and Lq functions is continuous and vanishes at infinity

## Why It's Hard

Hölder's inequality immediately gives |f*g(x)| ≤ ||f||\_p ||g||\_q, so f*g is bounded. But *continuity* requires showing |f*g(x+h) - f*g(x)| → 0 as h → 0, which amounts to showing ∫|f(x+h-y) - f(x-y)||g(y)| dy → 0. You can't just move the limit inside the integral (no dominated convergence, because you need the Lp translation to converge, not just pointwise). The key tool is **continuity of translation in Lp**: ||τ\_h f - f||\_p → 0 as h → 0 for 1 ≤ p < ∞. This is a nontrivial fact that uses density of compactly supported continuous functions.

The vanishing at infinity is harder still: you need to show the integral ∫ f(x-y)g(y) dy → 0 as |x| → ∞. Intuitively, f(x-·) and g(·) "slide apart" so their overlap shrinks, but making this precise again requires an approximation argument.

## The Key Insight

**Continuity:** By Hölder, |f*g(x+h) - f*g(x)| ≤ ||τ\_h f - f||\_p · ||g||\_q. The factor ||τ\_h f - f||\_p → 0 as h → 0 (continuity of Lp translations), and ||g||\_q is fixed. Done.

**Vanishing at infinity:** Approximate f by a compactly supported function φ with ||f - φ||\_p < ε. Then f*g = φ*g + (f-φ)*g. The second term satisfies ||(f-φ)*g||\_∞ ≤ ||f-φ||\_p ||g||\_q < ε||g||\_q. For the first term, φ*g(x) = ∫ φ(x-y)g(y) dy; since φ is supported on [-R,R], the integrand is nonzero only when |x-y| ≤ R, i.e., y ∈ [x-R, x+R]. For |x| large, g restricted to [x-R, x+R] has small Lq norm (since g ∈ Lq and the interval slides to infinity). So φ*g(x) → 0.

## Complete Proof

**Theorem.** Let 1 < p < ∞, 1/p + 1/q = 1, f ∈ Lp(ℝ), g ∈ Lq(ℝ). Then f*g is continuous on ℝ and f*g(x) → 0 as |x| → ∞.

### Part 1: f*g is well-defined and bounded

By Hölder's inequality, for each x:

$$|f*g(x)| = \left|\int f(x-y)g(y)\,dy\right| \leq \|f(x-\cdot)\|_p\|g\|_q = \|f\|_p\|g\|_q$$

since translation preserves the Lp norm. So f*g is well-defined and bounded by ||f||\_p ||g||\_q. ✓

### Part 2: f*g is continuous

For any x, h ∈ ℝ:

$$|f*g(x+h) - f*g(x)| = \left|\int(f(x+h-y) - f(x-y))g(y)\,dy\right| \leq \|\tau_h f - f\|_p \cdot \|g\|_q$$

by Hölder (where τ\_h f(t) = f(t+h) is the translation).

**Claim:** ||τ\_h f - f||\_p → 0 as h → 0 for f ∈ Lp, 1 ≤ p < ∞.

*Proof of claim.* First prove it for continuous compactly supported φ: ||τ\_h φ - φ||\_p ≤ (2R)^{1/p} · sup|φ(x+h) - φ(x)| → 0 by uniform continuity (where supp(φ) ⊂ [-R,R]).

For general f ∈ Lp, fix ε > 0 and choose φ ∈ C\_c with ||f - φ||\_p < ε/3. Then:

$$\|\tau_h f - f\|_p \leq \|\tau_h f - \tau_h\varphi\|_p + \|\tau_h\varphi - \varphi\|_p + \|\varphi - f\|_p < \frac{\varepsilon}{3} + \|\tau_h\varphi - \varphi\|_p + \frac{\varepsilon}{3}.$$

Choose |h| small enough that ||τ\_h φ - φ||\_p < ε/3. Then ||τ\_h f - f||\_p < ε. ✓

Therefore |f*g(x+h) - f*g(x)| ≤ ||τ\_h f - f||\_p · ||g||\_q → 0 as h → 0. ∎

### Part 3: f*g(x) → 0 as |x| → ∞

Fix ε > 0. Choose φ ∈ C\_c(ℝ) with ||f - φ||\_p < ε, say supp(φ) ⊂ [-R, R].

**Decompose:**

$$f*g = \varphi * g + (f - \varphi)*g.$$

**Error term:** By Hölder, ||(f-φ)*g||\_∞ ≤ ||f-φ||\_p ||g||\_q < ε||g||\_q.

**Main term:** For any x:

$$|\varphi*g(x)| = \left|\int \varphi(x-y)g(y)\,dy\right| \leq \|\varphi\|_p \cdot \left(\int_{x-R}^{x+R}|g(y)|^q\,dy\right)^{1/q}$$

since φ(x-y) = 0 unless |x-y| ≤ R (i.e., y ∈ [x-R, x+R]). The Hölder inequality is applied with φ(x-·) supported on [x-R, x+R].

Now g ∈ Lq(ℝ), so by the absolute continuity of the integral (or dominated convergence):

$$\int_{x-R}^{x+R}|g(y)|^q\,dy \to 0 \quad \text{as } |x| \to \infty$$

because the interval [x-R, x+R] slides to ±∞ and g^q ∈ L¹. Therefore |φ*g(x)| → 0 as |x| → ∞.

**Combine:** For |x| large enough, |φ*g(x)| < ε, so:

$$|f*g(x)| \leq |\varphi*g(x)| + |(f-\varphi)*g(x)| < \varepsilon + \varepsilon\|g\|_q.$$

Since ε was arbitrary, f*g(x) → 0. ∎

## What Connects

**To the Riemann-Lebesgue lemma.** f*g vanishes at infinity — this is an instance of the general principle that convolution "smooths" and "spreads." The Riemann-Lebesgue lemma (f̂(ξ) → 0 for f ∈ L¹) is the Fourier-side analogue: convolution in space = multiplication in frequency, and the product of Lp and Lq Fourier transforms vanishes at infinity.

**To Young's convolution inequality.** The general form says: ||f*g||\_r ≤ ||f||\_p ||g||\_q when 1/p + 1/q = 1 + 1/r. Our case is r = ∞ (1/p + 1/q = 1 = 1 + 1/∞), giving ||f*g||\_∞ ≤ ||f||\_p ||g||\_q. The continuity and vanishing at infinity are not part of Young's inequality but strengthen the conclusion from L∞ to C₀ (continuous functions vanishing at infinity).

**To the C₀ convolution theorem.** The result says f*g ∈ C₀(ℝ). Combined with the sup-norm bound, this places f*g in the Banach algebra C₀(ℝ). This is optimal: for general Lp * Lq, the convolution is in C₀ but not necessarily in any Lr for finite r.

**To approximate identities.** The continuity proof uses the same ingredients (density of C\_c in Lp, Hölder) that underlie the theory of approximate identities. The continuity of translations is the single most important structural property of Lp spaces.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.NormedSpace.Dual
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.ContinuousFunction.ZeroAtInfty

open MeasureTheory Set Filter NNReal ENNReal

noncomputable section

/-- Translation operator τ_h f(x) = f(x + h). -/
def translate (f : ℝ → ℝ) (h : ℝ) : ℝ → ℝ := fun x => f (x + h)

/-- Continuity of Lp translations: ‖τ_h f - f‖_p → 0 as h → 0.
    This is the foundational ingredient. -/
theorem Lp_translation_continuous
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {f : ℝ → ℝ} (hf : Memℒp f p volume) :
    Tendsto (fun h : ℝ => eLpNorm (fun x => f (x + h) - f x) p volume)
      (𝓝 0) (𝓝 0) := by
  sorry

/-- Dense subspace: C_c(ℝ) is dense in Lp(ℝ) for 1 ≤ p < ∞. -/
lemma Cc_dense_Lp
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {f : ℝ → ℝ} (hf : Memℒp f p volume) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : ℝ → ℝ, HasCompactSupport φ ∧ Continuous φ ∧
      Memℒp φ p volume ∧
      eLpNorm (f - φ) p volume < ENNReal.ofReal ε := by
  sorry

/-- Hölder's inequality for convolution:
    |f*g(x)| ≤ ‖f‖_p ‖g‖_q when 1/p + 1/q = 1. -/
lemma convolution_bound
    {p : ℝ≥0∞} (hp : 1 < p) (hp' : p ≠ ⊤)
    {f : ℝ → ℝ} (hf : Memℒp f p volume)
    {g : ℝ → ℝ} (hg : Memℒp g (p / (p - 1)) volume) (x : ℝ) :
    ‖∫ y, f (x - y) * g y ∂volume‖ ≤
      (eLpNorm f p volume * eLpNorm g (p / (p - 1)) volume).toReal := by
  sorry

/-- Continuity of the convolution:
    |f*g(x+h) - f*g(x)| ≤ ‖τ_h f - f‖_p · ‖g‖_q. -/
lemma convolution_continuity_bound
    {p : ℝ≥0∞} (hp : 1 < p) (hp' : p ≠ ⊤)
    {f : ℝ → ℝ} (hf : Memℒp f p volume)
    {g : ℝ → ℝ} (hg : Memℒp g (p / (p - 1)) volume)
    (x h : ℝ) :
    ‖(∫ y, f (x + h - y) * g y ∂volume) -
     (∫ y, f (x - y) * g y ∂volume)‖ ≤
      (eLpNorm (fun t => f (t + h) - f t) p volume *
       eLpNorm g (p / (p - 1)) volume).toReal := by
  sorry

/-- Main theorem, part 1: f * g is continuous. -/
theorem convolution_continuous
    {p : ℝ≥0∞} (hp : 1 < p) (hp' : p ≠ ⊤)
    {f : ℝ → ℝ} (hf : Memℒp f p volume)
    {g : ℝ → ℝ} (hg : Memℒp g (p / (p - 1)) volume)
    (hfm : AEStronglyMeasurable f volume)
    (hgm : AEStronglyMeasurable g volume) :
    Continuous (fun x => ∫ y, f (x - y) * g y ∂volume) := by
  sorry

/-- Lq norm on a sliding interval vanishes at infinity:
    ∫_{x-R}^{x+R} |g|^q dy → 0 as |x| → ∞ for g ∈ Lq. -/
lemma Lq_tail_vanishes
    {q : ℝ≥0∞} (hq : 1 ≤ q) (hq' : q ≠ ⊤)
    {g : ℝ → ℝ} (hg : Memℒp g q volume)
    {R : ℝ} (hR : 0 < R) :
    Tendsto (fun x => eLpNorm g q (volume.restrict (Icc (x - R) (x + R))))
      (cocompact ℝ) (𝓝 0) := by
  sorry

/-- Main theorem, part 2: f * g vanishes at infinity. -/
theorem convolution_tendsto_zero
    {p : ℝ≥0∞} (hp : 1 < p) (hp' : p ≠ ⊤)
    {f : ℝ → ℝ} (hf : Memℒp f p volume)
    {g : ℝ → ℝ} (hg : Memℒp g (p / (p - 1)) volume)
    (hfm : AEStronglyMeasurable f volume)
    (hgm : AEStronglyMeasurable g volume) :
    Tendsto (fun x => ∫ y, f (x - y) * g y ∂volume)
      (cocompact ℝ) (𝓝 0) := by
  sorry

/-- Full theorem packaged: f * g ∈ C₀(ℝ). -/
theorem convolution_mem_C0
    {p : ℝ≥0∞} (hp : 1 < p) (hp' : p ≠ ⊤)
    {f : ℝ → ℝ} (hf : Memℒp f p volume)
    {g : ℝ → ℝ} (hg : Memℒp g (p / (p - 1)) volume)
    (hfm : AEStronglyMeasurable f volume)
    (hgm : AEStronglyMeasurable g volume) :
    Continuous (fun x => ∫ y, f (x - y) * g y ∂volume) ∧
    Tendsto (fun x => ∫ y, f (x - y) * g y ∂volume)
      (cocompact ℝ) (𝓝 0) := by
  sorry

end
```

**Mathlib notes:**

- `Memℒp f p volume` says f ∈ Lp(ℝ). The conjugate exponent q is expressed as `p / (p - 1)` in ℝ≥0∞ arithmetic (since 1/p + 1/q = 1 iff q = p/(p-1)).
- `eLpNorm f p volume` is the Lp seminorm. The translation continuity `Lp_translation_continuous` is the core infrastructure lemma.
- `cocompact ℝ` is the filter for |x| → ∞. `Tendsto f (cocompact ℝ) (𝓝 0)` says f vanishes at infinity.
- The convolution is written explicitly as `fun x => ∫ y, f (x - y) * g y ∂volume` rather than using Mathlib's `convolution` (which uses `fun x => ∫ t, f t • g (x - t) ∂μ` with `•` for the smul action).
- `HasCompactSupport φ` in `Cc_dense_Lp` provides the approximation by compactly supported functions, essential for the vanishing-at-infinity argument.
- The proof chain: `convolution_continuity_bound` + `Lp_translation_continuous` → `convolution_continuous`; `Cc_dense_Lp` + `Lq_tail_vanishes` → `convolution_tendsto_zero`.
