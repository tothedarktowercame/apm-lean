

# APM a01A03: Identifying a convolution kernel from a functional identity

## Why It's Hard

The hypothesis says a *single* function g ∈ L¹(ℝ) satisfies g * f' = f(x+h) - f(x-h) for *all* f ∈ C¹(ℝ). This is a strong universal quantifier — g must work for every smooth function simultaneously. The difficulty is extracting the pointwise identity g = χ\_{[-h,h]} from this integral equation. You can't just "read off" g because the convolution mixes g with f' nonlocally. The key is to use the Fourier transform, where convolution becomes multiplication and the universal quantifier pins down ĝ uniquely.

## The Key Insight

Take Fourier transforms of both sides. On the left, convolution becomes multiplication: ĝ · (2πiξ f̂(ξ)) (since f' has transform 2πiξ f̂). On the right, f(x+h) - f(x-h) has transform (e^{2πiξh} - e^{-2πiξh}) f̂(ξ) = 2i sin(2πξh) f̂(ξ). Since this holds for all f, we can cancel f̂ and get ĝ(ξ) · 2πiξ = 2i sin(2πξh), i.e., ĝ(ξ) = sin(2πξh)/(πξ). This is exactly the Fourier transform of χ\_{[-h,h]}. Injectivity of the Fourier transform on L¹ gives g = χ\_{[-h,h]} a.e.

But there's a subtlety: we need f and f' to both be nice enough for the Fourier argument. The cleaner approach avoids the Fourier transform entirely and uses specific test functions.

## Complete Proof

**Theorem.** Let g ∈ L¹(ℝ) and h > 0. Suppose that for every f ∈ C¹(ℝ):

$$(g * f')(x) = f(x+h) - f(x-h) \quad \text{for all } x \in \mathbb{R}.$$

Then g = χ\_{[-h,h]} almost everywhere.

**Proof.**

**Step 1: Rewrite the identity.** By definition of convolution:

$$(g * f')(x) = \int_{-\infty}^{\infty} g(t) f'(x - t)\,dt.$$

The right side can also be written as a convolution. Note that:

$$f(x+h) - f(x-h) = \int_{x-h}^{x+h} f'(s)\,ds = \int_{-h}^{h} f'(x - (-u))\,du = \int_{-h}^{h} f'(x + u)\,du$$

Wait — let me be more careful with the substitution. Setting s = x + u:

$$f(x+h) - f(x-h) = \int_{x-h}^{x+h} f'(s)\,ds = \int_{-h}^{h} f'(x+u)\,du.$$

Now substitute u = -t:

$$= \int_{-h}^{h} f'(x - (-u))\,du = \int_{-h}^{h} f'(x+u)\,du.$$

Hmm, let me write it as a convolution directly. We have:

$$\int_{-h}^{h} f'(x+u)\,du = \int_{-\infty}^{\infty} \chi_{[-h,h]}(u) f'(x+u)\,du.$$

But convolution is (g * f')(x) = ∫ g(t) f'(x-t) dt. To match, substitute u = -t:

$$\int_{-\infty}^{\infty} \chi_{[-h,h]}(-t) f'(x-t)\,dt = \int_{-\infty}^{\infty} \chi_{[-h,h]}(t) f'(x-t)\,dt$$

since χ\_{[-h,h]} is symmetric. So:

$$f(x+h) - f(x-h) = (\chi_{[-h,h]} * f')(x).$$

Therefore the hypothesis says:

$$(g * f')(x) = (\chi_{[-h,h]} * f')(x) \quad \text{for all } x \in \mathbb{R}, \text{ for all } f \in C^1(\mathbb{R}).$$

Equivalently:

$$((g - \chi_{[-h,h]}) * f')(x) = 0 \quad \text{for all } x, \text{ for all } f \in C^1(\mathbb{R}).$$

**Step 2: Show g - χ\_{[-h,h]} = 0 a.e.**

Set φ = g - χ\_{[-h,h]} ∈ L¹(ℝ). We have φ * f' = 0 for all f ∈ C¹(ℝ).

Since f ranges over all C¹ functions, f' ranges over all continuous functions (every continuous function is the derivative of some C¹ function). So:

$$\phi * \psi = 0 \quad \text{for all } \psi \in C(\mathbb{R}).$$

In particular, choose ψ to be a smooth approximate identity: let ψ\_ε be a standard mollifier (nonneg, supported on [-ε, ε], integral 1). Then:

$$0 = (\phi * \psi_\varepsilon)(x) \quad \text{for all } x, \varepsilon > 0.$$

But φ * ψ\_ε → φ in L¹ as ε → 0 (standard approximation-to-the-identity theorem for L¹ functions). Since φ * ψ\_ε = 0 for all ε, we get φ = 0 in L¹, meaning g = χ\_{[-h,h]} almost everywhere. ∎

**Remark.** The step "f' ranges over all continuous functions" needs a small justification. Given any continuous ψ : ℝ → ℝ, define f(x) = ∫₀ˣ ψ(t) dt. Then f ∈ C¹(ℝ) and f' = ψ. (We don't need f to have any decay or integrability — the hypothesis holds for *all* f ∈ C¹.) Actually we need to be slightly careful: we need φ * ψ to make sense, which requires some growth control. Since φ ∈ L¹ (so it is integrable) and ψ is continuous, (φ * ψ)(x) = ∫ φ(t)ψ(x-t)dt is well-defined for each x as long as ψ is locally bounded, which all continuous functions are. The convolution is well-defined pointwise. So the argument goes through for ψ = ψ\_ε (compactly supported, smooth), which is more than sufficient.

## What Connects

**To the fundamental theorem of calculus.** The identity f(x+h) - f(x-h) = ∫\_{-h}^{h} f'(x+t) dt is the fundamental theorem applied to f' over the interval [x-h, x+h]. The problem asks: if some other kernel g reproduces this identity, must it be the obvious one?

**To approximate identities and uniqueness.** The proof uses the fact that L¹ convolution with approximate identities is faithful: if φ * ψ\_ε = 0 for all ε, then φ = 0. This is the L¹ analogue of "if a distribution annihilates all test functions, it is zero."

**To the Titchmarsh convolution theorem.** A deeper result says that if f * g = 0 and both are supported on half-lines, then one of them is zero. Our problem is simpler (we get zero convolution with *all* continuous functions, not just one) but lives in the same neighborhood.

**To uniqueness of the Fourier transform.** The Fourier-based proof (Step 0 in "Key Insight") uses the fact that ĝ is uniquely determined by the identity ĝ(ξ) · 2πiξ = 2i sin(2πξh) for all ξ ≠ 0. This gives ĝ = sin(2πξh)/(πξ), which is the sinc function — the Fourier transform of χ\_{[-h,h]}.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Topology.ContinuousFunction.Basic

open MeasureTheory Set Filter

noncomputable section

/-- The convolution of g with f' equals the symmetric difference of f. -/
def ConvolutionShiftProperty (g : ℝ → ℝ) (h : ℝ) : Prop :=
  ∀ (f : ℝ → ℝ), ContDiff ℝ 1 f →
    ∀ x : ℝ, ∫ t, g t * deriv f (x - t) = f (x + h) - f (x - h)

/-- Step 1: The right-hand side f(x+h) - f(x-h) is itself a convolution
    of f' with χ_{[-h,h]}, via the fundamental theorem of calculus. -/
lemma shift_eq_indicator_conv_deriv
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    f (x + h) - f (x - h) =
      ∫ t, (Icc (-h) h).indicator (fun _ => (1 : ℝ)) t * deriv f (x - t) := by
  sorry

/-- Step 2: The difference φ = g - χ_{[-h,h]} satisfies φ * ψ = 0
    for every continuous function ψ. -/
lemma conv_eq_zero_of_shift_property
    {g : ℝ → ℝ} {h : ℝ} (hh : 0 < h)
    (hg : Integrable g volume)
    (hprop : ConvolutionShiftProperty g h)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) (hψ_supp : HasCompactSupport ψ) :
    ∀ x, ∫ t, (g t - (Icc (-h) h).indicator (fun _ => (1 : ℝ)) t) *
      ψ (x - t) = 0 := by
  sorry

/-- Step 3: Convolution with approximate identities is faithful.
    If φ ∈ L¹ and φ * ψ_ε = 0 for all smooth mollifiers ψ_ε,
    then φ = 0 a.e. -/
lemma eq_zero_of_conv_mollifier_eq_zero
    {φ : ℝ → ℝ} (hφ : Integrable φ volume)
    (h_conv : ∀ (ψ : ℝ → ℝ), Continuous ψ → HasCompactSupport ψ →
      ∀ x, ∫ t, φ t * ψ (x - t) = 0) :
    φ =ᵐ[volume] 0 := by
  sorry

/-- Main theorem: g must equal χ_{[-h,h]} almost everywhere. -/
theorem convolution_shift_determines_kernel
    {g : ℝ → ℝ} {h : ℝ} (hh : 0 < h)
    (hg : Integrable g volume)
    (hprop : ConvolutionShiftProperty g h) :
    g =ᵐ[volume] (Icc (-h) h).indicator (fun _ => (1 : ℝ)) := by
  sorry

/-- Corollary: g equals the indicator on the open interval (-h,h)
    (which agrees a.e. with the closed-interval indicator). -/
theorem convolution_shift_determines_kernel'
    {g : ℝ → ℝ} {h : ℝ} (hh : 0 < h)
    (hg : Integrable g volume)
    (hprop : ConvolutionShiftProperty g h) :
    g =ᵐ[volume] (Ioo (-h) h).indicator (fun _ => (1 : ℝ)) := by
  sorry

end
```

**Mathlib notes:**

- `=ᵐ[volume]` is `Filter.EventuallyEq` with respect to the `ae volume` filter — the standard way to express "equal almost everywhere" in Mathlib.
- `(Icc (-h) h).indicator (fun _ => (1 : ℝ))` is the characteristic function χ\_{[-h,h]}, written using `Set.indicator`.
- `ContDiff ℝ 1 f` says f is C¹. `deriv f` is its derivative.
- `Integrable g volume` encodes g ∈ L¹(ℝ).
- `HasCompactSupport ψ` restricts the test functions to compactly supported ones, which is sufficient for the approximate identity argument and avoids integrability issues with the convolution.
- The convolution `∫ t, g t * ψ (x - t)` is written as a Bochner integral rather than using Mathlib's `convolution` function, to keep the types simpler. Mathlib's `MeasureTheory.convolution` uses `fun x => ∫ t, f t • g (x - t) ∂μ` with the same meaning.