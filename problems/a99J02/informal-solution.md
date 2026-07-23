<!-- source: agent-generated; stage: nl-proof-harvest; date: 2026-06-16 -->

# APM a99J02: Convolution of L² indicators is continuous, and the Steinhaus overlap estimate

## Why It's Hard

χ_E is, in general, **wildly discontinuous** — E is an arbitrary positive-measure measurable subset of [0,1], so χ_E can jump on a dense, fractal-like set. Yet the convolution χ_E ∗ χ_E is asserted to be *continuous*. The point is that convolution **regularizes**: integrating χ_E against a translate of itself averages out the pointwise pathology, and the right way to see this is not pointwise but through the **continuity of translation in L²**, which holds for *every* L² function regardless of how badly it behaves pointwise.

Part (b) hides a second subtlety. We will know the overlap |E ∩ (E+t)| equals |E| > 0 *at the single point t = 0*; but "positive at one point" says nothing about a neighborhood unless the overlap is a **continuous** function of t. So (b) is exactly an application of the regularity proved in (a): continuity is what lets a single positive value spread to a whole interval.

Note χ_E ∈ L²(ℝ): it is bounded by 1 and supported in [0,1], so ∫ χ_E² = |E| ≤ 1 < ∞ (likewise χ_E ∈ L¹).

## The Key Insight

One lemma does both parts:

> **Lemma.** If f, g ∈ L²(ℝ), then h(x) = ∫ f(x−y)g(y)\,dy is (uniformly) continuous.

The proof is Cauchy–Schwarz plus the standard fact that translation is continuous in L²: ‖f(·+δ) − f‖₂ → 0 as δ → 0. Then:

- **(a)** is the Lemma with f = g = χ_E.
- **(b)**: the overlap φ(t) = |E ∩ (E+t)| = ∫ χ_E(y) χ_E(y−t)\,dy is the same kind of integral (it is χ_E ∗ χ_{−E} evaluated at t), so the Lemma makes it continuous; since φ(0) = |E| > 0, continuity keeps φ positive on a neighborhood of 0.

## Complete Proof

**Lemma.** Let f, g ∈ L²(ℝ) and h(x) = ∫_ℝ f(x−y) g(y)\,dy. Then h is well-defined, bounded, and uniformly continuous.

*Proof.* For fixed x, the map y ↦ f(x−y) is in L² (translation/reflection preserve the L² norm), and g ∈ L², so by Cauchy–Schwarz the integrand is integrable and |h(x)| ≤ ‖f‖₂‖g‖₂; thus h is well-defined and bounded. For the modulus of continuity, fix δ ∈ ℝ and estimate

$$
h(x+\delta) - h(x) = \int_{\mathbb R}\big[f(x+\delta - y) - f(x - y)\big]\,g(y)\,dy,
$$

so by Cauchy–Schwarz,

$$
|h(x+\delta) - h(x)| \;\leq\; \Big(\int_{\mathbb R} |f(x+\delta-y) - f(x-y)|^2\,dy\Big)^{1/2}\,\|g\|_2 .
$$

Substituting u = x − y in the first factor (Lebesgue measure is translation-invariant),

$$
\int_{\mathbb R} |f(x+\delta-y) - f(x-y)|^2\,dy = \int_{\mathbb R} |f(u+\delta) - f(u)|^2\,du = \|f(\cdot+\delta) - f\|_2^2 .
$$

Hence, **uniformly in x**,

$$
|h(x+\delta) - h(x)| \;\leq\; \|f(\cdot+\delta) - f\|_2\,\|g\|_2 . \tag{$\ast$}
$$

It remains to recall **continuity of translation in L²**: ‖f(·+δ) − f‖₂ → 0 as δ → 0. (Given ε > 0, pick φ ∈ C_c(ℝ) with ‖f − φ‖₂ < ε, possible by density of C_c in L²; φ is uniformly continuous with compact support, so ‖φ(·+δ) − φ‖₂ → 0 by dominated convergence; then ‖f(·+δ) − f‖₂ ≤ 2‖f − φ‖₂ + ‖φ(·+δ) − φ‖₂ < 3ε for δ small.) By ($\ast$), h is uniformly continuous. ∎

**(a).** Since χ_E ∈ L²(ℝ), the Lemma with f = g = χ_E shows

$$
\chi_E \ast \chi_E (x) = \int_{\mathbb R} \chi_E(x-y)\,\chi_E(y)\,dy
$$

is (uniformly) continuous in x. ∎

**(b).** For t ∈ ℝ, the translate satisfies χ_{E+t}(y) = χ_E(y − t), so

$$
|E \cap (E+t)| = \int_{\mathbb R} \chi_E(y)\,\chi_{E+t}(y)\,dy = \int_{\mathbb R} \chi_E(y)\,\chi_E(y-t)\,dy =: \varphi(t).
$$

This is exactly an integral of the Lemma's form: with ǧ(y) := χ_E(−y) = χ_{−E}(y),

$$
\varphi(t) = \int_{\mathbb R} \chi_E(t - u)\,\chi_E(-u)\,du \quad (u = t - y) \;=\; (\chi_E \ast \chi_{-E})(t),
$$

a convolution of the two L² functions χ_E and χ_{−E}. By the Lemma, **φ is continuous on ℝ**. At t = 0,

$$
\varphi(0) = \int_{\mathbb R}\chi_E(y)^2\,dy = |E| > 0 .
$$

By continuity at 0 applied with the value |E|/2 > 0: there exists ε > 0 such that |φ(t) − φ(0)| < |E|/2 whenever |t| < ε, and hence

$$
|E \cap (E+t)| = \varphi(t) > \varphi(0) - \tfrac{|E|}{2} = \tfrac{|E|}{2} > 0 \qquad \text{for all } |t| < \varepsilon . \qquad \blacksquare
$$

## What Connects

**Within analysis**: This is the engine of the **Steinhaus theorem** — that the difference set E − E contains an open interval around 0 when |E| > 0. Indeed |E ∩ (E+t)| > 0 forces E ∩ (E+t) ≠ ∅, i.e. t ∈ E − E; so part (b) says (−ε, ε) ⊆ E − E. The proof needs no special structure on E, only positive measure, which is why it is a workhorse for "measurable ⟹ a little bit of regularity" results (e.g. measurable additive functions are linear, measurable subgroups of ℝ are open).

**The reusable principle**: convolution turns L² (or L¹) data into a continuous function — the autocorrelation of any L² function is continuous — and Cauchy–Schwarz reduces the whole matter to continuity of translation in L^p (1 ≤ p < ∞), itself a density-of-C_c argument. The same ($\ast$)-estimate proves that f ∗ g is continuous whenever the exponents are conjugate (Hölder in place of Cauchy–Schwarz).
