

# APM a03J04: Distribution functions, layer cake, and weak-L¹ estimates

## Why It's Hard

Part (a) requires the "layer cake" representation — converting a spatial integral into a height integral via Fubini on the subgraph. Parts (b)/(c) require extracting an integral bound from a distributional (weak-type) condition. The weak-L¹ condition λ(α) ≤ M/α only gives tail decay — not integrability of |f| itself — but for |f|^p with p < 1 on a finite-measure set, the reduced power p combined with the finite measure provides enough room. The challenge is optimizing the truncation level to get the sharp constant.

## The Key Insight

**(a)** Think of the region under |f| as horizontal slabs. The slab at height α has base {|f| > α} and thickness dα. Fubini on the subgraph {(x,α) : 0 ≤ α < |f(x)|} gives the identity.

**(b)/(c)** Apply the layer cake to |f|^p on E: ∫\_E |f|^p = ∫₀^∞ m(E ∩ {|f|^p > t}) dt. Bound the integrand by min(m(E), M/t^{1/p}) — the first from the trivial bound, the second from the weak-L¹ condition. Split the integral at the crossover point t₀ = (M/m(E))^p and optimize.

## Complete Proof

### Part (a): Layer cake formula

**Claim.** ∫\_{ℝⁿ} |f| dx = ∫₀^∞ λ(α) dα where λ(α) = m({|f| > α}).

**Proof.** Define S = {(x, α) ∈ ℝⁿ × [0,∞) : 0 ≤ α < |f(x)|}. This is measurable in the product σ-algebra.

**Slice in x:** For fixed x, S\_x = [0, |f(x)|) has 1-d measure |f(x)|. By Tonelli:

$$\iint_S dx\,d\alpha = \int_{\mathbb{R}^n} |f(x)|\,dx.$$

**Slice in α:** For fixed α ≥ 0, S^α = {x : |f(x)| > α} has measure λ(α). By Tonelli:

$$\iint_S dx\,d\alpha = \int_0^{\infty}\lambda(\alpha)\,d\alpha.$$

Both equal the product measure of S, so ∫|f| = ∫₀^∞ λ(α) dα. ∎

### Part (b): ∫\_E |f|^p < ∞ for 0 < p < 1 and m(E) < ∞

**Proof.** Apply the layer cake to |f|^p restricted to E:

$$\int_E |f|^p\,dx = \int_0^{\infty} m(E \cap \{|f|^p > t\})\,dt = \int_0^{\infty} m(E \cap \{|f| > t^{1/p}\})\,dt.$$

Bound the integrand using two estimates:

- **Trivial:** m(E ∩ {|f| > t^{1/p}}) ≤ m(E).
- **Weak-L¹:** m(E ∩ {|f| > t^{1/p}}) ≤ m({|f| > t^{1/p}}) = λ(t^{1/p}) ≤ M/t^{1/p}.

Set t₀ = (M/m(E))^p (crossover where m(E) = M/t₀^{1/p}).

$$\int_E |f|^p = \int_0^{t_0} m(E \cap \{|f| > t^{1/p}\})\,dt + \int_{t_0}^{\infty} m(E \cap \{|f| > t^{1/p}\})\,dt$$

$$\leq \int_0^{t_0} m(E)\,dt + \int_{t_0}^{\infty} \frac{M}{t^{1/p}}\,dt = m(E) \cdot t_0 + \frac{M \cdot t_0^{1-1/p}}{1/p - 1}.$$

The second integral converges because 1/p > 1 (since p < 1). Both terms are finite, so ∫\_E |f|^p < ∞. ∎

### Part (c): The explicit bound

**Proof.** Continuing from part (b) with t₀ = (M/m(E))^p:

**First term:** m(E) · t₀ = m(E) · (M/m(E))^p = m(E)^{1-p} · M^p.

**Second term:** ∫\_{t₀}^∞ M t^{-1/p} dt = M · [t^{1-1/p}/(1-1/p)]\_{t₀}^∞. Since 1-1/p < 0, the integral equals:

$$M \cdot \frac{t_0^{1-1/p}}{1/p - 1} = \frac{p}{1-p} \cdot M \cdot t_0^{(p-1)/p}.$$

Now t₀^{(p-1)/p} = ((M/m(E))^p)^{(p-1)/p} = (M/m(E))^{p-1} = M^{p-1} · m(E)^{1-p}.

So the second term = (p/(1-p)) · M · M^{p-1} · m(E)^{1-p} = (p/(1-p)) · M^p · m(E)^{1-p}.

**Total:**

$$\int_E |f|^p \leq m(E)^{1-p} M^p + \frac{p}{1-p} \cdot M^p \cdot m(E)^{1-p} = \frac{1}{1-p} \cdot m(E)^{1-p} \cdot M^p.$$

So c(n,p) = 1/(1-p) (independent of n).

$$\boxed{\int_E |f|^p\,dx \leq \frac{1}{1-p}\,m(E)^{1-p}\,M^p.} \qquad \blacksquare$$

## What Connects

**To interpolation.** The bound ∫\_E |f|^p ≤ C · m(E)^{1-p} M^p for 0 < p < 1 is a restricted weak-type estimate. It shows weak-L¹ ⊂ L^p\_{loc} for p < 1, which is the key input for Marcinkiewicz interpolation.

**To the Calderón-Zygmund theory.** The weak-L¹ condition arises naturally for singular integrals: the Hilbert transform, maximal function, etc. are bounded on L¹ only in the weak sense. Parts (b)/(c) show these operators produce locally Lp functions for p < 1.

**To the Cavalieri principle.** Part (a) is the measure-theory version of Cavalieri's principle from calculus: the volume under a surface equals the integral of cross-sectional areas.

**To problem a01A02.** That problem (weak-L² ⟹ local L¹) uses the same technique: layer cake + split at the optimal truncation level. Here the roles are shifted: weak-L¹ gives local L^p for p < 1 (instead of weak-L² giving local L¹).

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

/-- The distribution function λ(α) = m({|f| > α}). -/
def distribFn (f : (Fin n → ℝ) → ℝ) (μ : Measure (Fin n → ℝ)) (α : ℝ) : ℝ≥0∞ :=
  μ {x | α < ‖f x‖}

/-- Part (a): Layer cake formula.
    ∫ |f| dx = ∫₀^∞ λ(α) dα.
    This is `lintegral_norm_eq_lintegral_meas_lt` in Mathlib. -/
theorem layer_cake
    {μ : Measure (Fin n → ℝ)} [SigmaFinite μ]
    {f : (Fin n → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖f x‖₊ ∂μ =
      ∫⁻ α in Ioi (0 : ℝ), distribFn f μ α := by
  sorry

/-- Weak-L¹ condition: sup_{α>0} α · λ(α) ≤ M. -/
def MemWeakL1 (f : (Fin n → ℝ) → ℝ) (μ : Measure (Fin n → ℝ))
    (M : ℝ≥0∞) : Prop :=
  ∀ α : ℝ, 0 < α → ENNReal.ofReal α * distribFn f μ α ≤ M

/-- Weak-L¹ gives the distribution bound λ(α) ≤ M/α. -/
lemma MemWeakL1.distribFn_le
    {f : (Fin n → ℝ) → ℝ} {μ : Measure (Fin n → ℝ)} {M : ℝ≥0∞}
    (hf : MemWeakL1 f μ M) {α : ℝ} (hα : 0 < α) :
    distribFn f μ α ≤ M / ENNReal.ofReal α := by
  sorry

/-- Trivial bound: the restricted distribution function ≤ m(E). -/
lemma distribFn_restrict_le
    {f : (Fin n → ℝ) → ℝ} {μ : Measure (Fin n → ℝ)}
    {E : Set (Fin n → ℝ)} (hfm : Measurable f) (α : ℝ) :
    μ.restrict E {x | α < ‖f x‖} ≤ μ E := by
  sorry

/-- Layer cake for |f|^p on E:
    ∫_E |f|^p = ∫₀^∞ m(E ∩ {|f|^p > t}) dt. -/
lemma layer_cake_rpow
    {μ : Measure (Fin n → ℝ)} [SigmaFinite μ]
    {f : (Fin n → ℝ) → ℝ} (hf : Measurable f)
    {E : Set (Fin n → ℝ)} (hE : MeasurableSet E)
    {p : ℝ} (hp : 0 < p) :
    ∫⁻ x in E, ENNReal.ofReal (‖f x‖ ^ p) ∂μ =
      ∫⁻ t in Ioi (0 : ℝ),
        μ.restrict E {x | t < ‖f x‖ ^ p} := by
  sorry

/-- Splitting the integral at the crossover point. -/
lemma lintegral_Ioi_split (g : ℝ → ℝ≥0∞) {c : ℝ} (hc : 0 < c) :
    ∫⁻ t in Ioi (0 : ℝ), g t =
      ∫⁻ t in Ioc 0 c, g t + ∫⁻ t in Ioi c, g t := by
  sorry

/-- Low integral: ∫₀^{t₀} m(E) dt = m(E) · t₀. -/
lemma low_integral_bound {μ : Measure (Fin n → ℝ)}
    {E : Set (Fin n → ℝ)} {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ∫⁻ t in Ioc (0 : ℝ) t₀, μ E = μ E * ENNReal.ofReal t₀ := by
  sorry

/-- High integral: ∫_{t₀}^∞ M/t^{1/p} dt = (p/(1-p)) M t₀^{1-1/p}
    when p < 1. -/
lemma high_integral_bound
    {M : ℝ≥0∞} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {t₀ : ℝ} (ht₀ : 0 < t₀) (hM : M ≠ ⊤) :
    ∫⁻ t in Ioi t₀, M * ENNReal.ofReal (t ^ (-(1 : ℝ) / p)) ≤
      ENNReal.ofReal (p / (1 - p)) * M *
        ENNReal.ofReal (t₀ ^ (1 - 1 / p)) := by
  sorry

/-- Part (b): ∫_E |f|^p < ∞ for weak-L¹ f, 0 < p < 1, m(E) < ∞. -/
theorem weakL1_Lp_finite
    {μ : Measure (Fin n → ℝ)} [SigmaFinite μ]
    {f : (Fin n → ℝ) → ℝ} (hfm : Measurable f)
    {M : ℝ≥0∞} (hf : MemWeakL1 f μ M) (hM : M ≠ ⊤)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {E : Set (Fin n → ℝ)} (hE : MeasurableSet E)
    (hEfin : μ E ≠ ⊤) (hEpos : 0 < μ E) :
    ∫⁻ x in E, ENNReal.ofReal (‖f x‖ ^ p) ∂μ < ⊤ := by
  sorry

/-- Part (c): The explicit bound ∫_E |f|^p ≤ (1/(1-p)) m(E)^{1-p} M^p.
    The constant c(n,p) = 1/(1-p) is independent of n. -/
theorem weakL1_Lp_bound
    {μ : Measure (Fin n → ℝ)} [SigmaFinite μ]
    {f : (Fin n → ℝ) → ℝ} (hfm : Measurable f)
    {M : ℝ≥0∞} (hf : MemWeakL1 f μ M) (hM : M ≠ ⊤)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {E : Set (Fin n → ℝ)} (hE : MeasurableSet E)
    (hEfin : μ E ≠ ⊤) (hEpos : 0 < μ E) :
    ∫⁻ x in E, ENNReal.ofReal (‖f x‖ ^ p) ∂μ ≤
      ENNReal.ofReal (1 / (1 - p)) *
        (μ E) ^ (1 - p) * M ^ p := by
  sorry

/-- The optimal splitting point t₀ = (M/m(E))^p. -/
def optimalSplit (M : ℝ≥0∞) (mE : ℝ≥0∞) (p : ℝ) : ℝ≥0∞ :=
  (M / mE) ^ p

/-- Level set equivalence: {|f|^p > t} = {|f| > t^{1/p}} for t ≥ 0. -/
lemma levelSet_rpow_eq (f : (Fin n → ℝ) → ℝ)
    {p : ℝ} (hp : 0 < p) {t : ℝ} (ht : 0 ≤ t) :
    {x | t < ‖f x‖ ^ p} = {x | t ^ (1 / p) < ‖f x‖} := by
  sorry

end
```

**Mathlib notes:**

- Part (a) is essentially `MeasureTheory.lintegral_norm_eq_lintegral_meas_lt` in Mathlib's Layercake file. The distribution function `distribFn` matches the standard formulation.
- `MemWeakL1` encodes the weak-L¹ condition using ENNReal arithmetic: `ofReal α * μ{|f| > α} ≤ M`.
- `(μ E) ^ (1 - p)` and `M ^ p` use `ENNReal.rpow` for real exponents on extended nonneg reals.
- The proof chains: `layer_cake_rpow` (layer cake for |f|^p) → `levelSet_rpow_eq` (rewrite level sets) → `lintegral_Ioi_split` (split at t₀) → `low_integral_bound` + `high_integral_bound` (bound each piece) → `weakL1_Lp_bound` (combine and simplify).
- The constant 1/(1-p) is independent of n, confirming c(n,p) = 1/(1-p).
