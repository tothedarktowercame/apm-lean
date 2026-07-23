

# APM a02J04: Lebesgue decomposition of Lebesgue measure w.r.t. a pushforward measure

## Why It's Hard

The problem asks for the Lebesgue decomposition of m with respect to τ (not τ w.r.t. m, which would be more standard). Since τ is supported on [0,1] and Lebesgue measure m lives on all of ℝ, m has a large singular part (everything outside [0,1]) and a potentially absolutely continuous part on [0,1]. The computation requires first identifying τ explicitly, then decomposing m = m\_ac + m\_s where m\_ac ≪ τ and m\_s ⊥ τ.

## The Key Insight

**Compute τ explicitly.** For a Borel set A ⊂ ℝ:

$$\tau(A) = \mu(P^{-1}(A)) = \int\int_{P^{-1}(A)} g(x,y)\,dx\,dy = \int_A \left(\int_0^x 2\,dy\right) dx = \int_A 2x\,dx$$

for A ⊂ [0,1] (and τ(A) = 0 for A ⊂ ℝ \ [0,1]). So **dτ = 2x · 1\_{[0,1]}(x) dx** — the measure τ is absolutely continuous with respect to Lebesgue measure on [0,1] with density 2x.

Now we need the decomposition in the *other* direction: m w.r.t. τ. On [0,1], τ has density 2x w.r.t. m, so τ ≪ m there. For the reverse: m ≪ τ on (0,1] (since τ has positive density there), but m({0}) = 0 = τ({0}) so this is fine. On ℝ \ [0,1], τ = 0 but m is nonzero, so that part is singular.

## Complete Proof

### Step 1: Compute τ

For a Borel set A ⊂ ℝ:

$$\tau(A) = \mu(P^{-1}(A)) = \iint_{\{(x,y): x \in A,\, 0 \leq y \leq x \leq 1\}} 2\,dx\,dy.$$

The region {(x,y) : x ∈ A, 0 ≤ y ≤ x ≤ 1} has x ∈ A ∩ [0,1] and y ∈ [0,x]. By Fubini:

$$\tau(A) = \int_{A \cap [0,1]}\left(\int_0^x 2\,dy\right)dx = \int_{A \cap [0,1]} 2x\,dx.$$

So τ is the measure with density h(x) = 2x · 1\_{[0,1]}(x) with respect to Lebesgue measure m:

$$d\tau = 2x \cdot \mathbf{1}_{[0,1]}(x)\,dx.$$

Note: τ is supported on [0,1], and τ({0}) = 0, τ([0,1]) = ∫₀¹ 2x dx = 1.

### Step 2: Lebesgue decomposition of m w.r.t. τ

We write m = m\_ac + m\_s where m\_ac ≪ τ and m\_s ⊥ τ.

**Singular part.** τ is supported on [0,1] (in fact on (0,1], since τ({0}) = 0). So τ(ℝ \ (0,1]) = 0. Therefore m restricted to ℝ \ (0,1] is singular with respect to τ:

$$m_s = m|_{\mathbb{R} \setminus (0,1]}.$$

In other words, m\_s(A) = m(A ∩ (ℝ \ (0,1])) = m(A \ (0,1]).

**Absolutely continuous part.** On (0,1], τ has density 2x > 0 with respect to m. So m is absolutely continuous w.r.t. τ on (0,1]:

$$m_{ac} = m|_{(0,1]}.$$

For A ⊂ (0,1], if τ(A) = 0, then ∫\_A 2x dx = 0, which (since 2x > 0 on (0,1]) implies m(A) = 0. So m\_ac ≪ τ. ✓

**Verification of singularity.** m\_s is supported on ℝ \ (0,1], and τ is supported on (0,1]. So m\_s and τ are mutually singular. ✓

### Step 3: Radon-Nikodym derivative dm\_ac/dτ

For A ⊂ (0,1]:

$$m_{ac}(A) = m(A) = \int_A 1\,dx = \int_A \frac{1}{2x}\cdot 2x\,dx = \int_A \frac{1}{2x}\,d\tau(x).$$

So the Radon-Nikodym derivative is:

$$\frac{dm}{d\tau}(x) = \frac{1}{2x}, \quad x \in (0,1].$$

**Verification:** ∫\_A (1/2x) dτ = ∫\_A (1/2x) · 2x dx = ∫\_A 1 dx = m(A). ✓

### Summary

$$\boxed{m = m_{ac} + m_s, \quad m_{ac} = m|_{(0,1]}, \quad m_s = m|_{\mathbb{R}\setminus(0,1]}, \quad \frac{dm}{d\tau}(x) = \frac{1}{2x}.}$$

## What Connects

**To the pushforward measure.** τ = μ ∘ P⁻¹ is the marginal of μ on the first coordinate. Computing pushforward measures is fundamental in probability (marginal distributions) and in geometric measure theory (projections of measures).

**To the Radon-Nikodym theorem.** The decomposition m = m\_ac + m\_s is guaranteed by the Lebesgue decomposition theorem. The Radon-Nikodym derivative dm/dτ = 1/(2x) is the reciprocal of dτ/dm = 2x — this reciprocal relationship holds whenever both measures are mutually absolutely continuous on a set.

**To Bayes' theorem.** The density dτ/dm = 2x and dm/dτ = 1/(2x) are related like a prior and a likelihood: if τ is a "prior" weighting that favours larger x, then the Radon-Nikodym derivative dm/dτ = 1/(2x) is the "re-weighting" needed to recover uniform measure from the biased one.

**To the change-of-variables formula.** The computation τ(A) = ∫\_A 2x dx is a one-dimensional pushforward integral. The density 2x arises because the "fiber" P⁻¹({x}) ∩ supp(μ) = {(x,y) : 0 ≤ y ≤ x} has μ-measure 2x (integrating g = 2 over [0,x]).

---

## Lean 4 Theorem Statements

```lean
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory Set

noncomputable section

/-- The kernel g(x,y) = 2 for 0 ≤ y ≤ x ≤ 1, else 0. -/
def kernel (p : ℝ × ℝ) : ℝ :=
  if 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1 then 2 else 0

/-- The measure μ on ℝ² with density g w.r.t. Lebesgue. -/
def mu : Measure (ℝ × ℝ) :=
  volume.withDensity (fun p => ENNReal.ofReal (kernel p))

/-- The projection P(x,y) = x. -/
def proj : ℝ × ℝ → ℝ := Prod.fst

/-- The pushforward measure τ = μ ∘ P⁻¹. -/
def tau : Measure ℝ := mu.map proj

/-- Step 1: τ has density 2x · 𝟙_{[0,1]} w.r.t. Lebesgue measure. -/
theorem tau_eq_withDensity :
    tau = volume.withDensity
      (fun x => ENNReal.ofReal (2 * x * (Icc (0:ℝ) 1).indicator (fun _ => 1) x)) := by
  sorry

/-- τ applied to a Borel set A equals ∫_{A ∩ [0,1]} 2x dx. -/
theorem tau_apply {A : Set ℝ} (hA : MeasurableSet A) :
    tau A = ENNReal.ofReal (∫ x in A ∩ Icc 0 1, 2 * x ∂volume) := by
  sorry

/-- The Lebesgue decomposition: m = m_ac + m_s where
    m_ac = m restricted to (0,1] and m_s = m restricted to ℝ\(0,1]. -/
theorem lebesgue_decomposition_m_wrt_tau :
    volume = (volume.restrict (Ioc (0:ℝ) 1)) +
             (volume.restrict (Ioc (0:ℝ) 1)ᶜ) := by
  sorry

/-- The absolutely continuous part: m|(0,1] ≪ τ. -/
theorem restrict_Ioc_absolutelyContinuous :
    volume.restrict (Ioc (0:ℝ) 1) ≪ tau := by
  sorry

/-- The singular part: m|_{ℝ\(0,1]} ⊥ τ. -/
theorem restrict_compl_mutuallySingular :
    volume.restrict (Ioc (0:ℝ) 1)ᶜ ⟂ₘ tau := by
  sorry

/-- The Radon-Nikodym derivative dm/dτ = 1/(2x) on (0,1]. -/
theorem rnDeriv_volume_tau :
    ∀ᵐ x ∂tau,
      volume.rnDeriv tau x = ENNReal.ofReal (1 / (2 * x)) := by
  sorry

/-- Verification: ∫_A (1/2x) dτ = m(A) for A ⊆ (0,1]. -/
theorem rnDeriv_integral_eq {A : Set ℝ}
    (hA : MeasurableSet A) (hAsub : A ⊆ Ioc 0 1) :
    ∫⁻ x in A, ENNReal.ofReal (1 / (2 * x)) ∂tau = volume A := by
  sorry

/-- τ is supported on [0,1]: τ(ℝ\[0,1]) = 0. -/
theorem tau_support :
    tau (Icc (0:ℝ) 1)ᶜ = 0 := by
  sorry

/-- Total mass: τ([0,1]) = 1. -/
theorem tau_total :
    tau (Icc (0:ℝ) 1) = 1 := by
  sorry

end
```

**Mathlib notes:**

- `Measure.withDensity μ f` creates the measure with density f w.r.t. μ. `tau` is defined as the pushforward `mu.map proj` and shown to equal `volume.withDensity (fun x => ofReal(2x · 1_{[0,1]}))`.
- `Measure.rnDeriv μ ν` is the Radon-Nikodym derivative dμ/dν, valued in ℝ≥0∞. The statement `rnDeriv volume tau x = ofReal(1/(2x))` is the main computation.
- `Measure.restrict μ s` restricts μ to a set s. The decomposition `volume = volume.restrict (Ioc 0 1) + volume.restrict (Ioc 0 1)ᶜ` splits Lebesgue measure into its absolutely continuous and singular parts w.r.t. τ.
- `μ ≪ ν` is `Measure.AbsolutelyContinuous μ ν`; `μ ⟂ₘ ν` is `Measure.MutuallySingular μ ν`.
- The set `Ioc 0 1 = (0, 1]` is used rather than `Icc 0 1 = [0,1]` because τ({0}) = 0, so {0} contributes nothing to the absolutely continuous part. On `Ioc 0 1`, the density 2x > 0, ensuring mutual absolute continuity.
- `∫⁻ x in A, ... ∂tau` is the Lebesgue integral restricted to A w.r.t. τ.
