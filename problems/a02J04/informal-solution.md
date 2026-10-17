

# APM a02J04: Lebesgue decomposition of Lebesgue measure w.r.t. a pushforward measure

## Why It's Hard

The problem asks for the Lebesgue decomposition of $m$ with respect to $\tau$ (not $\tau$ w.r.t. $m$, which would be more standard). Since $\tau$ is supported on $[0,1]$ and Lebesgue measure $m$ lives on all of $\mathbb{R}$, $m$ has a large singular part (everything outside $[0,1]$) and a potentially absolutely continuous part on $[0,1]$. The computation requires first identifying $\tau$ explicitly, then decomposing $m = m_{ac} + m_s$ where $m_{ac} \ll \tau$ and $m_s \perp \tau$.

## The Key Insight

**Compute $\tau$ explicitly.** For a Borel set $A \subset \mathbb{R}$:

$$\tau(A) = \mu(P^{-1}(A)) = \int\int_{P^{-1}(A)} g(x,y)\,dx\,dy = \int_A \left(\int_0^x 2\,dy\right) dx = \int_A 2x\,dx$$

for $A \subset [0,1]$ (and $\tau(A) = 0$ for $A \subset \mathbb{R} \setminus [0,1]$). So **$d\tau = 2x \cdot 1_{[0,1]}(x) dx$** — the measure $\tau$ is absolutely continuous with respect to Lebesgue measure on $[0,1]$ with density $2x$.

Now we need the decomposition in the *other* direction: $m$ w.r.t. $\tau$. On $[0,1]$, $\tau$ has density $2x$ w.r.t. $m$, so $\tau \ll m$ there. For the reverse: $m \ll \tau$ on $(0,1]$ (since $\tau$ has positive density there), but $m(\{0\}) = 0 = \tau(\{0\})$ so this is fine. On $\mathbb{R} \setminus [0,1]$, $\tau = 0$ but $m$ is nonzero, so that part is singular.

## Complete Proof

### Step 1: Compute $\tau$

For a Borel set $A \subset \mathbb{R}$:

$$\tau(A) = \mu(P^{-1}(A)) = \iint_{\{(x,y): x \in A,\, 0 \leq y \leq x \leq 1\}} 2\,dx\,dy.$$

The region $\{(x,y) : x \in A, 0 \leq y \leq x \leq 1\}$ has $x \in A \cap [0,1]$ and $y \in [0,x]$. By Fubini:

$$\tau(A) = \int_{A \cap [0,1]}\left(\int_0^x 2\,dy\right)dx = \int_{A \cap [0,1]} 2x\,dx.$$

So $\tau$ is the measure with density $h(x) = 2x \cdot 1_{[0,1]}(x)$ with respect to Lebesgue measure $m$:

$$d\tau = 2x \cdot \mathbf{1}_{[0,1]}(x)\,dx.$$

Note: $\tau$ is supported on $[0,1]$, and $\tau(\{0\}) = 0$, $\tau([0,1]) = \int_{0}^{1} 2x dx = 1$.

### Step 2: Lebesgue decomposition of $m$ w.r.t. $\tau$

We write $m = m_{ac} + m_s$ where $m_{ac} \ll \tau$ and $m_s \perp \tau$.

**Singular part.** $\tau$ is supported on $[0,1]$ (in fact on $(0,1]$, since $\tau(\{0\}) = 0$). So $\tau(\mathbb{R} \setminus (0,1]) = 0$. Therefore $m$ restricted to $\mathbb{R} \setminus (0,1]$ is singular with respect to $\tau$:

$$m_s = m|_{\mathbb{R} \setminus (0,1]}.$$

In other words, $m_s(A) = m(A \cap (\mathbb{R} \setminus (0,1])) = m(A \setminus (0,1])$.

**Absolutely continuous part.** On $(0,1]$, $\tau$ has density $2x > 0$ with respect to $m$. So $m$ is absolutely continuous w.r.t. $\tau$ on $(0,1]$:

$$m_{ac} = m|_{(0,1]}.$$

For $A \subset (0,1]$, if $\tau(A) = 0$, then $\int_A 2x dx = 0$, which (since $2x > 0$ on $(0,1]$) implies $m(A) = 0$. So $m_{ac} \ll \tau$. ✓

**Verification of singularity.** $m_s$ is supported on $\mathbb{R} \setminus (0,1]$, and $\tau$ is supported on $(0,1]$. So $m_s$ and $\tau$ are mutually singular. ✓

### Step 3: Radon-Nikodym derivative $dm_{ac}/d\tau$

For $A \subset (0,1]$:

$$m_{ac}(A) = m(A) = \int_A 1\,dx = \int_A \frac{1}{2x}\cdot 2x\,dx = \int_A \frac{1}{2x}\,d\tau(x).$$

So the Radon-Nikodym derivative is:

$$\frac{dm}{d\tau}(x) = \frac{1}{2x}, \quad x \in (0,1].$$

**Verification:** $\int_A (1/2x) d\tau = \int_A (1/2x) \cdot 2x dx = \int_A 1 dx = m(A)$. ✓

### Summary

$$\boxed{m = m_{ac} + m_s, \quad m_{ac} = m|_{(0,1]}, \quad m_s = m|_{\mathbb{R}\setminus(0,1]}, \quad \frac{dm}{d\tau}(x) = \frac{1}{2x}.}$$

## What Connects

**To the pushforward measure.** $\tau = \mu \circ P^{-1}$ is the marginal of $\mu$ on the first coordinate. Computing pushforward measures is fundamental in probability (marginal distributions) and in geometric measure theory (projections of measures).

**To the Radon-Nikodym theorem.** The decomposition $m = m_{ac} + m_s$ is guaranteed by the Lebesgue decomposition theorem. The Radon-Nikodym derivative $dm/d\tau = 1/(2x)$ is the reciprocal of $d\tau/dm = 2x$ — this reciprocal relationship holds whenever both measures are mutually absolutely continuous on a set.

**To Bayes' theorem.** The density $d\tau/dm = 2x$ and $dm/d\tau = 1/(2x)$ are related like a prior and a likelihood: if $\tau$ is a "prior" weighting that favours larger $x$, then the Radon-Nikodym derivative $dm/d\tau = 1/(2x)$ is the "re-weighting" needed to recover uniform measure from the biased one.

**To the change-of-variables formula.** The computation $\tau(A) = \int_A 2x dx$ is a one-dimensional pushforward integral. The density $2x$ arises because the "fiber" $P^{-1}(\{x\}) \cap supp(\mu) = \{(x,y) : 0 \leq y \leq x\}$ has $\mu$-measure $2x$ (integrating $g = 2$ over $[0,x]$).

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

- `Measure.withDensity μ f` creates the measure with density $f$ w.r.t. $\mu$. `tau` is defined as the pushforward `mu.map proj` and shown to equal `volume.withDensity (fun x => ofReal(2x · 1_{[0,1]}))`.
- `Measure.rnDeriv μ ν` is the Radon-Nikodym derivative $d\mu/d\nu$, valued in $\mathbb{R}_{\geq 0}\infty$. The statement `rnDeriv volume tau x = ofReal(1/(2x))` is the main computation.
- `Measure.restrict μ s` restricts $\mu$ to a set $s$. The decomposition `volume = volume.restrict (Ioc 0 1) + volume.restrict (Ioc 0 1)ᶜ` splits Lebesgue measure into its absolutely continuous and singular parts w.r.t. $\tau$.
- `μ ≪ ν` is `Measure.AbsolutelyContinuous μ ν`; `μ ⟂ₘ ν` is `Measure.MutuallySingular μ ν`.
- The set `Ioc 0 1 = (0, 1]` is used rather than `Icc 0 1 = [0,1]` because $\tau(\{0\}) = 0$, so $\{0\}$ contributes nothing to the absolutely continuous part. On `Ioc 0 1`, the density $2x > 0$, ensuring mutual absolute continuity.
- `∫⁻ x in A, ... ∂tau` is the Lebesgue integral restricted to $A$ w.r.t. $\tau$.
