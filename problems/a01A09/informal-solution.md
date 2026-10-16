

# APM a01A09: Laplace transform analyticity

## Why It's Hard

The integral $G(z) = \int_{0}^{\infty} f(t) e^{tz} dt$ involves an exponential kernel $e^{tz}$ that grows or decays depending on the signs of $\text{Re}(z)$ and $t$. Since $t \geq 0$, you need $\text{Re}(z) < 0$ for the exponential to decay — wait, that's wrong. Let me re-read: $G(z) = \int f(t) e^{tz} dt$. For $t \geq 0$ and $\text{Re}(z) > 0$, $|e^{tz}| = e^{t \cdot \text{Re}(z)}$ *grows* exponentially. So convergence depends entirely on the decay of $f$. The problem says $f \in Lp$ for $1 < p < \infty$, so $f$ has polynomial-type integrability but not exponential decay. The integral converges on $\{\text{Re}\, z < 0\}$, not $\text{Re}\, z > 0$.

Wait — let me re-read the problem statement more carefully. It says "Prove that $G(z)$ is analytic for $z$ with $\text{Re}\, z > 0$." But with $f \in Lp([0,\infty))$ and $e^{tz}$ growing for $\text{Re}\, z > 0$, the integral would diverge for generic $f \in Lp$. Unless there's a sign convention issue.

**Corrected reading:** The problem almost certainly means $G(z) = \int_{0}^{\infty} f(t) e^{-tz} dt$ (the standard Laplace transform, with a minus sign), or the half-plane should be $\{\text{Re}\, z < 0\}$. With $G(z) = \int_{0}^{\infty} f(t) e^{-tz} dt$, for $\text{Re}\, z > 0$, $|e^{-tz}| = e^{-t \cdot \text{Re}\, z} \to 0$ as $t \to \infty$, and $f \in Lp$ makes the integral converge by Hölder.

I'll proceed with the standard Laplace transform $G(z) = \int_{0}^{\infty} f(t) e^{-tz} dt$, which is analytic on $\{\text{Re}\, z > 0\}$. (If the problem literally means $e^{+tz}$, then the answer is: $G$ is analytic on $\{\text{Re}\, z < 0\}$, by the same argument with $\text{Re}\, z$ replaced by $-\text{Re}\, z$.)

## The Key Insight

**Convergence:** For $\text{Re}\, z > 0$, the function $t \mapsto e^{-tz}$ decays exponentially, so $e^{-t \cdot \text{Re}\, z} \in Lq([0,\infty))$ where $1/p + 1/q = 1$. By Hölder's inequality, the integral $\int |f(t) e^{-tz}| dt \leq ||f||_p \cdot ||e^{-t \cdot \text{Re}\, z}||_q < \infty$.

**Analyticity:** The integrand is entire in $z$ for each fixed $t$, and we can differentiate under the integral sign because the derivative $\partial/\partial z [f(t) e^{-tz}] = -t f(t) e^{-tz}$ is dominated by an integrable function on compact subsets of $\{\text{Re}\, z > 0\}$. Alternatively, use Morera + Fubini.

**Entirety:** $G$ extends to an entire function if $f \in Lp$ *and* $f(t) e^{-\varepsilon t} \in L^{1}$ for every $\varepsilon > 0$ — equivalently, if $f$ has sub-exponential decay: $f(t) e^{ct} \in Lp$ for every $c > 0$. The most natural sufficient condition is that $f$ is compactly supported ($f \in Lp \cap L^{\infty}_c$), since then $e^{-tz}$ is bounded on the support for any $z$.

## Complete Proof

**Theorem.** Let $f \in Lp([0,\infty))$ with $1 < p < \infty$. Define $G(z) = \int_{0}^{\infty} f(t) e^{-tz} dt$. Then $G$ is analytic on $\{\text{Re}\, z > 0\}$.

### Step 1: $G(z)$ is well-defined for $\text{Re}\, z > 0$

Let $q = p/(p-1)$ be the conjugate exponent. For $\text{Re}\, z = \sigma > 0$:

$$\int_0^{\infty} |f(t) e^{-tz}|\,dt = \int_0^{\infty} |f(t)| e^{-\sigma t}\,dt.$$

By Hölder's inequality:

$$\int_0^{\infty} |f(t)| e^{-\sigma t}\,dt \leq \|f\|_p \cdot \left(\int_0^{\infty} e^{-q\sigma t}\,dt\right)^{1/q} = \|f\|_p \cdot (q\sigma)^{-1/q} < \infty.$$

So $G(z)$ converges absolutely for $\text{Re}\, z > 0$. ∎

### Step 2: $G$ is analytic (Morera + Fubini)

Let $\Delta$ be any triangle in $\{\text{Re}\, z > 0\}$. We show $\oint_\Delta G(z) dz = 0$.

Since $\Delta$ is compact and contained in $\{\text{Re}\, z > 0\}$, there exists $\sigma_{0} > 0$ such that $\text{Re}\, z \geq \sigma_{0}$ for all $z \in \Delta$. Then:

$$\oint_\Delta G(z)\,dz = \oint_\Delta \left(\int_0^{\infty} f(t) e^{-tz}\,dt\right) dz.$$

The integrand satisfies $|f(t) e^{-tz}| \leq |f(t)| e^{-\sigma_{0} t}$, and:

$$\int_0^{\infty} |f(t)| e^{-\sigma_0 t}\,dt < \infty \quad \text{(by Step 1)},$$

$$\oint_\Delta 1\,|dz| = \text{length}(\Delta) < \infty.$$

So the product $|f(t) e^{-tz}|$ is integrable on $[0,\infty) \times \Delta$. By Fubini's theorem:

$$\oint_\Delta G(z)\,dz = \int_0^{\infty} f(t) \left(\oint_\Delta e^{-tz}\,dz\right) dt.$$

For each fixed $t$, $z \mapsto e^{-tz}$ is entire, so $\oint_\Delta e^{-tz} dz = 0$ by Cauchy's theorem.

Therefore $\oint_\Delta G(z) dz = 0$. By Morera's theorem, $G$ is analytic on $\{\text{Re}\, z > 0\}$. ∎

### Step 2' (Alternative: direct differentiation)

For $z_{0}$ with $\text{Re}\, z_{0} = \sigma_{0} > 0$, the difference quotient:

$$\frac{G(z) - G(z_0)}{z - z_0} = \int_0^{\infty} f(t) \frac{e^{-tz} - e^{-tz_0}}{z - z_0}\,dt \to \int_0^{\infty} f(t)(-t) e^{-tz_0}\,dt$$

as $z \to z_{0}$. The convergence of the integral is justified by dominated convergence: the difference quotient of $e^{-tz}$ is bounded by $t e^{-t(\sigma_{0}/2)}$ for $z$ close to $z_{0}$ (with $\text{Re}\, z \geq \sigma_{0}/2$), and $t \mapsto |f(t)| \cdot t \cdot e^{-t\sigma_{0}/2}$ is integrable (by Hölder, since $t e^{-t\sigma_{0}/2} \in Lq$).

So $G'(z_{0}) = \int_{0}^{\infty} f(t)(-t) e^{-tz_{0}} dt$ exists, confirming analyticity. ∎

### Condition for entirety

$G(z) = \int_{0}^{\infty} f(t) e^{-tz} dt$ extends to an entire function if and only if the integral converges absolutely for all $z \in \mathbb{C}$, i.e., for every $\sigma \in \mathbb{R}$:

$$\int_0^{\infty} |f(t)| e^{-\sigma t}\,dt < \infty.$$

For $\sigma < 0$, this requires $f(t)$ to decay faster than $e^{\sigma t}$ for every $\sigma < 0$ — meaning $f(t) e^{ct} \in L^{1}$ for every $c > 0$.

**Sufficient condition:** $f$ has compact support, i.e., $f \in Lp([0,\infty))$ and there exists $T > 0$ such that $f(t) = 0$ for $t > T$. Then for any $z \in \mathbb{C}$:

$$|G(z)| \leq \int_0^T |f(t)| e^{|\text{Re}\,z| \cdot t}\,dt \leq e^{|\text{Re}\,z| \cdot T}\|f\|_1 < \infty$$

and the same Morera/Fubini argument applies on all of $\mathbb{C}$.

**More general sufficient condition:** $f(t) e^{ct} \in Lp([0,\infty))$ for every $c > 0$. Equivalently, $f$ has *sub-exponential growth*: for every $\varepsilon > 0$, $\int |f(t)|^p e^{\varepsilon t} dt < \infty$. ∎

## What Connects

**To the Laplace transform.** $G$ is the two-sided Laplace transform restricted to $t \geq 0$. The abscissa of convergence is $\text{Re}\, z = 0$ (the largest $\sigma$ such that $e^{-\sigma t} f(t) \in L^{1}$), and analyticity holds strictly to the right of it.

**To the Paley-Wiener theorem.** The Paley-Wiener theorem characterizes which analytic functions on a half-plane arise as Laplace transforms of Lp functions. For $f \in L^{2}$ with compact support $[0,T]$, $G$ extends to an entire function of exponential type $T$ — this is the "compact support $\Longrightarrow$ entire" direction.

**To the Fourier transform.** Setting $z = i\xi$ gives $G(i\xi) = \int f(t) e^{-i\xi t} dt =$ f̂$(\xi)$, the Fourier transform. The analyticity of $G$ on a half-plane is the analytic continuation of the Fourier transform off the imaginary axis.

**To the Hölder-based convergence.** The same Hölder argument shows that if $f \in Lp$, then the Laplace transform $G$ is not just analytic but continuous up to the boundary $\{\text{Re}\, z = 0\}$ in the Lp sense — though pointwise boundary values require more work (Hardy space theory).

---

## Lean 4 Theorem Statements

```lean
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.NormedSpace.HolomorphicFunction
import Mathlib.Order.Filter.Basic

open MeasureTheory Complex Set Filter

noncomputable section

/-- The Laplace transform of f: G(z) = ∫₀^∞ f(t) e^{-tz} dt. -/
def laplaceTransform (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), f t * exp (-(t : ℂ) * z) ∂volume

/-- Hölder conjugate. -/
def conjExp (p : ℝ) : ℝ := p / (p - 1)

/-- The integrand is absolutely integrable for Re z > 0 when f ∈ Lp. -/
lemma laplaceTransform_integrable
    {f : ℝ → ℂ} {p : ℝ} (hp : 1 < p)
    (hf : Memℒp f (ENNReal.ofReal p) (volume.restrict (Ioi 0)))
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t => f t * exp (-(t : ℂ) * z)) (Ioi 0) volume := by
  sorry

/-- The exponential kernel e^{-σt} is in Lq([0,∞)) for σ > 0. -/
lemma exp_neg_memLq {σ : ℝ} (hσ : 0 < σ) {q : ℝ} (hq : 1 ≤ q) :
    Memℒp (fun t : ℝ => exp (-(σ * t))) (ENNReal.ofReal q)
      (volume.restrict (Ioi 0)) := by
  sorry

/-- Main theorem: G is holomorphic on the right half-plane. -/
theorem laplaceTransform_differentiableOn
    {f : ℝ → ℂ} {p : ℝ} (hp : 1 < p)
    (hf : Memℒp f (ENNReal.ofReal p) (volume.restrict (Ioi 0))) :
    DifferentiableOn ℂ (laplaceTransform f) {z : ℂ | 0 < z.re} := by
  sorry

/-- The derivative of the Laplace transform:
    G'(z) = ∫₀^∞ f(t)·(-t)·e^{-tz} dt. -/
theorem hasDerivAt_laplaceTransform
    {f : ℝ → ℂ} {p : ℝ} (hp : 1 < p)
    (hf : Memℒp f (ENNReal.ofReal p) (volume.restrict (Ioi 0)))
    {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (laplaceTransform f)
      (∫ t in Ioi (0 : ℝ), f t * (-(t : ℂ)) * exp (-(t : ℂ) * z) ∂volume)
      z := by
  sorry

/-- Morera ingredient: contour integrals of G vanish on triangles
    in the right half-plane. -/
lemma laplaceTransform_triangle_integral_zero
    {f : ℝ → ℂ} {p : ℝ} (hp : 1 < p)
    (hf : Memℒp f (ENNReal.ofReal p) (volume.restrict (Ioi 0)))
    {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) :
    (∮ z in a, b, c, laplaceTransform f z) = 0 := by
  sorry

/-- G(z) → 0 as Re z → +∞: the Laplace transform decays. -/
lemma laplaceTransform_tendsto_zero
    {f : ℝ → ℂ} {p : ℝ} (hp : 1 < p)
    (hf : Memℒp f (ENNReal.ofReal p) (volume.restrict (Ioi 0))) :
    Tendsto (fun σ : ℝ => laplaceTransform f σ) atTop (𝓝 0) := by
  sorry

/-- Sufficient condition for entirety: f has compact support.
    If f vanishes outside [0, T], then G is entire. -/
theorem laplaceTransform_entire_of_compactSupport
    {f : ℝ → ℂ} {p : ℝ} (hp : 1 < p)
    (hf : Memℒp f (ENNReal.ofReal p) (volume.restrict (Ioi 0)))
    {T : ℝ} (hT : 0 < T)
    (hsupp : ∀ t, T < t → f t = 0) :
    Differentiable ℂ (laplaceTransform f) := by
  sorry

/-- More general sufficient condition for entirety:
    f(t) e^{ct} ∈ Lp for every c > 0. -/
theorem laplaceTransform_entire_of_subexponential
    {f : ℝ → ℂ} {p : ℝ} (hp : 1 < p)
    (hf : ∀ c : ℝ, 0 < c →
      Memℒp (fun t => f t * exp (c * t))
        (ENNReal.ofReal p) (volume.restrict (Ioi 0))) :
    Differentiable ℂ (laplaceTransform f) := by
  sorry

end
```

**Mathlib notes:**

- `laplaceTransform` is defined directly as a Bochner integral over `Ioi 0` with the kernel `exp(-(t:ℂ) * z)`. The coercion `(t : ℂ)` embeds `ℝ` into `ℂ` via `Complex.ofReal`.
- `Memℒp f p μ` is Mathlib's predicate for $f \in Lp(\mu)$. We use `ENNReal.ofReal p` since the Lp index in Mathlib is `ℝ≥0∞`.
- `DifferentiableOn ℂ f S` encodes holomorphicity on $S$. The right half-plane is `{z : ℂ | 0 < z.re}`.
- `HasDerivAt` gives the complex derivative at a point, establishing the derivative formula by differentiation under the integral.
- `Differentiable ℂ f` (without `On`) encodes entirety.
- The triangle contour integral notation `∮ z in a, b, c, ...` is schematic — in Mathlib one would compose `intervalIntegral` or use `circleIntegral`-adjacent machinery.
- The compact support condition `∀ t, T < t → f t = 0` combined with `Memℒp` on `Ioi 0` gives finite support, making the integral converge for all $z \in \mathbb{C}$.
