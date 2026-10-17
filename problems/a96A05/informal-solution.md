

# APM a96A05: $1/z$ cannot be uniformly approximated by polynomials on the unit circle

## 1. Informal proof

**Why it's hard.** The function $1/z$ is continuous on the unit circle, and by Weierstrass (or Stone-Weierstrass for the disk), polynomials are dense in $C(\partial\Delta)$ in the sup norm. But $1/z$ is NOT in the uniform closure of polynomials on the circle — this seems to contradict density, and the resolution requires understanding which functions polynomials can approximate.

**The key insight.** Use the integral: $\oint_{|z|=1} (1/z - P(z)) dz/(2\pi i)$. The integral of $1/z$ on the unit circle is $2\pi i$ (winding number 1), while the integral of any polynomial $P(z)$ is 0 (Cauchy's theorem — $P$ is entire). So the integral of $(1/z - P(z))$ is 1 (after dividing by $2\pi i$), and the sup norm controls the integral via $|\oint g dz| \leq \sup|g| \cdot \text{length}$.

**Proof.**

For any polynomial $P \in \mathbb{C}[z]$, consider the contour integral:

$$\frac{1}{2\pi i}\oint_{|z|=1}\left(\frac{1}{z} - P(z)\right)dz.$$

*Evaluate each part:*

- $\oint (1/z) dz = 2\pi i$ (the winding number of the unit circle around 0).
- $\oint P(z) dz = 0$ ($P$ is entire, so Cauchy's theorem gives zero for any closed contour).

So: $(1/2\pi i) \oint (1/z - P(z)) dz = 1$.

*Bound the integral by the sup norm:*

$$1 = \left|\frac{1}{2\pi i}\oint_{|z|=1}\left(\frac{1}{z} - P(z)\right)dz\right| \leq \frac{1}{2\pi}\cdot \sup_{|z|=1}\left|\frac{1}{z} - P(z)\right| \cdot 2\pi = \sup_{|z|=1}\left|\frac{1}{z} - P(z)\right|.$$

Therefore $\sup_{|z|=1} |1/z - P(z)| \geq 1$. ∎

**What connects.** This is a fundamental result in approximation theory on the complex plane. Polynomials are dense in $C(K)$ for compact $K \subset \mathbb{C}$ if and only if $\mathbb{C} \setminus K$ is connected (Mergelyan's theorem). For $K =$ the unit circle, $\mathbb{C} \setminus K$ has two components (the disk and its complement), so polynomials are NOT dense in $C(\partial\Delta)$. The function $1/z$ is the canonical example of a function that cannot be approximated: it has a nonzero "analytic content" (the integral $(1/2\pi i)\oint g dz$ is a continuous linear functional that vanishes on polynomials but not on $1/z$). This is also related to the Hahn-Banach theorem: the functional $\lambda(g) = (1/2\pi i)\oint g dz$ separates $1/z$ from the closure of polynomials, with $\lambda(1/z) = 1$ and $\lambda(P) = 0$. The bound 1 is sharp: one cannot do better than distance 1 from $1/z$ to any polynomial on the circle.

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.Complex.CauchyIntegral

open Complex Polynomial Metric

noncomputable section

/-- Main theorem: sup_{|z|=1} |1/z - P(z)| ≥ 1 for any polynomial P. -/
theorem sup_inv_sub_polynomial_ge_one
    (P : ℂ[X]) :
    1 ≤ ⨆ z ∈ sphere (0 : ℂ) 1, ‖z⁻¹ - Polynomial.aeval z P‖ := by
  sorry

/-- Equivalent: the distance from 1/z to the set of polynomials
    in C(∂Δ) is at least 1. -/
theorem dist_inv_polynomials_ge_one :
    ∀ P : ℂ[X], 1 ≤ sSup ((fun z => ‖z⁻¹ - Polynomial.aeval z P‖) '' sphere (0 : ℂ) 1) := by
  sorry

/-- The contour integral of 1/z over the unit circle is 2πi. -/
lemma circleIntegral_inv :
    ∮ z in C(0, 1), z⁻¹ = 2 * π * I := by
  sorry

/-- The contour integral of any polynomial over the unit circle is 0. -/
lemma circleIntegral_polynomial (P : ℂ[X]) :
    ∮ z in C(0, 1), Polynomial.aeval z P = 0 := by
  sorry

/-- Therefore the contour integral of (1/z - P(z)) equals 2πi. -/
lemma circleIntegral_inv_sub_polynomial (P : ℂ[X]) :
    ∮ z in C(0, 1), (fun z => z⁻¹ - Polynomial.aeval z P) z = 2 * π * I := by
  sorry

/-- The ML inequality: |∮_C f dz| ≤ sup|f| · length(C). -/
lemma norm_circleIntegral_le_sup_mul_length
    {f : ℂ → ℂ} (hf : ContinuousOn f (sphere 0 1))
    {R : ℝ} (hR : 0 < R) :
    ‖∮ z in C(0, R), f z‖ ≤
      (⨆ z ∈ sphere (0 : ℂ) R, ‖f z‖) * (2 * π * R) := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `Polynomial ℂ` / `ℂ[X]` — complex polynomials
- `Polynomial.aeval z P` — polynomial evaluation
- `circleIntegral` / `∮ z in C(0, 1)` — contour integral over the unit circle
- `Metric.sphere (0 : ℂ) 1` — the unit circle
- `iSup` / `⨆` — supremum over a set

**Key lemmas:**
- `Complex.circleIntegral_sub_inv_of_mem_ball` — $\oint 1/(z-a) dz = 2\pi i$ for $a$ inside the circle. Specialised to $a = 0$, this gives $\oint 1/z dz = 2\pi i$
- `Complex.circleIntegral_eq_zero_of_differentiableOn` — Cauchy's theorem: $\oint P(z) dz = 0$ for entire $P$
- `Complex.norm_circleIntegral_le_of_norm_le` — the ML inequality: $\|\oint f dz\| \leq M \cdot 2\pi R$ when $\|f\| \leq M$ on the circle
- `Polynomial.aeval_eq_sum` — evaluation as sum of monomials
- `ContinuousOn.polynomial` / `Polynomial.continuousOn` — polynomials are continuous (for sup norm being well-defined)
- `isCompact_sphere` — sphere is compact (for sup being attained)
- `IsCompact.sSup_lt_iff_of_continuous` — continuous function on compact set attains its sup

**Tactic hints:**
- `have h1 := circleIntegral_inv` — $\oint 1/z = 2\pi i$
- `have h2 := circleIntegral_polynomial P` — $\oint P = 0$
- `have h3 : ‖2 * π * I‖ = 2 * π := by simp [Complex.norm_mul, Complex.norm_I]` — computing $|2\pi i|$
- `calc 2 * π = ‖∮ (1/z - P)‖ ≤ sup · 2π` — ML inequality chain
- `linarith` — dividing by $2\pi$
- `norm_num` — for $2\pi > 0$
- `simp [circleIntegral_sub, h1, h2]` — splitting the contour integral
- `positivity` — for $\pi > 0$
- `exact?` — finding the Cauchy theorem or ML inequality