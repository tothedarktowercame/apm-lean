

# APM a01A07: $L^{1}$ convergence of analytic functions implies uniform convergence

## 1. Informal proof

**Why it's hard.** The hypothesis is very weak — only $L^{1}$ convergence on disks (area integral), not pointwise or uniform. For generic continuous functions, $L^{1}$ convergence implies nothing about uniform convergence. The gap seems unbridgeable without exploiting the rigid structure of analytic functions.

**The key insight.** The mean value property for analytic functions converts area integrals into pointwise values: $|g(z_{0})| \leq (1/\pi r^{2}) \int_{D(z_{0},r)} |g| dA$. Applied to $g = f_{n} - f_{m}$ (analytic), this bounds sup-norm by $L^{1}$ norm, upgrading $L^{1}$(disk) convergence to uniform convergence on compacts.

**Proof.**

*Step 1: $f_{n} \to F$ uniformly on compact subsets.* Fix compact $K \subset \Omega$. Choose $r > 0$ with $D(z,r) \subset \Omega$ for all $z \in K$ ($r = \text{dist}(K,\partial\Omega)/2$). For $z \in K$, the mean value property gives $f_{n}(z) = (1/\pi r^{2}) \int_{D(z,r)} f_{n} dA$. So:

$f_{n}(z) - F(z) = (1/\pi r^{2}) \int_{D(z,r)} (f_{n} - F) dA + [F(z) − (1/\pi r^{2}) \int_{D(z,r)} F dA] + [(1/\pi r^{2}) \int_{D(z,r)} F dA − F(z)]$.

Wait — cleaner: $|f_{n}(z) - f_{m}(z)| = (1/\pi r^{2})|\int_{D(z,r)} (f_{n}-f_{m}) dA| \leq (1/\pi r^{2}) \int_{D(z,r)} |f_{n}-f_{m}| dA$. Let $D_K$ be a disk containing the $r$-neighbourhood of $K$. Then $\sup_K |f_{n}-f_{m}| \leq (1/\pi r^{2}) \int_{D_K} |f_{n}-f_{m}| dA \leq (1/\pi r^{2})[\int_{D_K} |f_{n}-F| + \int_{D_K} |f_{m}-F|] \to 0$. So $\{f_{n}\}$ is uniformly Cauchy on $K$, converging uniformly to some limit.

For the limit to be $F$: choose $r$ small enough that $|(1/\pi r^{2}) \int_{D(z,r)} F − F(z)| < \epsilon$ (uniform continuity of $F$ on a compact neighbourhood). Then $|f_{n}(z) - F(z)| \leq (1/\pi r^{2}) \int_{D(z,r)} |f_{n}-F| + \epsilon$. The first term $\leq (1/\pi r^{2}) \int_{D_K} |f_{n}-F| \to 0$ uniformly in $z \in K$. So $f_{n} \to F$ uniformly on $K$.

*Step 2: $F$ is analytic.* $F$ is the uniform limit on compacts of analytic functions. By Morera's theorem: for any triangle $\Delta \subset \Omega$, $\oint_\Delta F dz = \lim \oint_\Delta f_{n} dz = 0$ (Cauchy's theorem for each $f_{n}$; limit passes through by uniform convergence). So $F$ is analytic.

*Step 3: $f_{n}' \to F'$ uniformly on compacts.* For $z \in K$, choose $\rho = \text{dist}(K,\partial\Omega)/2$. By the Cauchy integral formula for derivatives: $f_{n}'(z) - F'(z) = (1/2\pi i) \oint_{|w-z|=\rho} (f_{n}(w)-F(w))/(w-z)^{2} dw$. So $|f_{n}'(z)-F'(z)| \leq (1/\rho) \sup_{|w-z|=\rho} |f_{n}(w)-F(w)| \leq (1/\rho) ||f_{n}-F||_{\infty, K_\rho} \to 0$ uniformly in $z \in K$, by Step 1 applied to the compact set $K_\rho$. ∎

**What connects.** This is a strengthened Weierstrass convergence theorem: the classical version assumes uniform convergence on compacts as hypothesis, while this problem proves that for analytic functions, the much weaker $L^{1}$(disk) convergence automatically upgrades to uniform convergence. The engine is the mean value property / sub-mean value inequality for analytic functions, which controls pointwise values by integral averages. The same principle underlies Montel's theorem and the theory of normal families. The result generalises to any class of functions satisfying elliptic regularity estimates (harmonic functions, solutions of elliptic PDE), where interior estimates bound sup-norms by $L^{1}$ norms.

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Order.Filter.Basic

open MeasureTheory Complex Metric Set Filter Topology

noncomputable section

variable {Ω : Set ℂ} (hΩ : IsOpen Ω)

/-- L¹ convergence on disks: ∫_D |fₙ - F| dA → 0 for every closed disk D ⊂ Ω. -/
def L1ConvergesOnDisks (f : ℕ → ℂ → ℂ) (F : ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  ∀ (z : ℂ) (r : ℝ), 0 < r → closedBall z r ⊆ Ω →
    Tendsto (fun n => ∫ w in closedBall z r, ‖f n w - F w‖ ∂volume)
      atTop (𝓝 0)

/-- Mean value inequality: |g(z₀)| ≤ (1/πr²) ∫_{D(z₀,r)} |g| dA
    for g analytic. Controls pointwise values by L¹ averages. -/
lemma norm_le_integral_div_area
    {g : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (closedBall z₀ r)) :
    ‖g z₀‖ ≤ (1 / (Real.pi * r ^ 2)) *
      ∫ w in closedBall z₀ r, ‖g w‖ ∂volume := by
  sorry

/-- Step 1: fₙ → F uniformly on compact subsets. -/
theorem tendstoUniformlyOn_of_L1_on_disks
    {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hf : ∀ n, DifferentiableOn ℂ (f n) Ω)
    (hF : ContinuousOn F Ω)
    (hconv : L1ConvergesOnDisks f F Ω)
    {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    TendstoUniformlyOn f F atTop K := by
  sorry

/-- Step 2: F is analytic (Morera via uniform convergence). -/
theorem differentiableOn_limit
    {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hΩ : IsOpen Ω)
    (hf : ∀ n, DifferentiableOn ℂ (f n) Ω)
    (hF : ContinuousOn F Ω)
    (hconv : L1ConvergesOnDisks f F Ω) :
    DifferentiableOn ℂ F Ω := by
  sorry

/-- Cauchy estimate: ‖g'(z₀)‖ ≤ (1/ρ) sup_{|w-z₀|=ρ} ‖g(w)‖. -/
lemma deriv_norm_le_sup_div_radius
    {g : ℂ → ℂ} {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hg : DifferentiableOn ℂ g (closedBall z₀ ρ))
    {M : ℝ} (hM : ∀ w ∈ closedBall z₀ ρ, ‖g w‖ ≤ M) :
    ‖deriv g z₀‖ ≤ M / ρ := by
  sorry

/-- Step 3: fₙ' → F' uniformly on compact subsets. -/
theorem tendstoUniformlyOn_deriv
    {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hΩ : IsOpen Ω)
    (hf : ∀ n, DifferentiableOn ℂ (f n) Ω)
    (hF : ContinuousOn F Ω)
    (hconv : L1ConvergesOnDisks f F Ω)
    {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    TendstoUniformlyOn (fun n => deriv (f n)) (deriv F) atTop K := by
  sorry

/-- Full theorem packaged. -/
theorem L1_disk_convergence_analytic_upgrade
    {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hΩ : IsOpen Ω)
    (hf : ∀ n, DifferentiableOn ℂ (f n) Ω)
    (hF : ContinuousOn F Ω)
    (hconv : L1ConvergesOnDisks f F Ω) :
    DifferentiableOn ℂ F Ω ∧
    (∀ K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn f F atTop K) ∧
    (∀ K, IsCompact K → K ⊆ Ω →
      TendstoUniformlyOn (fun n => deriv (f n)) (deriv F) atTop K) := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `DifferentiableOn ℂ f Ω` — holomorphicity on $\Omega$ (complex differentiability implies analyticity in Mathlib)
- `ContinuousOn F Ω` — continuity of the limit
- `TendstoUniformlyOn f F atTop K` — uniform convergence on $K$ along $\mathbb{N}$
- `Metric.closedBall z r` — closed disk of radius $r$ centered at $z$
- `MeasureTheory.volume` — Lebesgue measure on $\mathbb{C} \cong \mathbb{R}^{2}$
- `Filter.atTop` — the cofinite filter on $\mathbb{N}$
- `Filter.Tendsto` — convergence along a filter
- `IsCompact`, `IsOpen` — topological predicates

**Key lemmas:**
- `Complex.norm_integral_le_of_norm_le` — bound on contour integrals by sup of integrand
- `Complex.circleIntegral.integral_sub_inv_of_mem_ball` — Cauchy integral formula in Mathlib
- `Complex.deriv_circleIntegral` / related — derivative via Cauchy formula
- `DifferentiableOn.mono` — restriction of differentiability
- `IsCompact.exists_pos_forall_lt` — extracting uniform constants from compact sets (for the radius $r$)
- `IsCompact.subset_interior_iff` / `IsCompact.dist_subset_closure` — compact $K$ has positive distance to $\partial\Omega$
- `MeasureTheory.integral_mono` — monotonicity of integrals (for bounding $L^{1}$ norms)
- `MeasureTheory.integral_add_norm` — triangle inequality for integrals
- `tendstoUniformlyOn_iff` — characterisation of uniform convergence in terms of $\epsilon$-$\delta$
- `Complex.differentiableOn_of_forall_circleIntegral_eq_zero` — Morera's theorem (may not be packaged in Mathlib; would need to be stated)
- `Metric.isCompact_closedBall` — closed disks are compact
- `IsCompact.isBounded` — compact sets are bounded
- `Real.volume_closedBall` — volume of a disk ($\pi r^{2}$)

**Tactic hints:**
- `intro` / `obtain` / `rcases` — unpacking hypotheses and filter convergence
- `calc` — for the chain of inequalities in the mean value estimate
- `gcongr` — for monotonicity-based inequality steps (e.g., bounding integrals)
- `positivity` — for $\pi r^{2} > 0$ and similar
- `exact?` / `apply?` — finding the right Cauchy integral / mean value lemma
- `simp [closedBall]` — set membership simplification
- `linarith` / `nlinarith` — arithmetic combination of $\epsilon$-$\delta$ bounds
- `filter_upwards` — working with the atTop filter for the convergence conclusion