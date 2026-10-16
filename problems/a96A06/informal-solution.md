

# APM a96A06: Taylor coefficients at 0 converge to residue at simple pole $z=1$

## 1. Informal proof

**Why it's hard.** The Taylor coefficients $a_{n} = f^{(n)}(0)/n!$ live at the origin, while the residue lives at $z = 1$. Connecting them requires decomposing $f$ into its polar part and an entire remainder, then showing the entire part's coefficients decay while the polar part's coefficients converge to the residue.

**The key insight.** The residue at $z = 1$ is determined by the contour integral: $\mathrm{Res}(f,1) = (1/2\pi i)\oint_{|z|=2} f(z)dz = (-2\pi i)/(2\pi i) = -1$. Then $f(z) = -1/(z-1) + g(z)$ where $g$ is entire (the singularity is removed). The Taylor coefficients of $-1/(z-1)$ at $z = 0$ are $(-1)\cdot(-1)^{n} = (-1)^{n+1}\ldots$ wait, let me recalculate: the residue from the given integral.

Actually: $\oint_{|z|=2} f(z)dz = 2\pi i \cdot \mathrm{Res}(f,1) = -2\pi i$, so $\mathrm{Res}(f,1) = -1$. Then $f(z) = -1/(z-1) + g(z)$ where $g$ is entire. The Taylor expansion of $-1/(z-1)$ at $z=0$: $-1/(z-1) = 1/(1-z) = \sum z^{n}$. So the $n$-th coefficient is 1. The entire part $g$ has $a_{n}(g) \to 0$ superexponentially. So $a_{n}(f) = 1 + a_{n}(g) \to 1$.

**Proof.**

*Step 1: Compute the residue.* $f$ has a simple pole only at $z = 1$. The residue theorem gives:

$\oint_{|z|=2} f(z)dz = 2\pi i \cdot \mathrm{Res}(f, 1) = -2\pi i$.

So $\mathrm{Res}(f, 1) = -1$.

*Step 2: Decompose $f$.* Write $f(z) = -1/(z-1) + g(z)$ where $g(z) = f(z) + 1/(z-1)$. Since $f$ has a simple pole at $z = 1$ with residue $-1$, the function $g$ has a removable singularity at $z = 1$ (the pole is cancelled). So $g$ is entire.

*Step 3: Taylor coefficients of $-1/(z-1)$.* Using the geometric series:

$-1/(z-1) = 1/(1-z) = \sum_{n=0}^{\infty} z^{n}$ for $|z| < 1$.

So the $n$-th Taylor coefficient ($= f^{(n)}(0)/n!$ for this term) is 1.

*Step 4: Taylor coefficients of $g$ decay.* $g$ is entire, hence analytic on any disk $D(0,R)$. By the Cauchy estimates on $D(0,R)$ for any $R > 1$:

$|g^{(n)}(0)/n!| \leq \max_{|z|=R} |g(z)| / R^{n} = M(R)/R^{n}$.

Since $R > 1$, this $\to 0$ as $n \to \infty$.

*Step 5: Combine.* $f^{(n)}(0)/n! = 1 + g^{(n)}(0)/n! \to 1 + 0 = 1$. ✓ ∎

**What connects.** This is essentially the same as a01J04 and a97J05: the Taylor coefficients of a function with a simple pole at $z = 1$ and no other singularity inside $|z| < R$ ($R > 1$) are asymptotic to the geometric series coefficients of the polar part. The entire remainder $g$ has coefficients decaying faster than any $R^{-n}$ (since $g$ is entire, its radius of convergence is $\infty$). The result is a basic instance of singularity analysis in analytic combinatorics: the dominant singularity at $z = 1$ determines the leading asymptotics of the coefficients, and the sign of the residue ($-1$ here) combined with the Laurent expansion of $1/(z-1)$ gives the limiting value.

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity

open Complex Filter

noncomputable section

/-- Main theorem: f^{(n)}(0)/n! → 1. -/
theorem taylor_coeffs_tend_to_one
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f {(1 : ℂ)}ᶜ)
    (hf_pole : ∃ c : ℂ, c ≠ 0 ∧ DifferentiableAt ℂ (fun z => (z - 1) * f z - c) 1)
    (hf_int : ∮ z in C(0, 2), f z = -(2 * π * I)) :
    Tendsto (fun n => iteratedDeriv n f 0 / ↑(n !))
      atTop (𝓝 1) := by
  sorry

/-- The residue at z = 1 is -1. -/
lemma residue_eq_neg_one
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f {(1 : ℂ)}ᶜ)
    (hf_pole : ∃ c : ℂ, c ≠ 0 ∧ DifferentiableAt ℂ (fun z => (z - 1) * f z - c) 1)
    (hf_int : ∮ z in C(0, 2), f z = -(2 * π * I)) :
    -- The residue Res(f, 1) = lim_{z→1} (z-1)f(z) = -1
    Tendsto (fun z => (z - 1) * f z) (𝓝[≠] 1) (𝓝 (-1)) := by
  sorry

/-- The entire part g = f + 1/(z-1) is entire. -/
lemma entire_part_differentiable
    {f : ℂ → ℂ}
    (hf_holo : DifferentiableOn ℂ f {(1 : ℂ)}ᶜ)
    (hf_res : Tendsto (fun z => (z - 1) * f z) (𝓝[≠] 1) (𝓝 (-1))) :
    Differentiable ℂ (fun z => f z + 1 / (z - 1)) := by
  sorry

/-- Taylor coefficients of 1/(1-z) are all 1. -/
lemma geom_series_coeff (n : ℕ) :
    iteratedDeriv n (fun z : ℂ => 1 / (1 - z)) 0 / ↑(n !) = 1 := by
  sorry

/-- Taylor coefficients of an entire function decay superexponentially. -/
lemma entire_coeffs_tendsto_zero
    {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Tendsto (fun n => iteratedDeriv n g 0 / ↑(n !)) atTop (𝓝 0) := by
  sorry

/-- Cauchy estimate: |g^{(n)}(0)/n!| ≤ M(R)/R^n. -/
lemma cauchy_estimate_entire
    {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {R : ℝ} (hR : 0 < R) :
    ‖iteratedDeriv n g 0 / ↑(n !)‖ ≤
      (⨆ w ∈ Metric.sphere (0 : ℂ) R, ‖g w‖) / R ^ n := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `DifferentiableOn ℂ f {1}ᶜ` — holomorphic except at $z = 1$
- `Differentiable ℂ g` — entire function (for the remainder)
- `circleIntegral` / `∮ z in C(0, 2)` — contour integral
- `iteratedDeriv n f 0` — $n$-th derivative at 0
- `Filter.Tendsto`, `Filter.atTop` — convergence

**Key lemmas:**
- `Complex.circleIntegral_sub_inv_of_mem_ball` — $\oint 1/(z-a) = 2\pi i$ for $a$ inside circle. Gives the residue theorem for simple poles
- `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` — Cauchy estimate $|f^{(n)}(0)/n!| \leq M/R^{n}$. In `Mathlib.Analysis.Complex.CauchyIntegral`
- `Complex.differentiableOn_update_of_bounded` — removable singularity theorem: bounded near a point $\Longrightarrow$ extends analytically. For showing $g$ is entire
- `hasSum_geometric_of_norm_lt_one` — $\sum z^{n} = 1/(1-z)$ for $|z| < 1$ (for the geometric series coefficients)
- `tendsto_pow_atTop_nhds_zero_of_lt_one` — $R^{-n} \to 0$ for $R > 1$ (for the Cauchy estimate decay)
- `Tendsto.add` — sum of convergent sequences converges to sum of limits

**Tactic hints:**
- `have h_res := residue_eq_neg_one ...` — compute residue $= -1$
- `have h_ent := entire_part_differentiable ...` — $g$ is entire
- `have h_decay := entire_coeffs_tendsto_zero h_ent` — $g$'s coefficients $\to 0$
- `calc f⁽ⁿ⁾(0)/n! = (1/(1-z))⁽ⁿ⁾(0)/n! + g⁽ⁿ⁾(0)/n! = 1 + g⁽ⁿ⁾(0)/n!` — decomposition
- `exact Tendsto.add tendsto_const_nhds h_decay` — $1 + 0 \to 1$
- `norm_num` — for $(-2\pi i)/(2\pi i) = -1$
- `simp [geom_series_coeff]` — for the coefficient of $1/(1-z)$
- `exact?` — finding Cauchy estimate or removable singularity