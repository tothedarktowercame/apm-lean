

# APM a95A03: Lp membership, integral, and convolution for |x|⁻²(1+|x|²)⁻¹ in ℝ³

## 1. Informal proof

**Why it's hard.** The function f(x) = |x|⁻²(1+|x|²)⁻¹ has a singularity at the origin (like |x|⁻²) and decay at infinity (like |x|⁻⁴). In ℝ³, determining for which p the Lp integral converges requires balancing these two competing behaviours, and the critical thresholds depend on the dimension n = 3.

**The key insight.** In spherical coordinates, ∫|f|^p = c₃ ∫₀^∞ r⁻²ᵖ(1+r²)⁻ᵖ · r² dr. Near 0, the integrand ~ r²⁻²ᵖ, integrable iff 2-2p > -1 iff p < 3/2. Near ∞, the integrand ~ r²⁻⁴ᵖ, integrable iff 2-4p < -1 iff p > 3/4. So f ∈ Lp iff 3/4 < p < 3/2.

**Proof.**

**(a)** Switch to spherical coordinates in ℝ³: dV = r² sin θ dr dθ dφ, and f depends only on |x| = r:

$$\int_{\mathbb{R}^3} |f(x)|^p = 4\pi \int_0^\infty \frac{r^2}{r^{2p}(1+r^2)^p}\,dr = 4\pi \int_0^\infty \frac{r^{2-2p}}{(1+r^2)^p}\,dr.$$

Near r = 0: integrand ~ r^{2-2p}. Integrable iff 2-2p > -1, i.e., **p < 3/2**.

Near r = ∞: integrand ~ r^{2-2p} · r^{-2p} = r^{2-4p}. Integrable iff 2-4p < -1, i.e., **p > 3/4**.

For p = ∞: ess sup |f| = lim_{|x|→0} |f(x)| = ∞ (since |x|⁻² → ∞). So f ∉ L^∞.

**Answer: f ∈ Lp(ℝ³) iff 3/4 < p < 3/2.**

**(b)** Compute ∫f = 4π ∫₀^∞ r²/(r²(1+r²)) dr = 4π ∫₀^∞ 1/(1+r²) dr = 4π · [arctan r]₀^∞ = 4π · π/2 = **2π²**.

**(c)** By Young's convolution inequality: ||f*g||₂ ≤ ||f||₁ · ||g||₂. From part (b), ||f||₁ = 2π². So f ∈ L¹(ℝ³) (since 3/4 < 1 < 3/2), and:

||f*g||₂ ≤ 2π² ||g||₂.

So c = ||f||₁ = **2π²**. ✓ ∎

**What connects.** This problem combines three fundamental techniques: (1) spherical coordinates for radial functions in ℝⁿ, reducing n-dimensional integrals to 1D; (2) asymptotic analysis of integrands near 0 and ∞ to determine Lp membership; (3) Young's convolution inequality ||f*g||_r ≤ ||f||_p · ||g||_q for convolution bounds. The critical exponents 3/4 and 3/2 come from the dimension n = 3: in general, for f(x) = |x|^{-a}(1+|x|²)^{-b} in ℝⁿ, the Lp condition is (a·p < n) AND ((2b+a)p > n), giving n/(2b+a) < p < n/a. Here a = 2, b = 1, n = 3: 3/4 < p < 3/2.

## 2. Lean 4 theorem statement

```lean
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set Real

noncomputable section

/-- The function f(x) = |x|⁻²(1+|x|²)⁻¹ on ℝ³. -/
def f_radial (x : Fin 3 → ℝ) : ℝ :=
  ‖x‖⁻² * (1 + ‖x‖²)⁻¹

/-- (a) f ∈ Lp(ℝ³) iff 3/4 < p < 3/2. -/
theorem f_radial_memLp_iff {p : ℝ} (hp : 0 < p) :
    Memℒp f_radial (ENNReal.ofReal p) (volume : Measure (Fin 3 → ℝ)) ↔
      3/4 < p ∧ p < 3/2 := by
  sorry

/-- f ∉ L^∞. -/
theorem f_radial_not_memLp_top :
    ¬Memℒp f_radial ⊤ (volume : Measure (Fin 3 → ℝ)) := by
  sorry

/-- (b) ∫_{ℝ³} f = 2π². -/
theorem f_radial_integral :
    ∫ x : Fin 3 → ℝ, f_radial x ∂volume = 2 * π ^ 2 := by
  sorry

/-- Reduction to radial integral:
    ∫_{ℝ³} g(|x|) dx = 4π ∫₀^∞ g(r) r² dr for radial functions. -/
lemma radial_integral_R3 {g : ℝ → ℝ} (hg : Integrable (fun x : Fin 3 → ℝ => g ‖x‖) volume) :
    ∫ x : Fin 3 → ℝ, g ‖x‖ ∂volume =
      4 * π * ∫ r in Ioi (0:ℝ), g r * r ^ 2 ∂volume := by
  sorry

/-- The key 1D integral: ∫₀^∞ 1/(1+r²) dr = π/2. -/
lemma integral_inv_one_plus_sq :
    ∫ r in Ioi (0:ℝ), 1 / (1 + r ^ 2) ∂volume = π / 2 := by
  sorry

/-- (c) ||f * g||₂ ≤ 2π² ||g||₂ by Young's inequality. -/
theorem f_radial_conv_L2_bound
    {g : (Fin 3 → ℝ) → ℝ}
    (hg : Memℒp g 2 (volume : Measure (Fin 3 → ℝ))) :
    eLpNorm (fun x => ∫ y, f_radial (x - y) * g y ∂volume) 2 volume ≤
      ENNReal.ofReal (2 * π ^ 2) * eLpNorm g 2 volume := by
  sorry

/-- f ∈ L¹(ℝ³) (needed for Young's inequality). -/
theorem f_radial_integrable :
    Integrable f_radial (volume : Measure (Fin 3 → ℝ)) := by
  sorry

/-- Young's inequality: ||φ * g||₂ ≤ ||φ||₁ · ||g||₂. -/
lemma young_L1_L2_R3
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : Integrable φ volume)
    {g : (Fin 3 → ℝ) → ℝ} (hg : Memℒp g 2 volume) :
    eLpNorm (fun x => ∫ y, φ (x - y) * g y ∂volume) 2 volume ≤
      eLpNorm φ 1 volume * eLpNorm g 2 volume := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `Fin 3 → ℝ` — ℝ³ (with `volume` as Lebesgue measure via `MeasureTheory.Measure.pi`)
- `MeasureTheory.Memℒp f p μ` — Lp membership
- `MeasureTheory.eLpNorm f p μ` — Lp seminorm
- `MeasureTheory.Integrable f μ` — L¹ membership
- `EuclideanSpace ℝ (Fin 3)` — alternative ℝ³ type
- `ENNReal.ofReal` — real to ℝ≥0∞ coercion

**Key lemmas:**
- `MeasureTheory.integral_comp_rpow_Ioi` / polar coordinate integration — for converting to radial integrals. Exact form may vary
- `Real.integral_inv_one_add_sq` — ∫₋∞^∞ 1/(1+x²) = π (or half-line version = π/2)
- `Real.arctan_tendsto_pi_div_two` — arctan → π/2
- Young's inequality — `MeasureTheory.convolution_le_Lp_mul_L1` or similar
- `norm_rpow_eq_rpow_norm` — ‖x‖^p computations
- `MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt` — layer cake for Lp computation
- `Real.rpow_lt_rpow` — monotonicity of power functions
- `MeasureTheory.integral_pos_of_pos_of_support` — for verifying the integral is positive

**Tactic hints:**
- `rw [radial_integral_R3]` — reducing to 1D
- `simp [f_radial]` — unfolding the definition
- `calc 4 * π * (π / 2) = 2 * π ^ 2 := by ring` — final answer arithmetic
- `constructor <;> intro h` — for the iff in part (a)
- `split_ifs` — for the near-0 vs near-∞ analysis
- `positivity` — for π > 0, r² > 0
- `norm_num` — for 3/4 < 1 < 3/2
- `gcongr` — for monotonicity bounds in the integrability analysis
- `nlinarith` — for combining the exponent conditions