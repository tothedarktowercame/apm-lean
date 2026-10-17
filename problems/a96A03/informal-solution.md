

# APM a96A03: a.e. convergence in $L^{2}$ unit ball implies weak convergence

## 1. Informal proof

**Why it's hard.** A.e. convergence does not imply $L^{2}$ convergence (or even $L^{1}$ convergence on $\mathbb{R}$, which has infinite measure), so we cannot pass to the limit inside $\int f_{n}g$ directly. The $L^{2}$ bound $\|f_{n}\|_{2} \leq 1$ provides uniform control, but combining it with a.e. convergence to get weak convergence requires a density + uniform bound argument.

**The key insight.** $f \in B$ follows from Fatou's lemma. Weak convergence $\langle f_{n}, g \rangle \to \langle f, g \rangle$ follows by approximation: for compactly supported continuous $g$, use DCT on the compact support; for general $g \in L^{2}$, approximate by such functions and use the uniform $L^{2}$ bound $\|f_{n}\|_{2} \leq 1$ to control the error.

**Proof.**

**$f \in B$:** By Fatou's lemma: $\int|f|^{2} = \int \liminf |f_{n}|^{2} \leq \liminf \int|f_{n}|^{2} \leq 1$. So $\|f\|_{2} \leq 1$. ✓

**Weak convergence:** Fix $g \in L^{2}(\mathbb{R})$. We show $\int f_{n}g \to \int fg$.

*Step 1: Compactly supported continuous $g$.* Suppose $g \in Cc(\mathbb{R})$ with $supp(g) \subseteq [-R, R]$. Then $f_{n}g \to fg$ a.e. on $[-R, R]$, and $|f_{n}(x)g(x)| \leq \|g\|_\infty \cdot |f_{n}(x)|$. By Cauchy-Schwarz on $[-R, R]$: $\int_{-R}^R |f_{n}g| \leq \|g\|_\infty \cdot \sqrt{2R} \cdot \|f_{n}\|_{2} \leq \|g\|_\infty \cdot \sqrt{2R}$. So the sequence is uniformly integrable on a finite interval. By the dominated convergence theorem (with dominator $\|g\|_\infty \cdot (|f| + 1)$ or directly via Vitali on the finite interval — but actually we need a fixed $L^{1}$ dominator):

$|f_{n}(x)g(x)| \leq \|g\|_\infty \cdot |f_{n}(x)|$. The trouble is $|f_{n}|$ is not dominated by a single $L^{1}$ function. Use equi-integrability instead: $\{f_{n}g\}$ restricted to $[-R,R]$ is uniformly integrable ($L^{2}$ bounded on finite measure $\Longrightarrow$ equi-integrable in $L^{1}$), and $f_{n}g \to fg$ a.e. By Vitali: $\int f_{n}g \to \int fg$. ✓

*Step 2: General $g \in L^{2}$.* Fix $\varepsilon > 0$. Choose $\varphi \in Cc(\mathbb{R})$ with $\|g - \varphi\|_{2} < \varepsilon/4$. Then:

$|\int f_{n}g - \int fg| \leq |\int f_{n}(g-\varphi)| + |\int f_{n}\varphi - \int f\varphi| + |\int f(\varphi-g)|$

$\leq \|f_{n}\|_{2} \|g-\varphi\|_{2} + |\int f_{n}\varphi - \int f\varphi| + \|f\|_{2} \|\varphi-g\|_{2}$

$\leq 1 \cdot \varepsilon/4 + |\int f_{n}\varphi - \int f\varphi| + 1 \cdot \varepsilon/4$.

By Step 1, $|\int f_{n}\varphi - \int f\varphi| < \varepsilon/2$ for $n$ large. Total: $< \varepsilon$. ✓ ∎

**What connects.** This is a fundamental result: bounded sequences in $L^{2}$ that converge a.e. converge weakly. It combines Fatou (for the limit being in the ball) with DCT on finite measure + density (for weak convergence). The argument is a template: (1) verify on a dense class ($Cc$), (2) extend by uniform bound (Cauchy-Schwarz with $\|f_{n}\|_{2} \leq 1$). This pattern appears throughout functional analysis — it's the Banach-Steinhaus / density argument for weak convergence. The result is optimal: a.e. convergence + $L^{2}$ boundedness gives weak but generally not strong convergence (the typewriter sequence shows this).

## 2. Lean 4 theorem statement

```lean
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter

noncomputable section

/-- The limit f belongs to the L² unit ball (Fatou). -/
theorem memLp_limit_of_ae_tendsto_bounded
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, Memℒp (f n) 2 volume)
    (hf_bdd : ∀ n, eLpNorm (f n) 2 volume ≤ 1)
    (hae : ∀ᵐ x ∂volume, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Memℒp g 2 volume ∧ eLpNorm g 2 volume ≤ 1 := by
  sorry

/-- Weak convergence: ∫ fₙ h → ∫ f h for all h ∈ L². -/
theorem weak_convergence_of_ae_tendsto_L2_bounded
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n) volume)
    (hgm : AEStronglyMeasurable g volume)
    (hf : ∀ n, Memℒp (f n) 2 volume)
    (hf_bdd : ∀ n, eLpNorm (f n) 2 volume ≤ 1)
    (hae : ∀ᵐ x ∂volume, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    {h : ℝ → ℝ} (hh : Memℒp h 2 volume) :
    Tendsto (fun n => ∫ x, f n x * h x ∂volume)
      atTop (𝓝 (∫ x, g x * h x ∂volume)) := by
  sorry

/-- Step 1: Weak convergence for compactly supported continuous h. -/
lemma weak_conv_Cc
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n) volume)
    (hf : ∀ n, Memℒp (f n) 2 volume)
    (hf_bdd : ∀ n, eLpNorm (f n) 2 volume ≤ 1)
    (hae : ∀ᵐ x ∂volume, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    {h : ℝ → ℝ} (hh_cont : Continuous h) (hh_supp : HasCompactSupport h) :
    Tendsto (fun n => ∫ x, f n x * h x ∂volume)
      atTop (𝓝 (∫ x, g x * h x ∂volume)) := by
  sorry

/-- Density: Cc(ℝ) is dense in L²(ℝ). -/
lemma Cc_dense_in_L2
    {h : ℝ → ℝ} (hh : Memℒp h 2 volume)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧ HasCompactSupport φ ∧
      Memℒp φ 2 volume ∧
      eLpNorm (h - φ) 2 volume < ENNReal.ofReal ε := by
  sorry

/-- Cauchy-Schwarz: |∫ fₙ (h-φ)| ≤ ‖fₙ‖₂ ‖h-φ‖₂ ≤ ‖h-φ‖₂. -/
lemma inner_le_snorm_mul
    {f h : ℝ → ℝ}
    (hf : Memℒp f 2 volume) (hh : Memℒp h 2 volume) :
    ENNReal.ofReal ‖∫ x, f x * h x ∂volume‖ ≤
      eLpNorm f 2 volume * eLpNorm h 2 volume := by
  sorry

/-- Fatou's lemma for Lp norms. -/
lemma eLpNorm_le_liminf_of_ae_tendsto
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n) volume)
    (hgm : AEStronglyMeasurable g volume)
    (hae : ∀ᵐ x ∂volume, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    eLpNorm g 2 volume ≤ atTop.liminf (fun n => eLpNorm (f n) 2 volume) := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `MeasureTheory.Memℒp f 2 volume` — $f \in L^{2}(\mathbb{R})$
- `MeasureTheory.eLpNorm f 2 volume` — $L^{2}$ norm
- `AEStronglyMeasurable` — measurability
- `HasCompactSupport` — compact support
- `Filter.Tendsto`, `Filter.atTop` — convergence

**Key lemmas:**
- `MeasureTheory.eLpNorm_le_liminf_eLpNorm_of_ae_tendsto` — Fatou for $L^p$ norms: $\|g\|_p \leq \liminf \|f_{n}\|_p$. Core for $f \in B$. May exist in `Mathlib.MeasureTheory.Function.LpSeminorm.Basic`
- `MeasureTheory.integral_mul_le_Lp_mul_Lq` — Cauchy-Schwarz / Hölder: $|\int fg| \leq \|f\|_p \|g\|_q$. For the uniform bound on the error term
- `MeasureTheory.tendsto_integral_of_dominated_convergence` — DCT for the compact-support case
- `MeasureTheory.Lp.boundedContinuousFunction_dense` / `MeasureTheory.Lp.hasCompactSupport_dense` — density of $Cc$ in $L^{2}$
- `MeasureTheory.Memℒp.integrable_mul` — $fg$ integrable when $f \in L^p$, $g \in L^q$
- `lintegral_liminf_le` — Fatou's lemma for lintegrals
- `IsCompact.measure_lt_top` — finite measure of compact support (for the DCT dominator)

**Tactic hints:**
- `have h_fatou := eLpNorm_le_liminf_eLpNorm_of_ae_tendsto ...` — Fatou step
- `intro ε hε` — for the $\varepsilon/3$ approximation argument
- `obtain ⟨φ, hφ_cont, hφ_supp, hφ_L2, hφ_approx⟩ := Cc_dense_in_L2 hh hε` — density
- `calc |∫fₙh - ∫gh| ≤ |∫fₙ(h-φ)| + |∫fₙφ - ∫gφ| + |∫g(φ-h)| ≤ ...` — triangle inequality
- `exact inner_le_snorm_mul ...` — Cauchy-Schwarz for the first and third terms
- `exact weak_conv_Cc ... (eventually_of_forall ...)` — DCT for the middle term
- `linarith` — combining $\varepsilon/4 + \varepsilon/2 + \varepsilon/4 = \varepsilon$
- `filter_upwards` — for a.e. convergence statements
- `exact?` — finding Fatou or Hölder