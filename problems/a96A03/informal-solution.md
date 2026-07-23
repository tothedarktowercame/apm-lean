

# APM a96A03: a.e. convergence in L² unit ball implies weak convergence

## 1. Informal proof

**Why it's hard.** A.e. convergence does not imply L² convergence (or even L¹ convergence on ℝ, which has infinite measure), so we cannot pass to the limit inside ∫fₙg directly. The L² bound ||fₙ||₂ ≤ 1 provides uniform control, but combining it with a.e. convergence to get weak convergence requires a density + uniform bound argument.

**The key insight.** f ∈ B follows from Fatou's lemma. Weak convergence ⟨fₙ, g⟩ → ⟨f, g⟩ follows by approximation: for compactly supported continuous g, use DCT on the compact support; for general g ∈ L², approximate by such functions and use the uniform L² bound ||fₙ||₂ ≤ 1 to control the error.

**Proof.**

**f ∈ B:** By Fatou's lemma: ∫|f|² = ∫ lim inf |fₙ|² ≤ lim inf ∫|fₙ|² ≤ 1. So ||f||₂ ≤ 1. ✓

**Weak convergence:** Fix g ∈ L²(ℝ). We show ∫fₙg → ∫fg.

*Step 1: Compactly supported continuous g.* Suppose g ∈ Cc(ℝ) with supp(g) ⊆ [-R, R]. Then fₙg → fg a.e. on [-R, R], and |fₙ(x)g(x)| ≤ ||g||∞ · |fₙ(x)|. By Cauchy-Schwarz on [-R, R]: ∫_{-R}^R |fₙg| ≤ ||g||∞ · √(2R) · ||fₙ||₂ ≤ ||g||∞ · √(2R). So the sequence is uniformly integrable on a finite interval. By the dominated convergence theorem (with dominator ||g||∞ · (|f| + 1) or directly via Vitali on the finite interval — but actually we need a fixed L¹ dominator):

|fₙ(x)g(x)| ≤ ||g||∞ · |fₙ(x)|. The trouble is |fₙ| is not dominated by a single L¹ function. Use equi-integrability instead: {fₙg} restricted to [-R,R] is uniformly integrable (L² bounded on finite measure ⟹ equi-integrable in L¹), and fₙg → fg a.e. By Vitali: ∫fₙg → ∫fg. ✓

*Step 2: General g ∈ L².* Fix ε > 0. Choose φ ∈ Cc(ℝ) with ||g - φ||₂ < ε/4. Then:

|∫fₙg - ∫fg| ≤ |∫fₙ(g-φ)| + |∫fₙφ - ∫fφ| + |∫f(φ-g)|

≤ ||fₙ||₂ ||g-φ||₂ + |∫fₙφ - ∫fφ| + ||f||₂ ||φ-g||₂

≤ 1 · ε/4 + |∫fₙφ - ∫fφ| + 1 · ε/4.

By Step 1, |∫fₙφ - ∫fφ| < ε/2 for n large. Total: < ε. ✓ ∎

**What connects.** This is a fundamental result: bounded sequences in L² that converge a.e. converge weakly. It combines Fatou (for the limit being in the ball) with DCT on finite measure + density (for weak convergence). The argument is a template: (1) verify on a dense class (Cc), (2) extend by uniform bound (Cauchy-Schwarz with ||fₙ||₂ ≤ 1). This pattern appears throughout functional analysis — it's the Banach-Steinhaus / density argument for weak convergence. The result is optimal: a.e. convergence + L² boundedness gives weak but generally not strong convergence (the typewriter sequence shows this).

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
- `MeasureTheory.Memℒp f 2 volume` — f ∈ L²(ℝ)
- `MeasureTheory.eLpNorm f 2 volume` — L² norm
- `AEStronglyMeasurable` — measurability
- `HasCompactSupport` — compact support
- `Filter.Tendsto`, `Filter.atTop` — convergence

**Key lemmas:**
- `MeasureTheory.eLpNorm_le_liminf_eLpNorm_of_ae_tendsto` — Fatou for Lp norms: ||g||_p ≤ lim inf ||fₙ||_p. Core for f ∈ B. May exist in `Mathlib.MeasureTheory.Function.LpSeminorm.Basic`
- `MeasureTheory.integral_mul_le_Lp_mul_Lq` — Cauchy-Schwarz / Hölder: |∫fg| ≤ ||f||_p ||g||_q. For the uniform bound on the error term
- `MeasureTheory.tendsto_integral_of_dominated_convergence` — DCT for the compact-support case
- `MeasureTheory.Lp.boundedContinuousFunction_dense` / `MeasureTheory.Lp.hasCompactSupport_dense` — density of Cc in L²
- `MeasureTheory.Memℒp.integrable_mul` — fg integrable when f ∈ Lp, g ∈ Lq
- `lintegral_liminf_le` — Fatou's lemma for lintegrals
- `IsCompact.measure_lt_top` — finite measure of compact support (for the DCT dominator)

**Tactic hints:**
- `have h_fatou := eLpNorm_le_liminf_eLpNorm_of_ae_tendsto ...` — Fatou step
- `intro ε hε` — for the ε/3 approximation argument
- `obtain ⟨φ, hφ_cont, hφ_supp, hφ_L2, hφ_approx⟩ := Cc_dense_in_L2 hh hε` — density
- `calc |∫fₙh - ∫gh| ≤ |∫fₙ(h-φ)| + |∫fₙφ - ∫gφ| + |∫g(φ-h)| ≤ ...` — triangle inequality
- `exact inner_le_snorm_mul ...` — Cauchy-Schwarz for the first and third terms
- `exact weak_conv_Cc ... (eventually_of_forall ...)` — DCT for the middle term
- `linarith` — combining ε/4 + ε/2 + ε/4 = ε
- `filter_upwards` — for a.e. convergence statements
- `exact?` — finding Fatou or Hölder