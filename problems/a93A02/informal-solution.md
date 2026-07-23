

# APM a93A02: L²-bounded a.e. convergent sequence converges in Lp for p < 2

## 1. Informal proof

**Why it's hard.** A.e. convergence alone doesn't imply Lp convergence (typewriter sequence). L² boundedness alone doesn't either. Together they give Lp convergence for p < 2 but *not* for p = 2 — so the strict inequality p < 2 is essential and must be used somewhere in the proof.

**The key insight.** Use Vitali's convergence theorem: on a finite measure space, a.e. convergence + uniform integrability ⟹ L¹ convergence. The L² bound provides uniform integrability of |fₙ - f|^p via Hölder (since p < 2, the Lp integrability is "buffered" by the L² margin). Alternatively, use Egorov + Hölder directly.

**Proof.**

*Step 0: f ∈ L² (hence Lp).* By Fatou's lemma, ∫|f|² ≤ lim inf ∫|fₙ|² ≤ (sup ||fₙ||₂)² < ∞. So f ∈ L²([0,1]). Since [0,1] has finite measure and p < 2, L² ⊂ Lp, so f ∈ Lp.

*Step 1: Uniform integrability of |fₙ - f|^p.* Set M = sup ||fₙ||₂. For any measurable E ⊆ [0,1], by Hölder with exponents 2/p and 2/(2-p) (conjugate since p/2 + (2-p)/2 = 1):

∫_E |fₙ - f|^p ≤ (∫_E |fₙ-f|²)^{p/2} · m(E)^{(2-p)/2} ≤ (∫|fₙ-f|²)^{p/2} · m(E)^{(2-p)/2}.

Now ∫|fₙ-f|² ≤ 2∫|fₙ|² + 2∫|f|² ≤ 2M² + 2M² = 4M² (by (a+b)² ≤ 2a² + 2b²). So:

∫_E |fₙ - f|^p ≤ (4M²)^{p/2} · m(E)^{(2-p)/2} = C · m(E)^{(2-p)/2}.

Since (2-p)/2 > 0, this → 0 as m(E) → 0 uniformly in n. This is uniform integrability of |fₙ - f|^p.

*Step 2: A.e. convergence of |fₙ - f|^p.* Since fₙ → f a.e., |fₙ - f|^p → 0 a.e.

*Step 3: Apply Vitali.* On [0,1] (finite measure), |fₙ - f|^p → 0 a.e. and {|fₙ - f|^p} is uniformly integrable. By the Vitali convergence theorem:

∫|fₙ - f|^p → 0, i.e., ||fₙ - f||_p → 0. ✓

*Counterexample for p = 2:* Let fₙ = √n · 1_{[0,1/n]}. Then ||fₙ||₂ = 1 for all n, and fₙ → 0 a.e. (since fₙ(x) = 0 for x > 1/n). But ||fₙ - 0||₂ = 1 ↛ 0. So L² convergence fails despite a.e. convergence and bounded L² norms. ✓ ∎

**What connects.** This is a special case of the general interpolation principle: on a finite measure space, L²-bounded sequences that converge a.e. converge in Lp for all p < 2. The mechanism is that L² boundedness provides "room" for uniform integrability at any lower exponent, and Vitali's theorem converts a.e. convergence + uniform integrability into norm convergence. The counterexample for p = 2 shows this room vanishes at the critical exponent: concentration on shrinking sets (fₙ = √n · 1_{[0,1/n]}) preserves the L² norm while converging to 0 a.e. The result generalises: if ||fₙ||_q ≤ M and fₙ → f a.e. on a finite measure space, then fₙ → f in Lp for all p < q. The Dunford-Pettis theorem provides the abstract framework: L^q-bounded families on finite measure spaces are uniformly integrable in Lp for p < q.

## 2. Lean 4 theorem statement

```lean
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set Filter ENNReal

noncomputable section

variable {μ : Measure ℝ := volume.restrict (Icc 0 1)}

/-- The limit f is in L² by Fatou. -/
lemma memLp_limit_of_ae_tendsto_of_L2_bounded
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, Memℒp (f n) 2 (volume.restrict (Icc 0 1)))
    (hbdd : ∃ M, ∀ n, eLpNorm (f n) 2 (volume.restrict (Icc 0 1)) ≤ M)
    (hae : ∀ᵐ x ∂(volume.restrict (Icc (0:ℝ) 1)),
      Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Memℒp g 2 (volume.restrict (Icc 0 1)) := by
  sorry

/-- Uniform integrability of |fₙ - f|^p from L² boundedness when p < 2. -/
lemma uniformIntegrable_sub_rpow
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, Memℒp (f n) 2 (volume.restrict (Icc 0 1)))
    (hg : Memℒp g 2 (volume.restrict (Icc 0 1)))
    (hbdd : ∃ M, ∀ n, eLpNorm (f n) 2 (volume.restrict (Icc 0 1)) ≤ M)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p < 2) :
    UnifIntegrable (fun n x => f n x - g x) p
      (volume.restrict (Icc 0 1)) := by
  sorry

/-- Main theorem: L²-bounded a.e. convergence implies Lp convergence for p < 2. -/
theorem tendsto_Lp_of_ae_tendsto_of_L2_bounded
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n) (volume.restrict (Icc 0 1)))
    (hgm : AEStronglyMeasurable g (volume.restrict (Icc 0 1)))
    (hf : ∀ n, Memℒp (f n) 2 (volume.restrict (Icc 0 1)))
    (hbdd : ∃ M, ∀ n, eLpNorm (f n) 2 (volume.restrict (Icc 0 1)) ≤ M)
    (hae : ∀ᵐ x ∂(volume.restrict (Icc (0:ℝ) 1)),
      Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p < 2) :
    Tendsto (fun n => eLpNorm (fun x => f n x - g x) p
      (volume.restrict (Icc 0 1)))
      atTop (𝓝 0) := by
  sorry

/-- Counterexample: fails for p = 2. fₙ = √n · 1_{[0,1/n]}. -/
def counterex_p2 (n : ℕ) : ℝ → ℝ :=
  (Icc (0:ℝ) (1/(↑n+1))).indicator (fun _ => Real.sqrt (↑n+1))

/-- Each fₙ has L² norm 1. -/
lemma counterex_p2_norm (n : ℕ) :
    eLpNorm (counterex_p2 n) 2 (volume.restrict (Icc 0 1)) = 1 := by
  sorry

/-- fₙ → 0 a.e. -/
lemma counterex_p2_ae_tendsto :
    ∀ᵐ x ∂(volume.restrict (Icc (0:ℝ) 1)),
      Tendsto (fun n => counterex_p2 n x) atTop (𝓝 0) := by
  sorry

/-- But fₙ does not converge to 0 in L². -/
lemma counterex_p2_not_L2 :
    ¬Tendsto (fun n => eLpNorm (counterex_p2 n) 2
      (volume.restrict (Icc 0 1)))
      atTop (𝓝 0) := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `MeasureTheory.Memℒp f p μ` — f ∈ Lp(μ)
- `MeasureTheory.eLpNorm f p μ` — the Lp seminorm
- `MeasureTheory.UnifIntegrable` — uniform integrability (in `Mathlib.MeasureTheory.Function.UnifIntegrable`)
- `MeasureTheory.Measure.restrict` — restricted measure to [0,1]
- `AEStronglyMeasurable` — measurability condition
- `Filter.Tendsto`, `Filter.atTop` — convergence

**Key lemmas:**
- `MeasureTheory.UnifIntegrable.tendsto_Lp` / `MeasureTheory.tendsto_Lp_of_tendstoInMeasure_of_unifIntegrable` — Vitali's convergence theorem: uniform integrability + convergence in measure (or a.e. on finite measure) ⟹ Lp convergence. In `Mathlib.MeasureTheory.Function.UnifIntegrable`
- `MeasureTheory.tendstoInMeasure_of_tendsto_ae` — on finite measure spaces, a.e. convergence ⟹ convergence in measure (Egorov). Provides the convergence-in-measure input for Vitali
- `MeasureTheory.Memℒp.memℒp_of_exponent_le` — Lq ⊂ Lp embedding on finite measure spaces (q ≥ p)
- `MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ` — Hölder embedding: ||f||_p ≤ ||f||_q · μ(X)^{1/p-1/q}
- `MeasureTheory.Memℒp.of_tendsto_ae` / Fatou — the limit inherits Lp membership
- `lintegral_liminf_le` — Fatou's lemma for lintegrals
- `MeasureTheory.integral_indicator` — for the counterexample
- `eLpNorm_indicator_const` — Lp norm of c·1_E
- `Real.volume_Icc` — m([0, 1/n])
- `IsFiniteMeasure` — [0,1] has finite measure

**Tactic hints:**
- `exact MeasureTheory.tendsto_Lp_of_tendstoInMeasure_of_unifIntegrable ...` — if Vitali is packaged
- `apply MeasureTheory.tendstoInMeasure_of_tendsto_ae` — convert a.e. to in-measure
- `calc` — for the Hölder chain ∫_E |fₙ-f|^p ≤ (∫|fₙ-f|²)^{p/2} · m(E)^{(2-p)/2}
- `gcongr` — for monotonicity steps in the Hölder bound
- `positivity` — for (2-p)/2 > 0 and related
- `norm_num` — for the counterexample norm computation
- `simp [counterex_p2, Set.indicator]` — unfolding the counterexample
- `filter_upwards` — for the a.e. convergence of the counterexample
- `linarith` — combining p < 2 with exponent arithmetic