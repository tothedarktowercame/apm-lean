

# APM a93A02: $L^{2}$-bounded a.e. convergent sequence converges in $L^p$ for $p < 2$

## 1. Informal proof

**Why it's hard.** A.e. convergence alone doesn't imply $L^p$ convergence (typewriter sequence). $L^{2}$ boundedness alone doesn't either. Together they give $L^p$ convergence for $p < 2$ but *not* for $p = 2$ — so the strict inequality $p < 2$ is essential and must be used somewhere in the proof.

**The key insight.** Use Vitali's convergence theorem: on a finite measure space, a.e. convergence + uniform integrability $\Longrightarrow$ $L^{1}$ convergence. The $L^{2}$ bound provides uniform integrability of $|f_{n} - f|^p$ via Hölder (since $p < 2$, the $L^p$ integrability is "buffered" by the $L^{2}$ margin). Alternatively, use Egorov + Hölder directly.

**Proof.**

*Step 0: $f \in L^{2}$ (hence $L^p$).* By Fatou's lemma, $\int|f|^{2} \leq \liminf \int|f_{n}|^{2} \leq (\sup \|f_{n}\|_{2})^{2} < \infty$. So $f \in L^{2}([0,1])$. Since $[0,1]$ has finite measure and $p < 2$, $L^{2} \subset L^p$, so $f \in L^p$.

*Step 1: Uniform integrability of $|f_{n} - f|^p$.* Set $M = \sup \|f_{n}\|_{2}$. For any measurable $E \subseteq [0,1]$, by Hölder with exponents $2/p$ and $2/(2-p)$ (conjugate since $p/2 + (2-p)/2 = 1$):

$\int_E |f_{n} - f|^p \leq (\int_E |f_{n}-f|^{2})^{p/2} \cdot m(E)^{(2-p)/2} \leq (\int|f_{n}-f|^{2})^{p/2} \cdot m(E)^{(2-p)/2}$.

Now $\int|f_{n}-f|^{2} \leq 2\int|f_{n}|^{2} + 2\int|f|^{2} \leq 2M^{2} + 2M^{2} = 4M^{2}$ (by $(a+b)^{2} \leq 2a^{2} + 2b^{2}$). So:

$\int_E |f_{n} - f|^p \leq (4M^{2})^{p/2} \cdot m(E)^{(2-p)/2} = C \cdot m(E)^{(2-p)/2}$.

Since $(2-p)/2 > 0$, this $\to 0$ as $m(E) \to 0$ uniformly in $n$. This is uniform integrability of $|f_{n} - f|^p$.

*Step 2: A.e. convergence of $|f_{n} - f|^p$.* Since $f_{n} \to f$ a.e., $|f_{n} - f|^p \to 0$ a.e.

*Step 3: Apply Vitali.* On $[0,1]$ (finite measure), $|f_{n} - f|^p \to 0$ a.e. and $\{|f_{n} - f|^p\}$ is uniformly integrable. By the Vitali convergence theorem:

$\int|f_{n} - f|^p \to 0$, i.e., $\|f_{n} - f\|_p \to 0$. ✓

*Counterexample for $p = 2$:* Let $f_{n} = \sqrt{n} \cdot 1_{[0,1/n]}$. Then $\|f_{n}\|_{2} = 1$ for all $n$, and $f_{n} \to 0$ a.e. (since $f_{n}(x) = 0$ for $x > 1/n$). But $\|f_{n} - 0\|_{2} = 1 \not\to 0$. So $L^{2}$ convergence fails despite a.e. convergence and bounded $L^{2}$ norms. ✓ ∎

**What connects.** This is a special case of the general interpolation principle: on a finite measure space, $L^{2}$-bounded sequences that converge a.e. converge in $L^p$ for all $p < 2$. The mechanism is that $L^{2}$ boundedness provides "room" for uniform integrability at any lower exponent, and Vitali's theorem converts a.e. convergence + uniform integrability into norm convergence. The counterexample for $p = 2$ shows this room vanishes at the critical exponent: concentration on shrinking sets ($f_{n} = \sqrt{n} \cdot 1_{[0,1/n]}$) preserves the $L^{2}$ norm while converging to 0 a.e. The result generalises: if $\|f_{n}\|_q \leq M$ and $f_{n} \to f$ a.e. on a finite measure space, then $f_{n} \to f$ in $L^p$ for all $p < q$. The Dunford-Pettis theorem provides the abstract framework: $L^q$-bounded families on finite measure spaces are uniformly integrable in $L^p$ for $p < q$.

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
- `MeasureTheory.Memℒp f p μ` — $f \in L^p(\mu)$
- `MeasureTheory.eLpNorm f p μ` — the $L^p$ seminorm
- `MeasureTheory.UnifIntegrable` — uniform integrability (in `Mathlib.MeasureTheory.Function.UnifIntegrable`)
- `MeasureTheory.Measure.restrict` — restricted measure to $[0,1]$
- `AEStronglyMeasurable` — measurability condition
- `Filter.Tendsto`, `Filter.atTop` — convergence

**Key lemmas:**
- `MeasureTheory.UnifIntegrable.tendsto_Lp` / `MeasureTheory.tendsto_Lp_of_tendstoInMeasure_of_unifIntegrable` — Vitali's convergence theorem: uniform integrability + convergence in measure (or a.e. on finite measure) $\Longrightarrow$ $L^p$ convergence. In `Mathlib.MeasureTheory.Function.UnifIntegrable`
- `MeasureTheory.tendstoInMeasure_of_tendsto_ae` — on finite measure spaces, a.e. convergence $\Longrightarrow$ convergence in measure (Egorov). Provides the convergence-in-measure input for Vitali
- `MeasureTheory.Memℒp.memℒp_of_exponent_le` — $L^q \subset L^p$ embedding on finite measure spaces ($q \geq p$)
- `MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ` — Hölder embedding: $\|f\|_p \leq \|f\|_q \cdot \mu(X)^{1/p-1/q}$
- `MeasureTheory.Memℒp.of_tendsto_ae` / Fatou — the limit inherits $L^p$ membership
- `lintegral_liminf_le` — Fatou's lemma for lintegrals
- `MeasureTheory.integral_indicator` — for the counterexample
- `eLpNorm_indicator_const` — $L^p$ norm of $c \cdot 1_E$
- `Real.volume_Icc` — $m([0, 1/n])$
- `IsFiniteMeasure` — $[0,1]$ has finite measure

**Tactic hints:**
- `exact MeasureTheory.tendsto_Lp_of_tendstoInMeasure_of_unifIntegrable ...` — if Vitali is packaged
- `apply MeasureTheory.tendstoInMeasure_of_tendsto_ae` — convert a.e. to in-measure
- `calc` — for the Hölder chain $\int_E |f_{n}-f|^p \leq (\int|f_{n}-f|^{2})^{p/2} \cdot m(E)^{(2-p)/2}$
- `gcongr` — for monotonicity steps in the Hölder bound
- `positivity` — for $(2-p)/2 > 0$ and related
- `norm_num` — for the counterexample norm computation
- `simp [counterex_p2, Set.indicator]` — unfolding the counterexample
- `filter_upwards` — for the a.e. convergence of the counterexample
- `linarith` — combining $p < 2$ with exponent arithmetic
