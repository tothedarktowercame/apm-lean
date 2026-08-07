import Mathlib

/-!
# APM m00A02: Poincaré asymptotic expansions

## Statement repairs

Part (c) prints the formal derivative as `∑ n aₙ / xⁿ`. The derivative of
`aₙ / xⁿ` is instead `-n aₙ / xⁿ⁺¹`. We use this corrected sign and
index shift in the formal derivative coefficients.

## Encoding questions

None. An asymptotic expansion is encoded by the remainder limit for every
finite partial sum; no convergence of the infinite formal series is assumed.
-/

open Filter Finset
open scoped Topology ContDiff

noncomputable section

/-- Poincaré asymptotic expansion in descending integral powers at `+∞`. -/
def apm_m00A02_hasExpansion (f : ℝ → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ N : ℕ,
    Tendsto
      (fun x : ℝ ↦
        x ^ N * (f x - ∑ n ∈ range (N + 1), a n / x ^ n))
      atTop (nhds 0)

/-- Coefficients of the termwise derivative of `∑ aₙ x⁻ⁿ`. -/
def apm_m00A02_derivativeCoefficients (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => -(n : ℝ) * a n

/-- A smooth, asymptotically null function whose derivative is not null. -/
def apm_m00A02_counterexample (x : ℝ) : ℝ :=
  Real.exp (-x) * Real.sin (Real.exp x)

private lemma apm_m00A02_counterexample_hasDerivAt (x : ℝ) :
    HasDerivAt apm_m00A02_counterexample
      (Real.cos (Real.exp x) - Real.exp (-x) * Real.sin (Real.exp x)) x := by
  unfold apm_m00A02_counterexample
  convert
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).mul
      ((Real.hasDerivAt_sin (Real.exp x)).comp x (Real.hasDerivAt_exp x)) using 1 <;>
    simp only [Function.comp_apply]
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero x]
  <;> ring

theorem apm_m00a02 :
    apm_m00A02_hasExpansion (fun x : ℝ ↦ Real.exp (-x)) 0 ∧
    ContDiff ℝ ∞ apm_m00A02_counterexample ∧
    apm_m00A02_hasExpansion apm_m00A02_counterexample 0 ∧
    ¬apm_m00A02_hasExpansion (deriv apm_m00A02_counterexample) 0 ∧
    ∀ (f : ℝ → ℝ) (a b : ℕ → ℝ),
      Differentiable ℝ f →
      apm_m00A02_hasExpansion f a →
      apm_m00A02_hasExpansion (deriv f) b →
      apm_m00A02_hasExpansion (deriv f)
        (apm_m00A02_derivativeCoefficients a) := by
  have hexp : apm_m00A02_hasExpansion (fun x : ℝ ↦ Real.exp (-x)) 0 := by
    intro N
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N
  have hsmooth : ContDiff ℝ ∞ apm_m00A02_counterexample := by
    unfold apm_m00A02_counterexample
    fun_prop
  have hcounter : apm_m00A02_hasExpansion apm_m00A02_counterexample 0 := by
    intro N
    simp only [Pi.zero_apply, zero_div, sum_const_zero, sub_zero]
    apply squeeze_zero_norm
    · intro x
      unfold apm_m00A02_counterexample
      simp only [Real.norm_eq_abs, abs_mul]
      calc
        |x ^ N| * (|Real.exp (-x)| * |Real.sin (Real.exp x)|) ≤
            |x ^ N| * (|Real.exp (-x)| * 1) := by
              gcongr
              exact Real.abs_sin_le_one _
        _ = |x ^ N * Real.exp (-x)| := by rw [abs_mul, mul_one]
    · simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N).abs
  refine ⟨hexp, hsmooth, hcounter, ?_, ?_⟩
  · intro hderiv
    have hzero : Tendsto (deriv apm_m00A02_counterexample) atTop (nhds 0) := by
      simpa [apm_m00A02_hasExpansion] using hderiv 0
    let u : ℕ → ℝ := fun k => ((k + 1 : ℕ) : ℝ) * (2 * Real.pi)
    have hu : Tendsto u atTop atTop := by
      apply Tendsto.atTop_mul_const (mul_pos zero_lt_two Real.pi_pos)
      have hcast :=
        (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
      convert hcast using 1
    have hlog : Tendsto (fun k => Real.log (u k)) atTop atTop :=
      Real.tendsto_log_atTop.comp hu
    have hone : Tendsto
        (fun k => deriv apm_m00A02_counterexample (Real.log (u k)))
        atTop (nhds 1) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [] with k
      rw [(apm_m00A02_counterexample_hasDerivAt _).deriv]
      have huk : 0 < u k := mul_pos (by positivity) (mul_pos zero_lt_two Real.pi_pos)
      rw [Real.exp_log huk]
      have hcos : Real.cos (u k) = 1 := by
        simpa [u] using Real.cos_nat_mul_two_pi (k + 1)
      have hsin : Real.sin (u k) = 0 := by
        convert Real.sin_nat_mul_pi (2 * (k + 1)) using 1 <;> push_cast <;> simp [u] <;> ring
      rw [hcos, hsin]
      ring
    have hzero' := hzero.comp hlog
    have : (0 : ℝ) = 1 := tendsto_nhds_unique hzero' hone
    norm_num at this

  · /-
    Boundary for coefficient rigidity: the final implication requires a formal
    theorem that two integral-power Poincaré expansions have identical
    coefficients, plus integration of a derivative expansion from infinity.
    Searches of Mathlib and solved siblings found no reusable API for asymptotic
    expansion uniqueness or termwise integration in this custom encoding. A
    direct proof must first derive `b 0 = b 1 = 0` from convergence of `f`, then
    formalize improper FTC estimates order by order and compare coefficients.
    Closer hop 2 completed the independent counterexample-negation conjunct via
    the logarithmic sequence above. Further searches in the asymptotics and
    improper-integral APIs still found no theorem connecting this custom
    all-orders remainder predicate to the required integrated expansion.
    -/
    sorry
