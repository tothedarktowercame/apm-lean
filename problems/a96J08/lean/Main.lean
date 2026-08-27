/-
! # APM a96J08: Evaluate ∫_{-∞}^{∞} e^{ωx}/(1-e^x) dx for 0 < Re(ω) < 1

The integral equals **-π cot(πω)**.

## Proof strategy

Use a rectangular contour with corners at -R and R+2πi, exploiting the 2πi periodicity
of e^z. The bottom edge gives the integral I, the top edge gives -e^{2πiω}I (period shift),
and the vertical edges vanish as R → ∞ (since 0 < Re(ω) < 1). The pole at z = 0 on the
bottom edge contributes a half-residue via indentation, and the pole at z = 2πi on the
top edge contributes similarly. Solving: I(1 - e^{2πiω}) = -πi(1 + e^{2πiω}),
hence I = -π cot(πω).

## Mathlib infrastructure

- `integral_boundary_rect_eq_zero_of_differentiableOn`: Cauchy-Goursat for rectangles
- `circleIntegral.integral_sub_inv_of_mem_ball`: residue of 1/(z-a) = 2πi
- `Complex.exp_add`: e^{a+b} = e^a · e^b (period shift)
- `Complex.abs_exp`: |e^z| = e^{Re(z)} (edge estimates)

## Statement note

The integral is a principal value (pole at x = 0). The statement uses a symmetric
truncation parameter δ for the principal value and R for the tail.
-/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

open Complex MeasureTheory Set Filter Topology

open scoped Real

noncomputable section

/-- The integrand e^{ωx}/(1 - e^x). -/
def integrand (ω : ℂ) (x : ℝ) : ℂ := Complex.exp (ω * x) / (1 - Complex.exp x)

/-- Reflection in the singular point exchanges the parameters `ω` and `1 - ω`.
This is the elementary symmetry behind the oddness of the principal value under
`ω ↦ 1 - ω`; it also reduces any eventual analytic evaluation to half of the
critical strip. -/
lemma integrand_one_sub_neg (ω : ℂ) (x : ℝ) :
    integrand (1 - ω) (-x) = -integrand ω x := by
  unfold integrand
  push_cast
  rw [show (1 - ω) * (-(x : ℂ)) = ω * x - x by ring,
    Complex.exp_sub, Complex.exp_neg]
  field_simp [Complex.exp_ne_zero]
  rw [show (Complex.exp (x : ℂ) - 1) = -(1 - Complex.exp x) by ring,
    div_neg]

/-- On a positive compact interval the singular denominator does not vanish. -/
lemma integrand_intervalIntegrable_pos (ω : ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (integrand ω) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  unfold integrand
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro x hx
    rw [← ofReal_exp]
    exact sub_ne_zero.mpr (mod_cast ne_of_lt
      (Real.one_lt_exp_iff.mpr (lt_of_lt_of_le ha hx.1)))

/-- Fold the negative half of a symmetric truncation onto the positive axis.
This isolates a nonsingular, absolutely convergent paired integrand. -/
lemma truncation_eq_integral_pair (ω : ℂ) {δ : ℝ}
    (hδ : 0 < δ) (hδ_one : δ < 1) :
    (∫ x in -(δ⁻¹)..(-δ), integrand ω x) +
        (∫ x in δ..δ⁻¹, integrand ω x) =
      ∫ x in δ..δ⁻¹, (integrand ω x - integrand (1 - ω) x) := by
  have hδ_inv : δ < δ⁻¹ := hδ_one.trans ((one_lt_inv₀ hδ).2 hδ_one)
  have hf := integrand_intervalIntegrable_pos ω hδ hδ_inv.le
  have hfneg : IntervalIntegrable
      (fun x : ℝ ↦ integrand ω (-x)) volume δ δ⁻¹ := by
    apply ((integrand_intervalIntegrable_pos (1 - ω) hδ hδ_inv.le).neg).congr
    intro x hx
    simpa only [Pi.neg_apply, sub_sub_cancel] using
      (integrand_one_sub_neg (1 - ω) x).symm
  rw [← intervalIntegral.integral_comp_neg (fun x ↦ integrand ω x),
    ← intervalIntegral.integral_add hfneg hf]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [show integrand ω (-x) = -integrand (1 - ω) x by
    simpa only [sub_sub_cancel] using integrand_one_sub_neg (1 - ω) x]
  ring

/-- For positive `x`, rewrite the denominator as a convergent geometric
series.  This is the pointwise expansion needed for the cotangent-series
route; the strip hypotheses enter later, when integrating the terms. -/
lemma integrand_eq_neg_mul_tsum (ω : ℂ) {x : ℝ} (hx : 0 < x) :
    integrand ω x =
      -Complex.exp (-(1 - ω) * x) * ∑' n : ℕ, Complex.exp (-x) ^ n := by
  have hnorm : ‖Complex.exp (-(x : ℂ))‖ < 1 := by
    rw [Complex.norm_exp]
    simpa using (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx))
  rw [tsum_geometric_of_norm_lt_one hnorm]
  unfold integrand
  rw [show Complex.exp (x : ℂ) = (Complex.exp (-(x : ℂ)))⁻¹ by
    simpa using Complex.exp_neg (-(x : ℂ))]
  have hexp : Complex.exp (-(x : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  rw [show Complex.exp (ω * (x : ℂ)) =
      Complex.exp (-(1 - ω) * (x : ℂ)) * Complex.exp (x : ℂ) by
    rw [← Complex.exp_add]
    congr 1
    ring]
  field_simp
  rw [← Complex.exp_add]
  rw [show Complex.exp (-(x : ℂ)) - 1 =
    -(1 - Complex.exp (-(x : ℂ))) by ring]
  simp
  rw [show Complex.exp (-(x : ℂ)) - 1 =
    -(1 - Complex.exp (-(x : ℂ))) by ring, inv_neg]

/-- Geometric-series form of the nonsingular paired integrand.  Its two
families have decay rates `n + 1 - ω` and `n + ω`, respectively; integrating
them over `Ioi 0` produces the reciprocal series in `cot_series_rep`. -/
lemma integrand_pair_eq_tsum (ω : ℂ) {x : ℝ} (hx : 0 < x) :
    integrand ω x - integrand (1 - ω) x =
      -Complex.exp (-(1 - ω) * x) * ∑' n : ℕ, Complex.exp (-x) ^ n +
        Complex.exp (-ω * x) * ∑' n : ℕ, Complex.exp (-x) ^ n := by
  rw [integrand_eq_neg_mul_tsum ω hx, integrand_eq_neg_mul_tsum (1 - ω) hx]
  ring_nf

/-- A point in the open critical strip cannot be an integer. -/
lemma mem_integerComplement_of_re_mem_strip (ω : ℂ)
    (hre_pos : 0 < ω.re) (hre_lt : ω.re < 1) : ω ∈ integerComplement := by
  rw [mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  have hre := congrArg Complex.re hn
  norm_num at hre
  have hn_pos : 0 < n := by exact_mod_cast hre_pos.trans_eq hre.symm
  have hn_lt : n < 1 := by exact_mod_cast hre ▸ hre_lt
  omega

/-- The reciprocal sequence occurring after the exponential integrations,
indexed with its `1 / ω` head separated from the equal-offset pairs. -/
def reciprocalCotTerm (ω : ℂ) : ℕ → ℂ
  | 0 => 1 / ω
  | n + 1 => 1 / (ω - (n + 1)) + 1 / (ω + (n + 1))

/-- Absolute convergence of the head-plus-tail reciprocal sequence. -/
lemma summable_reciprocalCotTerm (ω : ℂ)
    (hre_pos : 0 < ω.re) (hre_lt : ω.re < 1) :
    Summable (reciprocalCotTerm ω) := by
  have hz := mem_integerComplement_of_re_mem_strip ω hre_pos hre_lt
  have htail : Summable (fun n : ℕ ↦ reciprocalCotTerm ω (n + 1)) := by
    simpa only [reciprocalCotTerm] using summable_cotTerm hz
  exact (summable_nat_add_iff 1).mp htail

/-- The integrated head-plus-tail sequence is exactly the Mittag--Leffler
series for `π cot (πω)`. -/
lemma cot_eq_tsum_reciprocalCotTerm (ω : ℂ)
    (hre_pos : 0 < ω.re) (hre_lt : ω.re < 1) :
    π * Complex.cot (π * ω) =
      ∑' n : ℕ, reciprocalCotTerm ω n := by
  have hz := mem_integerComplement_of_re_mem_strip ω hre_pos hre_lt
  have hg := summable_reciprocalCotTerm ω hre_pos hre_lt
  have hsplit := hg.sum_add_tsum_nat_add 1
  have hcot := cot_series_rep' hz
  rw [← hsplit]
  simp only [Finset.sum_range_one, reciprocalCotTerm]
  rw [← hcot]
  ring

/-- Each positive-rate exponential in the first geometric family is
integrable on the positive half-line and contributes its reciprocal rate. -/
lemma integral_Ioi_exp_neg_nat_add (ω : ℂ) (hre_pos : 0 < ω.re) (n : ℕ) :
    ∫ x : ℝ in Ioi 0, Complex.exp (-((n : ℂ) + ω) * x) =
      1 / ((n : ℂ) + ω) := by
  have ha : (-((n : ℂ) + ω)).re < 0 := by
    norm_num
    linarith [show 0 ≤ (n : ℝ) by positivity]
  rw [integral_exp_mul_complex_Ioi ha 0]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero, neg_div, one_div]
  rw [inv_neg]
  ring

/-- The reflected exponential family is likewise integrable in the critical
strip and contributes the reciprocal of `n + 1 - ω`. -/
lemma integral_Ioi_exp_neg_nat_succ_sub (ω : ℂ) (hre_lt : ω.re < 1) (n : ℕ) :
    ∫ x : ℝ in Ioi 0, Complex.exp (-((n + 1 : ℕ) - ω) * x) =
      1 / ((n + 1 : ℕ) - ω) := by
  have ha : (-((n + 1 : ℕ) - ω)).re < 0 := by
    norm_num
    linarith [show 0 ≤ (n : ℝ) by positivity]
  rw [integral_exp_mul_complex_Ioi ha 0]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero, neg_div, one_div]
  rw [inv_neg]
  ring

/-- The unmatched endpoint in the finite equal-offset reindexing vanishes. -/
lemma tendsto_inv_nat_succ_sub (ω : ℂ)
    (hre_lt : ω.re < 1) :
    Tendsto (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) - ω)) atTop (𝓝 0) := by
  have hsmall : Tendsto (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℂ)) atTop (𝓝 0) := by
    convert (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℂ)).comp
      (tendsto_add_atTop_nat 1) using 1
  have hden : Tendsto (fun n : ℕ ↦ 1 - ω * (1 / ((n + 1 : ℕ) : ℂ)))
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hsmall)
  have hquot := hsmall.div hden (by norm_num : (1 : ℂ) ≠ 0)
  have hquot' : Tendsto
      (fun n : ℕ ↦ (1 / ((n + 1 : ℕ) : ℂ)) /
        (1 - ω * (1 / ((n + 1 : ℕ) : ℂ)))) atTop (𝓝 0) := by
    simpa using hquot
  apply hquot'.congr'
  filter_upwards with n
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hω : ((n + 1 : ℕ) : ℂ) - ω ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    have hnlt : (n : ℝ) < 0 := by linarith
    exact (not_lt_of_ge (show (0 : ℝ) ≤ (n : ℝ) by positivity)) hnlt
  field_simp

/-- Pair the two integrated exponential families at their original geometric
index.  Finite sums differ from equal-offset cotangent partial sums by exactly
one endpoint. -/
lemma sum_reciprocal_diff_eq (ω : ℂ) (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1),
        (1 / ((n : ℂ) + ω) - 1 / ((n + 1 : ℕ) - ω)) =
      1 / ω + ∑ n ∈ Finset.range m, cotTerm ω n -
        1 / ((m + 1 : ℕ) - ω) := by
  induction m with
  | zero => simp [cotTerm]
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp only [cotTerm]
      push_cast
      rw [show ω - ((m : ℂ) + 1) = -(((m : ℂ) + 1) - ω) by ring]
      simp only [one_div, inv_neg]
      ring

/-- Consequently the original-index reciprocal partial sums converge to the
same cotangent value.  This theorem records the endpoint bookkeeping needed
after integrating finite geometric partial sums. -/
lemma tendsto_sum_reciprocal_diff (ω : ℂ)
    (hre_pos : 0 < ω.re) (hre_lt : ω.re < 1) :
    Tendsto (fun m : ℕ ↦ ∑ n ∈ Finset.range (m + 1),
      (1 / ((n : ℂ) + ω) - 1 / ((n + 1 : ℕ) - ω)))
      atTop (𝓝 (π * Complex.cot (π * ω))) := by
  have hz := mem_integerComplement_of_re_mem_strip ω hre_pos hre_lt
  have hcot := tendsto_logDeriv_euler_cot_sub hz
  have hend := tendsto_inv_nat_succ_sub ω hre_lt
  have hlim := ((tendsto_const_nhds (x := (1 / ω : ℂ))).add hcot).sub hend
  convert hlim using 1
  · funext m
    exact sum_reciprocal_diff_eq ω m
  · abel

/-- The paired geometric summand, kept in a form whose two finite families can
be integrated directly before reindexing their reciprocal values. -/
def pairedGeomTerm (ω : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (-ω * x) * Complex.exp (-x) ^ n -
    Complex.exp (-(1 - ω) * x) * Complex.exp (-x) ^ n

/-- Normalize a paired geometric term to the two exponential rates used by
the half-line integral formulas. -/
lemma pairedGeomTerm_eq_exp_sub (ω : ℂ) (n : ℕ) (x : ℝ) :
    pairedGeomTerm ω n x =
      Complex.exp (-((n : ℂ) + ω) * x) -
        Complex.exp (-((n + 1 : ℕ) - ω) * x) := by
  unfold pairedGeomTerm
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 2
  · ring
  · rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- Every paired geometric term is integrable on the positive half-line. -/
lemma integrableOn_pairedGeomTerm (ω : ℂ)
    (hre_pos : 0 < ω.re) (hre_lt : ω.re < 1) (n : ℕ) :
    IntegrableOn (pairedGeomTerm ω n) (Ioi 0) := by
  rw [show pairedGeomTerm ω n = fun x : ℝ ↦
      Complex.exp (-((n : ℂ) + ω) * x) -
        Complex.exp (-((n + 1 : ℕ) - ω) * x) by
    funext x
    exact pairedGeomTerm_eq_exp_sub ω n x]
  apply Integrable.sub
  · apply integrableOn_exp_mul_complex_Ioi
    norm_num
    linarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
  · apply integrableOn_exp_mul_complex_Ioi
    norm_num
    linarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]

/-- Integrating one paired term gives the corresponding original-index
reciprocal difference. -/
lemma integral_pairedGeomTerm (ω : ℂ)
    (hre_pos : 0 < ω.re) (hre_lt : ω.re < 1) (n : ℕ) :
    ∫ x : ℝ in Ioi 0, pairedGeomTerm ω n x =
      1 / ((n : ℂ) + ω) - 1 / ((n + 1 : ℕ) - ω) := by
  simp_rw [pairedGeomTerm_eq_exp_sub]
  rw [integral_sub]
  · rw [integral_Ioi_exp_neg_nat_add ω hre_pos n,
      integral_Ioi_exp_neg_nat_succ_sub ω hre_lt n]
  · apply integrableOn_exp_mul_complex_Ioi
    norm_num
    linarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
  · apply integrableOn_exp_mul_complex_Ioi
    norm_num
    linarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]

/-- Finite paired geometric partial sums integrate to the reciprocal partial
sums whose limit was identified above. -/
lemma integral_sum_pairedGeomTerm (ω : ℂ)
    (hre_pos : 0 < ω.re) (hre_lt : ω.re < 1) (m : ℕ) :
    ∫ x : ℝ in Ioi 0, ∑ n ∈ Finset.range (m + 1), pairedGeomTerm ω n x =
      ∑ n ∈ Finset.range (m + 1),
        (1 / ((n : ℂ) + ω) - 1 / ((n + 1 : ℕ) - ω)) := by
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro n hn
    exact integral_pairedGeomTerm ω hre_pos hre_lt n
  · intro n hn
    exact integrableOn_pairedGeomTerm ω hre_pos hre_lt n

/-- The integrals of the finite paired geometric partial sums converge to the
cotangent value. -/
lemma tendsto_integral_sum_pairedGeomTerm (ω : ℂ)
    (hre_pos : 0 < ω.re) (hre_lt : ω.re < 1) :
    Tendsto (fun m : ℕ ↦
      ∫ x : ℝ in Ioi 0, ∑ n ∈ Finset.range (m + 1), pairedGeomTerm ω n x)
      atTop (𝓝 (π * Complex.cot (π * ω))) := by
  apply (tendsto_sum_reciprocal_diff ω hre_pos hre_lt).congr'
  filter_upwards with m
  exact (integral_sum_pairedGeomTerm ω hre_pos hre_lt m).symm

/-- Numerator and denominator exhibiting the removable singularity of the
paired integrand at zero. -/
def pairNumerator (ω : ℂ) (z : ℂ) : ℂ :=
  Complex.exp (ω * z) - Complex.exp ((1 - ω) * z)

def pairDenominator (z : ℂ) : ℂ := 1 - Complex.exp z

lemma integrand_pair_eq_div (ω : ℂ) (x : ℝ) :
    integrand ω x - integrand (1 - ω) x =
      pairNumerator ω x / pairDenominator x := by
  unfold integrand pairNumerator pairDenominator
  ring

lemma hasDerivAt_pairNumerator (ω : ℂ) :
    HasDerivAt (pairNumerator ω) (2 * ω - 1) 0 := by
  unfold pairNumerator
  convert (((hasDerivAt_id (0 : ℂ)).const_mul ω).cexp.sub
    (((hasDerivAt_id (0 : ℂ)).const_mul (1 - ω)).cexp)) using 1
  all_goals norm_num
  all_goals ring

lemma hasDerivAt_pairDenominator :
    HasDerivAt pairDenominator (-1 : ℂ) 0 := by
  unfold pairDenominator
  convert (hasDerivAt_const (x := (0 : ℂ)) (1 : ℂ)).sub
    ((hasDerivAt_id (0 : ℂ)).cexp) using 1
  all_goals norm_num

/-- The paired quotient has the expected removable value at zero. -/
lemma tendsto_pair_div_zero (ω : ℂ) :
    Tendsto (fun z : ℂ ↦ pairNumerator ω z / pairDenominator z)
      (𝓝[≠] 0) (𝓝 (1 - 2 * ω)) := by
  have hn := (hasDerivAt_pairNumerator ω).tendsto_slope_zero
  have hd := hasDerivAt_pairDenominator.tendsto_slope_zero
  have hq := hn.div hd (by norm_num : (-1 : ℂ) ≠ 0)
  have hq' : Tendsto
      ((fun t : ℂ ↦ t⁻¹ • (pairNumerator ω (0 + t) - pairNumerator ω 0)) /
        fun t : ℂ ↦ t⁻¹ • (pairDenominator (0 + t) - pairDenominator 0))
      (𝓝[≠] 0) (𝓝 (1 - 2 * ω)) := by
    convert hq using 1
    all_goals ring_nf
  apply hq'.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hn0 : pairNumerator ω 0 = 0 := by simp [pairNumerator]
  have hd0 : pairDenominator 0 = 0 := by simp [pairDenominator]
  simp only [zero_add, hn0, hd0, sub_zero]
  change (z⁻¹ • pairNumerator ω z) / (z⁻¹ • pairDenominator z) =
    pairNumerator ω z / pairDenominator z
  simp only [smul_eq_mul]
  exact mul_div_mul_left _ _ (inv_ne_zero hz)

/-- Continuous complex extension of the paired quotient at its removable
singularity.  Other complex zeros of the denominator are irrelevant to the
real positive-axis application. -/
def pairExtension (ω : ℂ) : ℂ → ℂ :=
  Function.update (fun z ↦ pairNumerator ω z / pairDenominator z)
    0 (1 - 2 * ω)

lemma continuousAt_pairExtension_zero (ω : ℂ) :
    ContinuousAt (pairExtension ω) 0 := by
  exact continuousAt_update_same.mpr (tendsto_pair_div_zero ω)

lemma pairExtension_of_ne (ω : ℂ) {z : ℂ} (hz : z ≠ 0) :
    pairExtension ω z = pairNumerator ω z / pairDenominator z := by
  simp [pairExtension, hz]

/-- Along the punctured real axis the continuous extension agrees with the
paired integrand. -/
lemma pairExtension_ofReal_eq_integrand_pair (ω : ℂ) {x : ℝ} (hx : x ≠ 0) :
    pairExtension ω x = integrand ω x - integrand (1 - ω) x := by
  rw [pairExtension_of_ne ω (ofReal_ne_zero.mpr hx), integrand_pair_eq_div]

/-- The real-axis restriction of the removable extension. -/
def realPairExtension (ω : ℂ) (x : ℝ) : ℂ := pairExtension ω x

lemma continuous_realPairExtension (ω : ℂ) :
    Continuous (realPairExtension ω) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    change ContinuousAt (pairExtension ω ∘ ((↑) : ℝ → ℂ)) 0
    exact (continuousAt_pairExtension_zero ω).comp_of_eq
      Complex.continuous_ofReal.continuousAt (by norm_num)
  · apply ContinuousAt.comp _ Complex.continuous_ofReal.continuousAt
    rw [show pairExtension ω = Function.update
      (fun z ↦ pairNumerator ω z / pairDenominator z) 0 (1 - 2 * ω) from rfl,
      continuousAt_update_of_ne (ofReal_ne_zero.mpr hx)]
    apply ContinuousAt.div
    · unfold pairNumerator
      fun_prop
    · unfold pairDenominator
      fun_prop
    · unfold pairDenominator
      rw [← ofReal_exp]
      apply sub_ne_zero.mpr
      exact (ofReal_injective.ne (by simpa using hx)).symm

/-- In particular, the extended paired integrand is integrable on every
compact real interval containing the former singular point. -/
lemma intervalIntegrable_realPairExtension (ω : ℂ) (a b : ℝ) :
    IntervalIntegrable (realPairExtension ω) volume a b :=
  (continuous_realPairExtension ω).continuousOn.intervalIntegrable

/-- The original paired integrand is integrable immediately to the right of
zero, because it differs from the continuous extension only at the excluded
endpoint. -/
lemma integrableOn_integrand_pair_Ioc_zero_one (ω : ℂ) :
    IntegrableOn (fun x : ℝ ↦ integrand ω x - integrand (1 - ω) x)
      (Ioc 0 1) := by
  have hext : IntegrableOn (realPairExtension ω) (Ioc 0 1) :=
    ((continuous_realPairExtension ω).continuousOn.integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  apply hext.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  simpa [realPairExtension] using
    pairExtension_ofReal_eq_integrand_pair ω (ne_of_gt hx.1)

/-- Exact real norm of the geometric denominator on the positive axis. -/
lemma norm_one_sub_exp_neg {x : ℝ} (hx : 0 ≤ x) :
    ‖(1 : ℂ) - Complex.exp (-(x : ℂ))‖ = 1 - Real.exp (-x) := by
  rw [show -(x : ℂ) = ((-x : ℝ) : ℂ) by norm_num, ← ofReal_exp]
  norm_cast
  rw [Real.norm_eq_abs, abs_of_nonneg]
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx))

/-- Past `x = 1`, the geometric denominator is uniformly separated from
zero. -/
lemma one_sub_exp_neg_one_le_norm {x : ℝ} (hx : 1 ≤ x) :
    1 - Real.exp (-1) ≤ ‖(1 : ℂ) - Complex.exp (-(x : ℂ))‖ := by
  rw [norm_one_sub_exp_neg (by linarith)]
  gcongr

/-- Positive-axis form exposing the decaying numerator and uniformly
controlled geometric denominator. -/
lemma integrand_eq_neg_exp_div (ω : ℂ) {x : ℝ} (hx : 0 < x) :
    integrand ω x =
      -Complex.exp (-(1 - ω) * x) / (1 - Complex.exp (-(x : ℂ))) := by
  rw [integrand_eq_neg_mul_tsum ω hx]
  have hnorm : ‖Complex.exp (-(x : ℂ))‖ < 1 := by
    rw [Complex.norm_exp]
    simpa using (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx))
  rw [tsum_geometric_of_norm_lt_one hnorm]
  ring

/-- The integrand has an integrable exponential tail whenever `Re ω < 1`. -/
lemma integrableOn_integrand_Ioi_one (ω : ℂ) (hre_lt : ω.re < 1) :
    IntegrableOn (integrand ω) (Ioi 1) := by
  let c : ℝ := 1 - Real.exp (-1)
  have hc : 0 < c := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hrate : -(1 - ω.re) < 0 := by linarith
  have hmajor : IntegrableOn
      (fun x : ℝ ↦ c⁻¹ * Real.exp (-(1 - ω.re) * x)) (Ioi 1) := by
    exact (integrableOn_exp_mul_Ioi hrate 1).const_mul c⁻¹
  apply hmajor.mono'
  · apply ContinuousOn.aestronglyMeasurable
    · unfold integrand
      apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro x hx
        rw [← ofReal_exp]
        exact sub_ne_zero.mpr (mod_cast (ne_of_gt
          (Real.one_lt_exp_iff.mpr (lt_trans zero_lt_one hx))).symm)
    · exact measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [integrand_eq_neg_exp_div ω (lt_trans zero_lt_one hx)]
    simp only [norm_div, norm_neg, Complex.norm_exp]
    have hden := one_sub_exp_neg_one_le_norm hx.le
    have hinv : ‖(1 : ℂ) - Complex.exp (-(x : ℂ))‖⁻¹ ≤ c⁻¹ := by
      exact (inv_le_inv₀ (hc.trans_le hden) hc).mpr hden
    rw [div_eq_mul_inv]
    convert mul_le_mul_of_nonneg_left hinv (Real.exp_nonneg _) using 1
    all_goals dsimp [c]
    all_goals ring_nf

/-- Both tails of the paired integrand are integrable in the critical strip. -/
lemma integrableOn_integrand_pair_Ioi_one (ω : ℂ)
    (hre_pos : 0 < ω.re) (hre_lt : ω.re < 1) :
    IntegrableOn (fun x : ℝ ↦ integrand ω x - integrand (1 - ω) x)
      (Ioi 1) := by
  apply Integrable.sub (integrableOn_integrand_Ioi_one ω hre_lt)
  apply integrableOn_integrand_Ioi_one (1 - ω)
  norm_num
  linarith

/-- Combining the removable local singularity with the exponential tails
gives integrability of the paired integrand on the full positive half-line. -/
lemma integrableOn_integrand_pair_Ioi (ω : ℂ)
    (hre_pos : 0 < ω.re) (hre_lt : ω.re < 1) :
    IntegrableOn (fun x : ℝ ↦ integrand ω x - integrand (1 - ω) x)
      (Ioi 0) := by
  have hu := (integrableOn_integrand_pair_Ioc_zero_one ω).union
    (integrableOn_integrand_pair_Ioi_one ω hre_pos hre_lt)
  apply hu.mono_set
  intro x hx
  by_cases hx1 : x ≤ 1
  · exact Or.inl ⟨hx, hx1⟩
  · exact Or.inr (lt_of_not_ge hx1)

/-- A finite paired geometric sum is the paired integrand times the usual
finite-geometric remainder factor. -/
lemma sum_pairedGeomTerm_eq_mul (ω : ℂ) {x : ℝ} (hx : 0 < x) (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1), pairedGeomTerm ω n x =
      (integrand ω x - integrand (1 - ω) x) *
        (1 - Complex.exp (-x) ^ (m + 1)) := by
  let q : ℂ := Complex.exp (-x)
  let A : ℂ := Complex.exp (-ω * x)
  let B : ℂ := Complex.exp (-(1 - ω) * x)
  have hqnorm : ‖q‖ < 1 := by
    dsimp [q]
    rw [Complex.norm_exp]
    simpa using (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx))
  have hqne : q ≠ 1 := by
    intro h
    rw [h] at hqnorm
    norm_num at hqnorm
  have hq : 1 - q ≠ 0 := sub_ne_zero.mpr hqne.symm
  have hpair : integrand ω x - integrand (1 - ω) x =
      (A - B) * (1 - q)⁻¹ := by
    rw [integrand_pair_eq_tsum ω hx,
      tsum_geometric_of_norm_lt_one hqnorm]
    dsimp [A, B, q]
    ring
  rw [hpair]
  change ∑ n ∈ Finset.range (m + 1), (A * q ^ n - B * q ^ n) =
    (A - B) * (1 - q)⁻¹ * (1 - q ^ (m + 1))
  have hgeom : (∑ n ∈ Finset.range (m + 1), q ^ n) =
      (1 - q)⁻¹ * (1 - q ^ (m + 1)) := by
    apply (eq_inv_mul_iff_mul_eq₀ hq).2
    simpa [mul_comm] using geom_sum_mul_neg q (m + 1)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← sub_mul]
  rw [hgeom]
  ring

/-- The finite paired sums admit a majorant independent of the truncation
index; the factor two is the elementary geometric-remainder bound. -/
lemma norm_sum_pairedGeomTerm_le (ω : ℂ) {x : ℝ} (hx : 0 < x) (m : ℕ) :
    ‖∑ n ∈ Finset.range (m + 1), pairedGeomTerm ω n x‖ ≤
      2 * ‖integrand ω x - integrand (1 - ω) x‖ := by
  rw [sum_pairedGeomTerm_eq_mul ω hx m, norm_mul]
  have hq : ‖Complex.exp (-(x : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp]
    exact (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx.le))
  have hpow : ‖Complex.exp (-(x : ℂ)) ^ (m + 1)‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hq
  have hfactor : ‖1 - Complex.exp (-(x : ℂ)) ^ (m + 1)‖ ≤ 2 := by
    calc
      ‖1 - Complex.exp (-(x : ℂ)) ^ (m + 1)‖ ≤
          ‖(1 : ℂ)‖ + ‖Complex.exp (-(x : ℂ)) ^ (m + 1)‖ := norm_sub_le _ _
      _ = 1 + ‖Complex.exp (-(x : ℂ)) ^ (m + 1)‖ := by rw [norm_one]
      _ ≤ 1 + 1 := by linarith
      _ = 2 := by norm_num
  nlinarith [norm_nonneg (integrand ω x - integrand (1 - ω) x)]

/-- On the positive axis the paired integrand is the sum of the paired
geometric terms. -/
lemma hasSum_pairedGeomTerm (ω : ℂ) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ ↦ pairedGeomTerm ω n x)
      (integrand ω x - integrand (1 - ω) x) := by
  have hnorm : ‖Complex.exp (-(x : ℂ))‖ < 1 := by
    rw [Complex.norm_exp]
    simpa using (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx))
  have hgeom := hasSum_geometric_of_norm_lt_one hnorm
  have hp := (hgeom.mul_left (Complex.exp (-ω * x))).sub
    (hgeom.mul_left (Complex.exp (-(1 - ω) * x)))
  convert hp using 1
  · rw [integrand_pair_eq_tsum ω hx, hgeom.tsum_eq]
    ring

/-- Dominated convergence identifies the limit of the finite paired sums
with the integral of their pointwise geometric-series limit. -/
lemma tendsto_integral_sum_to_integrand_pair (ω : ℂ)
    (hre_pos : 0 < ω.re) (hre_lt : ω.re < 1) :
    Tendsto (fun m : ℕ ↦
      ∫ x : ℝ in Ioi 0, ∑ n ∈ Finset.range (m + 1), pairedGeomTerm ω n x)
      atTop
      (𝓝 (∫ x : ℝ in Ioi 0, integrand ω x - integrand (1 - ω) x)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun x : ℝ ↦ 2 * ‖integrand ω x - integrand (1 - ω) x‖)
  · intro m
    exact (integrable_finset_sum _ fun n hn ↦
      integrableOn_pairedGeomTerm ω hre_pos hre_lt n).aestronglyMeasurable
  · exact (integrableOn_integrand_pair_Ioi ω hre_pos hre_lt).norm.const_mul 2
  · intro m
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_sum_pairedGeomTerm_le ω hx m
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (hasSum_pairedGeomTerm ω hx).tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 1)

/-- The positive-half-line paired integral is the cotangent partial-fraction
sum. -/
lemma integral_integrand_pair_Ioi_eq_cot (ω : ℂ)
    (hre_pos : 0 < ω.re) (hre_lt : ω.re < 1) :
    ∫ x : ℝ in Ioi 0, integrand ω x - integrand (1 - ω) x =
      π * Complex.cot (π * ω) := by
  exact tendsto_nhds_unique
    (tendsto_integral_sum_to_integrand_pair ω hre_pos hre_lt)
    (tendsto_integral_sum_pairedGeomTerm ω hre_pos hre_lt)

/-- The lower endpoint contributes nothing as it approaches the removable
singularity from the right. -/
lemma tendsto_integral_zero_to_integrand_pair (ω : ℂ)
    (hre_pos : 0 < ω.re) (hre_lt : ω.re < 1) :
    Tendsto (fun δ : ℝ ↦
      ∫ x in 0..δ, integrand ω x - integrand (1 - ω) x)
      (𝓝[>] 0) (𝓝 0) := by
  let f : ℝ → ℂ := fun x ↦ integrand ω x - integrand (1 - ω) x
  have hf : IntegrableOn f (Ioi 0) :=
    integrableOn_integrand_pair_Ioi ω hre_pos hre_lt
  have htail : Tendsto (fun δ : ℝ ↦ ∫ x in Ioi δ, f x)
      (𝓝[>] 0) (𝓝 (∫ x in Ioi 0, f x)) :=
    hf.continuousWithinAt_Ici_primitive_Ioi.mono Ioi_subset_Ici_self
  have hconst : Tendsto (fun _ : ℝ ↦ ∫ x in Ioi 0, f x)
      (𝓝[>] 0) (𝓝 (∫ x in Ioi 0, f x)) := tendsto_const_nhds
  have hsub := hconst.sub htail
  simpa only [sub_self] using hsub.congr' (by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    simpa [f] using (intervalIntegral.integral_Ioi_sub_Ioi hf hδ.le))

/-- Exhausting both endpoints of the positive half-line recovers its set
integral. -/
lemma tendsto_interval_integrand_pair_Ioi (ω : ℂ)
    (hre_pos : 0 < ω.re) (hre_lt : ω.re < 1) :
    Tendsto (fun δ : ℝ ↦
      ∫ x in δ..δ⁻¹, integrand ω x - integrand (1 - ω) x)
      (𝓝[>] 0)
      (𝓝 (∫ x : ℝ in Ioi 0, integrand ω x - integrand (1 - ω) x)) := by
  let f : ℝ → ℂ := fun x ↦ integrand ω x - integrand (1 - ω) x
  have hf : IntegrableOn f (Ioi 0) :=
    integrableOn_integrand_pair_Ioi ω hre_pos hre_lt
  have hu : Tendsto (fun δ : ℝ ↦ ∫ x in 0..δ⁻¹, f x)
      (𝓝[>] 0) (𝓝 (∫ x in Ioi 0, f x)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hf tendsto_inv_nhdsGT_zero
  have hl := tendsto_integral_zero_to_integrand_pair ω hre_pos hre_lt
  have hd := hu.sub hl
  simpa only [sub_zero] using hd.congr' (by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδi : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ).le
    have hiδ : IntervalIntegrable f volume 0 δ :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hδ.le).2
        (hf.mono_set Ioc_subset_Ioi_self)
    have hiδi : IntervalIntegrable f volume 0 δ⁻¹ :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hδi).2
        (hf.mono_set Ioc_subset_Ioi_self)
    simpa [f] using
      (intervalIntegral.integral_interval_sub_left hiδi hiδ))

/-- Why this unblocks `apm_a96J08`: this is the missing analytic
principal-value evaluation, stated directly in the truncation and filter API
used by the frozen theorem. An indented-contour or beta/reflection argument
can prove it without any further algebraic interface lemma. -/
theorem apm_a96J08_bridge_1 (ω : ℂ)
    (hre_pos : 0 < ω.re) (hre_lt : ω.re < 1) :
    Tendsto (fun δ : ℝ =>
      (∫ x in -(δ⁻¹)..(-δ), integrand ω x) +
        (∫ x in δ..δ⁻¹, integrand ω x))
      (𝓝[>] 0)
      (𝓝 (π * Complex.cos (π * ω) / Complex.sin (π * ω))) := by
  have h := tendsto_interval_integrand_pair_Ioi ω hre_pos hre_lt
  rw [integral_integrand_pair_Ioi_eq_cot ω hre_pos hre_lt,
    Complex.cot] at h
  have heq : (fun δ : ℝ ↦
      ∫ x in δ..δ⁻¹, integrand ω x - integrand (1 - ω) x) =ᶠ[𝓝[>] 0]
      (fun δ : ℝ ↦
        (∫ x in -(δ⁻¹)..(-δ), integrand ω x) +
          (∫ x in δ..δ⁻¹, integrand ω x)) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)] with δ hδ hδ_one
    exact (truncation_eq_integral_pair ω hδ hδ_one).symm
  simpa [mul_div_assoc] using h.congr' heq

/-- **Main theorem**: ∫_{-∞}^{∞} e^{ωx}/(1-e^x) dx = +π cot(πω) for 0 < Re(ω) < 1.

    The integral is interpreted as a principal value at x = 0 (where 1-e^x has a simple zero).
    The answer is +π cos(πω)/sin(πω) = +π cot(πω).

    SIGN CORRECTED 2026-08-26 (frame f45 -> recast as f46). The registered target
    was -π cot(πω), transcribed faithfully from the informal solution's boxed
    answer. That boxed answer is wrong: the informal derivation itself ends at
    I(1 - e^(2πiω)) = -πi(1 + e^(2πiω)), and (1 + e^(2iθ))/(1 - e^(2iθ)) = i·cot θ,
    so I = -πi·(i cot πω) = +π cot(πω). The f45 Solver refuted the minus sign
    with two axiom-clean instances -- ω = 1/4 (truncations positive, target -π)
    and ω = 3/4 (truncations negative, target +π). ω = 1/2 cannot discriminate,
    since cot(π/2) = 0 under either sign. -/
theorem apm_a96J08 (ω : ℂ) (hre_pos : 0 < ω.re) (hre_lt : ω.re < 1) :
    Tendsto (fun δ : ℝ =>
      (∫ x in -(δ⁻¹)..(-δ), integrand ω x) + (∫ x in δ..δ⁻¹, integrand ω x))
      (𝓝[>] 0) (𝓝 (π * Complex.cos (π * ω) / Complex.sin (π * ω))) := by
  -- The proof uses a rectangular contour with corners at -R and R+2πi.
  -- Bottom edge: ∫_{-R}^{R} f(x) dx → I (principal value)
  -- Top edge: ∫_{R}^{-R} f(x+2πi) dx = -e^{2πiω} I (period shift, reversed direction)
  -- Vertical edges → 0 as R → ∞
  -- Pole at z=0: residue -1, half-residue contribution πi (indentation)
  -- Pole at z=2πi: residue -e^{2πiω}, half-residue contribution πi·e^{2πiω}
  --
  -- The Cauchy-Goursat theorem for rectangles (available in Mathlib as
  -- integral_boundary_rect_eq_zero_of_differentiableOn) applies to the
  -- region between the two horizontal lines, but the poles at z=0 and z=2πi
  -- require either indentation or the residue theorem for rectangles.
  --
  -- The residue theorem for rectangles (boundary integral = 2πi × sum of residues)
  -- is NOT directly available in Mathlib. The Cauchy-Goursat theorem only handles
  -- the zero-residue case (no poles inside). For a single simple pole, one can
  -- remove a small disk around the pole and apply Cauchy-Goursat to the punctured
  -- region, but this requires significant topological machinery.
  --
  -- Mid-solve lookup: psr_search "rectangular contour integral residue theorem
  -- boundary integral poles" returned no relevant patterns. memory_search with
  -- tags ["contour", "integral", "residue"] returned empty.
  --
  -- Closer hop 2 proved `integrand_one_sub_neg`, the exact reflection identity
  -- `f_{1-ω}(-x) = -f_ω(x)`.  Searches of the repository and Mathlib for a
  -- principal-value change-of-variables theorem, cotangent integral, beta
  -- integral, or rectangle residue theorem found no result that converts this
  -- symmetry into the required value.  The remaining bridge is still an
  -- analytic evaluation (via an indented contour, beta/reflection formula, or
  -- an equivalent principal-value theorem), rather than algebraic rewriting.
  exact apm_a96J08_bridge_1 ω hre_pos hre_lt

end

-- #print axioms apm_a96J08
