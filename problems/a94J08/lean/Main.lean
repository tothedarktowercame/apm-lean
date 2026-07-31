import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# APM a94J08: No entire function satisfies |f(z)| ≥ |z|^{3/2}

## Problem (from `a94J08.tex`)

Prove that no entire function `f` can satisfy `|f(z)| ≥ |z|^{3/2}` for all
complex numbers `z`.

## Proof strategy

Suppose `f` is entire with `|f(z)| ≥ |z|^{3/2}` for all `z`.

**Case A: `f(0) ≠ 0`.** Then `f` never vanishes (for `z ≠ 0`, `|f(z)| ≥ |z|^{3/2} > 0`).
So `g = 1/f` is entire. For `|z| ≥ 1`: `|g(z)| = 1/|f(z)| ≤ 1/|z|^{3/2} ≤ 1`.
For `|z| ≤ 1`: `g` is continuous on the compact set `closedBall 0 1`, hence bounded.
So `g` is bounded everywhere. By Liouville, `g` is constant, so `f` is constant.
But `|f(z)| ≥ |z|^{3/2}` is impossible for a constant and large `|z|`. Contradiction.

**Case B: `f(0) = 0`.** Then `f(z) = zⁿ h(z)` with `h` entire, `h(0) ≠ 0`, `n ≥ 1`.
The bound gives `|h(z)| ≥ |z|^{3/2 - n}` for `z ≠ 0`.
- If `n ≥ 2`: `|h(z)| ≥ |z|^{-1/2} → ∞` as `z → 0`, contradicting `h` continuous at `0`.
- If `n = 1`: `h` is entire, `h(0) ≠ 0`, `|h(z)| ≥ |z|^{1/2}`. Apply Case A to `h`.
-/

set_option linter.unusedVariables false in
noncomputable section

open Complex Bornology Set Metric

open scoped Real

namespace ApmCanaries.A94J08

/-- Helper: `a⁻¹ ≤ 1` when `1 ≤ a`. -/
lemma inv_le_one_of_le_one {a : ℝ} (ha : 1 ≤ a) : a⁻¹ ≤ 1 := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have : a⁻¹ = 1 / a := by rw [one_div]
  rw [this]; exact (div_le_one ha0).mpr ha

/-- Helper: `f(z) ≠ 0` for `z ≠ 0` from the lower bound. -/
lemma nonzero_of_lower_bound
    (f : ℂ → ℂ)
    (hbound : ∀ z, ‖z‖ ^ ((3:ℝ)/2) ≤ ‖f z‖)
    (z : ℂ) (hz : z ≠ 0) : f z ≠ 0 := by
  intro h
  have hb := hbound z
  rw [h] at hb; simp at hb
  linarith [Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) ((3:ℝ)/2)]

/-- Helper: `‖1/f(z)‖ ≤ 1` for `|z| ≥ 1`. -/
lemma norm_inv_le_one_of_lower_bound
    (f : ℂ → ℂ) (hf_ne : ∀ z, f z ≠ 0)
    (hbound : ∀ z, ‖z‖ ^ ((3:ℝ)/2) ≤ ‖f z‖)
    (z : ℂ) (hz : 1 ≤ ‖z‖) :
    ‖(f z)⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  exact inv_le_one_of_le_one
    ((Real.one_le_rpow hz (by norm_num)).trans (hbound z))

/-- The nonvanishing case of the main theorem.  The reciprocal is bounded on
the unit disk by compactness and outside it by the assumed lower bound, hence
is constant by Liouville's theorem. -/
lemma false_of_entire_nonvanishing_lower_bound
    (f : ℂ → ℂ) (hf_diff : Differentiable ℂ f) (hf_ne : ∀ z, f z ≠ 0)
    (hbound : ∀ z : ℂ, ‖z‖ ^ ((3 : ℝ) / 2) ≤ ‖f z‖) : False := by
  let g : ℂ → ℂ := fun z => (f z)⁻¹
  have hg_diff : Differentiable ℂ g := Differentiable.inv hf_diff hf_ne
  have hg_bdd : IsBounded (range g) := by
    have hcompact : IsCompact (g '' closedBall (0 : ℂ) 1) :=
      (isCompact_closedBall (0 : ℂ) 1).image hg_diff.continuous
    refine (hcompact.isBounded.union
      (isBounded_closedBall : IsBounded (closedBall (0 : ℂ) 1))).subset ?_
    rintro w ⟨z, rfl⟩
    by_cases hz : ‖z‖ ≤ 1
    · exact Or.inl ⟨z, by simpa using hz, rfl⟩
    · apply Or.inr
      rw [mem_closedBall_zero_iff]
      exact norm_inv_le_one_of_lower_bound f hf_ne hbound z (le_of_not_ge hz)
  obtain ⟨c, hc⟩ := hg_diff.exists_const_forall_eq_of_bounded hg_bdd
  have hf_const : ∀ z, f z = f 0 := by
    intro z
    exact inv_inj.mp ((hc z).trans (hc 0).symm)
  let R : ℝ := ‖f 0‖ + 1
  have hR : 1 ≤ R := by simp [R]
  have hRnorm : ‖(R : ℂ)‖ = R := by
    simp [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_trans zero_le_one hR)]
  have hb := hbound (R : ℂ)
  rw [hRnorm, hf_const] at hb
  have hpow : R ≤ R ^ ((3 : ℝ) / 2) :=
    Real.self_le_rpow_of_one_le hR (by norm_num)
  dsimp [R] at hb hpow
  linarith

/-- The quotient used to remove a possible zero of `f` at the origin. -/
noncomputable def quadraticQuotient (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else z ^ 2 / f z

/-- The fractional lower bound makes the quadratic quotient sublinear. -/
lemma norm_quadraticQuotient_le
    (f : ℂ → ℂ)
    (hbound : ∀ z : ℂ, ‖z‖ ^ ((3 : ℝ) / 2) ≤ ‖f z‖) (z : ℂ) :
    ‖quadraticQuotient f z‖ ≤ ‖z‖ ^ ((1 : ℝ) / 2) := by
  by_cases hz : z = 0
  · simp [quadraticQuotient, hz]
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [quadraticQuotient, if_neg hz, norm_div, norm_pow]
    calc
      ‖z‖ ^ 2 / ‖f z‖ ≤ ‖z‖ ^ 2 / (‖z‖ ^ ((3 : ℝ) / 2)) :=
        div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hn _)
          (hbound z)
      _ = ‖z‖ ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_sub hn]
        congr 1
        norm_num

/-- The quadratic quotient extends continuously across the origin. -/
lemma quadraticQuotient_continuousAt_zero
    (f : ℂ → ℂ)
    (hbound : ∀ z : ℂ, ‖z‖ ^ ((3 : ℝ) / 2) ≤ ‖f z‖) :
    ContinuousAt (quadraticQuotient f) 0 := by
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hpow : Filter.Tendsto (fun z : ℂ => ‖z‖ ^ ((1 : ℝ) / 2))
      (nhds 0) (nhds 0) := by
    simpa using (tendsto_norm_zero.rpow_const (Or.inr (by norm_num :
      (0 : ℝ) ≤ (1 : ℝ) / 2)))
  apply squeeze_zero (fun z => norm_nonneg _) (fun z => ?_) hpow
  simpa [quadraticQuotient] using norm_quadraticQuotient_le f hbound z

/-- The quadratic quotient is entire: its value at zero is the removable
extension supplied by the fractional lower bound. -/
lemma quadraticQuotient_differentiable
    (f : ℂ → ℂ) (hf_diff : Differentiable ℂ f)
    (hbound : ∀ z : ℂ, ‖z‖ ^ ((3 : ℝ) / 2) ≤ ‖f z‖) :
    Differentiable ℂ (quadraticQuotient f) := by
  have hdiff (z : ℂ) (hz : z ≠ 0) :
      DifferentiableAt ℂ (quadraticQuotient f) z := by
    apply ((differentiableAt_id.pow 2).div (hf_diff z)
      (nonzero_of_lower_bound f hbound z hz)).congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    simp [quadraticQuotient, hw]
  intro z
  by_cases hz : z = 0
  · subst z
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      _ (quadraticQuotient_continuousAt_zero f hbound) |>.differentiableAt
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ 0 := by simpa using hz
    exact hdiff z hz'
  · exact hdiff z hz

/-- An entire function with square-root growth is constant.  This is the
sublinear-growth form of Liouville's theorem, proved from Cauchy's estimate. -/
lemma eq_const_of_norm_le_rpow_half
    (q : ℂ → ℂ) (hq_diff : Differentiable ℂ q)
    (hq : ∀ z : ℂ, ‖q z‖ ≤ ‖z‖ ^ ((1 : ℝ) / 2)) :
    ∀ z, q z = q 0 := by
  have hlim (c : ℂ) :
      Filter.Tendsto (fun R : ℝ => (R + ‖c‖) ^ ((1 : ℝ) / 2) / R)
        Filter.atTop (nhds 0) := by
    have hrat : Filter.Tendsto
        (fun R : ℝ => (R + ‖c‖) / R ^ 2) Filter.atTop (nhds 0) := by
      have h₁ : Filter.Tendsto (fun R : ℝ => R⁻¹) Filter.atTop (nhds 0) :=
        tendsto_inv_atTop_zero
      have h₂ : Filter.Tendsto (fun R : ℝ => ‖c‖ / R ^ 2)
          Filter.atTop (nhds 0) := by
        have hsq : Filter.Tendsto (fun R : ℝ => R ^ 2) Filter.atTop Filter.atTop := by
          apply Filter.tendsto_atTop.2
          intro b
          filter_upwards [Filter.eventually_ge_atTop (max 1 b)] with R hR
          have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
          have hRb : b ≤ R := (le_max_right _ _).trans hR
          nlinarith [mul_nonneg (sub_nonneg.mpr hR1) (by linarith : 0 ≤ R)]
        exact hsq.const_div_atTop _
      have heq : (fun R : ℝ => R⁻¹ + ‖c‖ / R ^ 2) =ᶠ[Filter.atTop]
          (fun R : ℝ => (R + ‖c‖) / R ^ 2) := by
        filter_upwards [Filter.eventually_ne_atTop 0] with R hR
        field_simp [hR]
      have hadd : Filter.Tendsto (fun R : ℝ => R⁻¹ + ‖c‖ / R ^ 2)
          Filter.atTop (nhds 0) := by simpa using h₁.add h₂
      exact Filter.Tendsto.congr' heq hadd
    have hsqrt := hrat.rpow_const (Or.inr (by norm_num :
      (0 : ℝ) ≤ (1 : ℝ) / 2))
    simpa using Filter.Tendsto.congr' (by
      filter_upwards [Filter.eventually_ge_atTop (max 1 (-‖c‖ + 1))] with R hR
      have hR0 : 0 < R := lt_of_lt_of_le (by positivity) (le_max_left _ _ |>.trans hR)
      have hsum : 0 ≤ R + ‖c‖ := by positivity
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
        ← Real.sqrt_eq_rpow, Real.sqrt_div hsum, Real.sqrt_sq_eq_abs,
        abs_of_pos hR0]) hsqrt
  have hderiv : ∀ c, deriv q c = 0 := by
    intro c
    apply norm_le_zero_iff.mp
    apply ge_of_tendsto (hlim c)
    filter_upwards [Filter.eventually_gt_atTop 0] with R hR
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR
      hq_diff.diffContOnCl
    intro z hz
    refine (hq z).trans (Real.rpow_le_rpow (norm_nonneg z) ?_ (by norm_num))
    rw [mem_sphere_iff_norm] at hz
    calc
      ‖z‖ = ‖(z - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
      _ = R + ‖c‖ := by rw [hz]
  exact fun z => is_const_of_deriv_eq_zero hq_diff hderiv z 0

/-- **Main theorem.** No entire function satisfies `|f(z)| ≥ |z|^{3/2}`.

    The proof splits into cases on whether `f(0) = 0`.  In the nonzero case,
    compactness and Liouville apply to `1/f`.  In the zero case, the removable
    quotient `z²/f(z)` has square-root growth, and Cauchy's estimate forces it
    to be constant. -/
theorem no_entire_lower_bound_three_halves :
    ¬∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      ∀ z : ℂ, ‖z‖ ^ ((3:ℝ)/2) ≤ ‖f z‖ := by
  rintro ⟨f, hf_diff, hbound⟩
  -- Case split: f(0) = 0 or f(0) ≠ 0
  by_cases hf0 : f 0 = 0
  · -- Case B: f(0) = 0
    -- Rather than explicitly computing the order of the zero, remove it by
    -- multiplying the reciprocal by `z²`.  The resulting entire function has
    -- square-root growth, so Cauchy's estimate makes it constant.
    have hq_diff := quadraticQuotient_differentiable f hf_diff hbound
    have hq_const : ∀ z, quadraticQuotient f z = quadraticQuotient f 0 :=
      eq_const_of_norm_le_rpow_half (quadraticQuotient f) hq_diff
        (norm_quadraticQuotient_le f hbound)
    have hq1 : quadraticQuotient f 1 = 0 := by
      simpa [quadraticQuotient] using hq_const 1
    have hf1 : f 1 ≠ 0 :=
      nonzero_of_lower_bound f hbound 1 one_ne_zero
    have hinv1 : (f 1)⁻¹ ≠ 0 := inv_ne_zero hf1
    apply hinv1
    simpa [quadraticQuotient] using hq1
  · -- Case A: f(0) ≠ 0
    -- f never vanishes
    have hf_ne : ∀ z, f z ≠ 0 := by
      intro z
      by_cases hz : z = 0
      · rw [hz]; exact hf0
      · exact nonzero_of_lower_bound f hbound z hz
    -- 1/f is bounded: |1/f(z)| ≤ 1 for |z| ≥ 1, and continuous (hence bounded)
    -- on compact {|z| ≤ 1}
    -- For |z| ≥ 1: proven above
    -- For |z| ≤ 1: need compactness argument
    exact false_of_entire_nonvanishing_lower_bound f hf_diff hf_ne hbound

end ApmCanaries.A94J08
