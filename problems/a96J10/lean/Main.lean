import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.Bernoulli

open Complex Set

noncomputable section

/-- The function f(z) = z/(e^{2πz} - 1) + z/2 extended by f(0) = 1/(2π) + 0
    is analytic on the open unit disk. -/
def apm_a96J10_f (z : ℂ) : ℂ :=
  if z = 0 then 1 / (2 * Real.pi) else z / (Complex.exp (2 * Real.pi * z) - 1) + z / 2

lemma exp_two_pi_mul_sub_ne_zero_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    Complex.exp (2 * (Real.pi : ℂ) * z) - 1 ≠ 0 := by
  intro h
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * z) = 1 := sub_eq_zero.mp h
  rcases Complex.exp_eq_one_iff.mp hexp with ⟨n, hn⟩
  have hRe : z.re = 0 := by
    have hre := congrArg Complex.re hn
    simp [Complex.mul_re, Complex.mul_im] at hre
    nlinarith [Real.pi_pos]
  have hIm : z.im = n := by
    have him := congrArg Complex.im hn
    simp [Complex.mul_re, Complex.mul_im, hRe] at him
    nlinarith [Real.pi_pos]
  have hzI : z = n * Complex.I := by
    apply Complex.ext <;> simp [hRe, hIm]
  by_cases hn0 : n = 0
  · exact hz0 (by simp [hzI, hn0])
  · have hnorm_ge : (1 : ℝ) ≤ ‖z‖ := by
      rw [hzI, norm_mul, norm_I, Complex.norm_intCast]
      simpa using (show (1 : ℝ) ≤ |(n : ℝ)| from by exact_mod_cast Int.one_le_abs hn0)
    linarith

def apm_a96J10_q : ℂ → ℂ := dslope Complex.exp 0

lemma apm_a96J10_q_analytic : AnalyticOn ℂ apm_a96J10_q univ := by
  refine DifferentiableOn.analyticOn ?_ isOpen_univ
  refine (Complex.differentiableOn_dslope (s := (Set.univ : Set ℂ)) (c := 0) ?_).2 ?_
  · simp
  · intro z hz
    exact (differentiableAt_exp : DifferentiableAt ℂ Complex.exp z).differentiableWithinAt

lemma apm_a96J10_q_of_ne (z : ℂ) (hz0 : z ≠ 0) :
    apm_a96J10_q z = (Complex.exp z - 1) / z := by
  rw [apm_a96J10_q, dslope_of_ne _ hz0]
  simp [slope, div_eq_mul_inv, mul_comm]

lemma apm_a96J10_q_nonzero_on_ball {z : ℂ} (hz : ‖z‖ < 1) :
    apm_a96J10_q ((2 * Real.pi : ℂ) * z) ≠ 0 := by
  by_cases hz0 : z = 0
  · simp [apm_a96J10_q, hz0, dslope_same]
  · have harg0 : (2 * (Real.pi : ℂ) * z) ≠ 0 := by
      simpa [hz0, Real.pi_ne_zero]
    rw [apm_a96J10_q_of_ne _ harg0]
    apply div_ne_zero
    · exact exp_two_pi_mul_sub_ne_zero_of_norm_lt_one hz hz0
    · exact harg0

theorem apm_a96J10_f_analytic :
    AnalyticOn ℂ apm_a96J10_f (Metric.ball (0:ℂ) 1) := by
  have hEq :
      apm_a96J10_f =
        (fun w : ℂ => (2 * Real.pi : ℂ)⁻¹ * (apm_a96J10_q ((2 * Real.pi : ℂ) * w))⁻¹ + w / 2) := by
    funext w
    by_cases hw0 : w = 0
    · simp [apm_a96J10_f, hw0, apm_a96J10_q, dslope_same]
    · have harg0 : (2 * (Real.pi : ℂ) * w) ≠ 0 := by
        simpa [hw0, Real.pi_ne_zero]
      rw [apm_a96J10_f, if_neg hw0, apm_a96J10_q_of_ne _ harg0]
      field_simp [harg0]
  rw [hEq]
  intro z hz
  have hnorm : ‖z‖ < 1 := by simpa using hz
  have hqAt : AnalyticAt ℂ apm_a96J10_q ((2 * Real.pi : ℂ) * z) := by
    simpa [analyticWithinAt_univ] using apm_a96J10_q_analytic ((2 * Real.pi : ℂ) * z) (by simp)
  have hlin : AnalyticAt ℂ (fun w : ℂ => (2 * Real.pi : ℂ) * w) z := by
    simpa using
      (analyticAt_const.mul analyticAt_id : AnalyticAt ℂ (fun w : ℂ => (2 * Real.pi : ℂ) * w) z)
  have hcomp : AnalyticAt ℂ (fun w : ℂ => apm_a96J10_q ((2 * Real.pi : ℂ) * w)) z :=
    hqAt.comp hlin
  have hcomp_nz : apm_a96J10_q ((2 * Real.pi : ℂ) * z) ≠ 0 := apm_a96J10_q_nonzero_on_ball hnorm
  have hmain :
      AnalyticAt ℂ (fun w : ℂ => (2 * Real.pi : ℂ)⁻¹ * (apm_a96J10_q ((2 * Real.pi : ℂ) * w))⁻¹ + w / 2) z := by
    refine (analyticAt_const.mul ?_).add ?_
    · exact hcomp.inv hcomp_nz
    · simpa [div_eq_mul_inv, mul_comm] using
        ((analyticAt_id).mul analyticAt_const : AnalyticAt ℂ (fun w : ℂ => w * ((2 : ℂ)⁻¹)) z)
  exact hmain.analyticWithinAt

/-- The Bernoulli-type identity: f is even on Δ. -/
theorem apm_a96J10_f_even
    (z : ℂ) (hz : ‖z‖ < 1) :
    apm_a96J10_f (-z) = apm_a96J10_f z := by
  by_cases hz0 : z = 0
  · simp [apm_a96J10_f, hz0]
  · have h1 : Complex.exp (2 * (Real.pi : ℂ) * z) - 1 ≠ 0 :=
      exp_two_pi_mul_sub_ne_zero_of_norm_lt_one hz hz0
    let E : ℂ := Complex.exp (2 * (Real.pi : ℂ) * z)
    have hE0 : E ≠ 0 := by
      simpa [E] using Complex.exp_ne_zero (2 * (Real.pi : ℂ) * z)
    have hE1 : E - 1 ≠ 0 := by
      simpa [E, sub_eq_add_neg] using h1
    have hnegarg : 2 * (Real.pi : ℂ) * (-z) = -(2 * (Real.pi : ℂ) * z) := by
      ring
    have hrewrite :
        (-z) / (Complex.exp (2 * (Real.pi : ℂ) * (-z)) - 1) = z * E / (E - 1) := by
      rw [hnegarg, Complex.exp_neg, div_eq_mul_inv]
      change -z * (E⁻¹ - 1)⁻¹ = z * E / (E - 1)
      have h1' : 1 - E ≠ 0 := sub_ne_zero.mpr <| by simpa using (sub_ne_zero.mp hE1).symm
      field_simp [hE0, h1', hE1]
      ring
    have hsplit : E / (E - 1) = 1 + 1 / (E - 1) := by
      field_simp [hE1]
      ring
    calc
      apm_a96J10_f (-z)
          = (-z) / (Complex.exp (2 * (Real.pi : ℂ) * (-z)) - 1) + (-z) / 2 := by
              simp [apm_a96J10_f, hz0, neg_eq_zero]
      _ = z * E / (E - 1) - z / 2 := by
              rw [hrewrite]
              ring
      _ = z * (E / (E - 1)) - z / 2 := by ring
      _ = z * (1 + 1 / (E - 1)) - z / 2 := by rw [hsplit]
      _ = z / (E - 1) + z / 2 := by ring
      _ = apm_a96J10_f z := by
              simp [apm_a96J10_f, hz0, E]

open FormalMultilinearSeries

private def evenFactorRoot (w : ℂ) : ℂ :=
  Classical.choose (Complex.isSquare w)

private lemma evenFactorRoot_sq (w : ℂ) : evenFactorRoot w ^ 2 = w := by
  simpa [pow_two, evenFactorRoot] using
    (Classical.choose_spec (Complex.isSquare w)).symm

private lemma evenFactorRoot_tendsto :
    Filter.Tendsto evenFactorRoot (nhds 0) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.eventually_nhds_iff.mpr
    ⟨ε ^ 2, sq_pos_of_pos hε, fun y hy => hy⟩] with w hw
  simp only [dist_zero_right] at hw ⊢
  have hs := congrArg norm (evenFactorRoot_sq w)
  rw [norm_pow] at hs
  nlinarith [sq_nonneg ‖evenFactorRoot w‖]

private lemma evenCoefficients_radius_pos
    (p : FormalMultilinearSeries ℂ ℂ ℂ) (hp : 0 < p.radius) :
    0 < (FormalMultilinearSeries.ofScalars ℂ
      (fun n => p.coeff (2 * n))).radius := by
  let q := FormalMultilinearSeries.ofScalars ℂ (fun n => p.coeff (2 * n))
  obtain ⟨C, r, _hC, hr, hbound⟩ := p.le_mul_pow_of_radius_pos hp
  let s : NNReal := ⟨(r ^ 2)⁻¹, by positivity⟩
  have hs : 0 < s := by
    exact_mod_cast (inv_pos.mpr (sq_pos_of_pos hr))
  have hsq : (s : ENNReal) ≤ q.radius := by
    apply q.le_radius_of_bound C
    intro n
    rw [show ‖q n‖ = ‖p (2 * n)‖ by
      simp [q, FormalMultilinearSeries.norm_apply_eq_norm_coef]]
    calc
      ‖p (2 * n)‖ * (s : ℝ) ^ n
          ≤ (C * r ^ (2 * n)) * (s : ℝ) ^ n :=
            mul_le_mul_of_nonneg_right (hbound (2 * n)) (by positivity)
      _ = C := by
        simp only [s, NNReal.coe_mk]
        rw [show r ^ (2 * n) = (r ^ 2) ^ n by rw [← pow_mul]]
        rw [show ((r ^ 2)⁻¹) ^ n = ((r ^ 2) ^ n)⁻¹ by rw [inv_pow]]
        field_simp
  exact lt_of_lt_of_le (by exact_mod_cast hs) hsq

private lemma evenCoefficients_sum
    (h : ℂ → ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (hp : HasFPowerSeriesAt h p 0)
    (hodd : ∀ n : ℕ, Odd n → p.coeff n = 0) :
    ∀ᶠ w in nhds 0,
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => p.coeff (2 * n))).sum w = h (evenFactorRoot w) := by
  let q := FormalMultilinearSeries.ofScalars ℂ (fun n => p.coeff (2 * n))
  have hqrad : 0 < q.radius := evenCoefficients_radius_pos p hp.radius_pos
  have hq : HasFPowerSeriesAt q.sum q 0 :=
    ⟨q.radius, q.hasFPowerSeriesOnBall hqrad⟩
  filter_upwards [hq.eventually_hasSum,
    evenFactorRoot_tendsto hp.eventually_hasSum] with w hqw hpw
  simp only [zero_add] at hqw hpw
  let a : ℕ → ℂ := fun n => p n (fun _ => evenFactorRoot w)
  have ha : Summable a := hpw.summable
  have hi_even : Function.Injective (fun k : ℕ => 2 * k) := by
    intro i j hij
    exact Nat.mul_left_cancel (by decide) hij
  have hi_odd : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro i j hij
    exact Nat.mul_left_cancel (by decide) (Nat.add_right_cancel hij)
  have hae : Summable (fun k => a (2 * k)) := ha.comp_injective hi_even
  have hao : Summable (fun k => a (2 * k + 1)) := ha.comp_injective hi_odd
  have heven_term (n : ℕ) : a (2 * n) = q n (fun _ => w) := by
    rw [show a (2 * n) = evenFactorRoot w ^ (2 * n) • p.coeff (2 * n) by
      exact apply_eq_pow_smul_coeff]
    have hpow : evenFactorRoot w ^ (2 * n) = w ^ n := by
      calc
        evenFactorRoot w ^ (2 * n) = (evenFactorRoot w ^ 2) ^ n := pow_mul _ 2 n
        _ = w ^ n := by rw [evenFactorRoot_sq]
    simp only [q, FormalMultilinearSeries.ofScalars,
      ContinuousMultilinearMap.smul_apply,
      ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_const,
      List.prod_replicate, smul_eq_mul]
    rw [hpow]
    ring
  have hodd_term (n : ℕ) : a (2 * n + 1) = 0 := by
    rw [show a (2 * n + 1) =
      evenFactorRoot w ^ (2 * n + 1) • p.coeff (2 * n + 1) by
        exact apply_eq_pow_smul_coeff]
    rw [hodd (2 * n + 1) ⟨n, by omega⟩, smul_zero]
  have hsplit := tsum_even_add_odd hae hao
  rw [show (∑' k, a (2 * k)) = q.sum w by
        rw [← hqw.tsum_eq]
        apply tsum_congr
        exact heven_term,
      show (∑' k, a (2 * k + 1)) = 0 by
        simp_rw [hodd_term]
        exact tsum_zero,
      add_zero,
      hpw.tsum_eq] at hsplit
  simpa [q] using hsplit

/-- An analytic even function on a disk factors through z². -/
theorem apm_a96J10_even_factors
    (h : ℂ → ℂ) (hh : AnalyticOn ℂ h (Metric.ball (0:ℂ) 1))
    (heven : ∀ z, ‖z‖ < 1 → h (-z) = h z) :
    ∃ g : ℂ → ℂ, AnalyticOn ℂ g (Metric.ball (0:ℂ) 1) ∧
      ∀ z, ‖z‖ < 1 → g (z ^ 2) = h z := by
  -- h is analytic at 0, extract the power series p with radius r.
  have hAn : AnalyticAt ℂ h 0 := hh.analyticAt (Metric.ball_mem_nhds 0 zero_lt_one)
  obtain ⟨p, hp⟩ := hAn
  -- Step 1: odd Taylor coefficients of p vanish.
  have hodd : ∀ n : ℕ, Odd n → p.coeff n = 0 := by
    intro n hn
    set negMap : ℂ →L[ℂ] ℂ := -(ContinuousLinearMap.id ℂ ℂ) with hnM
    have hneg0 : negMap 0 = 0 := by simp [negMap]
    have hcomp_neg : HasFPowerSeriesAt (h ∘ negMap)
        (p.compContinuousLinearMap negMap) 0 := by
      have : HasFPowerSeriesAt h p (negMap 0) := by rw [hneg0]; exact hp
      exact HasFPowerSeriesAt.compContinuousLinearMap this
    have heq : (h ∘ negMap) =ᶠ[nhds 0] h := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
      simp only [negMap, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply,
        Function.comp_apply, neg_neg]
      exact heven z (by simpa using hz)
    have hcomp_neg' : HasFPowerSeriesAt h (p.compContinuousLinearMap negMap) 0 :=
      hcomp_neg.congr heq
    have hcoeff_neg : (p.compContinuousLinearMap negMap).coeff n = (-1 : ℂ) ^ n • p.coeff n := by
      show (p.compContinuousLinearMap negMap) n 1 = (-1 : ℂ) ^ n • p n 1
      rw [compContinuousLinearMap_apply]
      have hneg1 : (negMap ∘ (1 : Fin n → ℂ)) = fun _ => (-1 : ℂ) := by
        funext i; simp [negMap]
      rw [hneg1, apply_eq_pow_smul_coeff, coeff]
    obtain ⟨r1, hr1⟩ := hp
    obtain ⟨r2, hr2⟩ := hcomp_neg'
    have key1 : Nat.factorial n • p.coeff n = iteratedDeriv n h 0 := by
      have hh : Nat.factorial n • p n (fun _ : Fin n => (1 : ℂ)) = iteratedFDeriv ℂ n h 0 fun _ => (1 : ℂ) :=
        hr1.factorial_smul (y := (1 : ℂ)) n
      rw [iteratedDeriv_eq_iteratedFDeriv]
      convert hh using 1
    have key2 : Nat.factorial n • (p.compContinuousLinearMap negMap).coeff n = iteratedDeriv n h 0 := by
      have hh : Nat.factorial n • (p.compContinuousLinearMap negMap) n (fun _ : Fin n => (1 : ℂ))
          = iteratedFDeriv ℂ n h 0 fun _ => (1 : ℂ) :=
        hr2.factorial_smul (y := (1 : ℂ)) n
      rw [iteratedDeriv_eq_iteratedFDeriv]
      convert hh using 1
    have hcoeff_eq : p.coeff n = (p.compContinuousLinearMap negMap).coeff n := by
      have h12 : Nat.factorial n • p.coeff n = Nat.factorial n • (p.compContinuousLinearMap negMap).coeff n :=
        key1.trans key2.symm
      have hn_ne : (Nat.factorial n : ℂ) ≠ 0 := mod_cast n.factorial_ne_zero
      have : (Nat.factorial n : ℂ) * p.coeff n = (Nat.factorial n : ℂ) * (p.compContinuousLinearMap negMap).coeff n := by
        simpa [smul_eq_mul] using h12
      exact mul_left_cancel₀ hn_ne this
    -- p.coeff n = (comp).coeff n = (-1)^n • p.coeff n.
    -- Chain: hcoeff_eq.trans hcoeff_neg gives the key identity.
    have hkey : p.coeff n = (-1 : ℂ) ^ n • p.coeff n := hcoeff_eq.trans hcoeff_neg
    rw [hn.neg_one_pow, smul_eq_mul] at hkey
    -- hkey : p.coeff n = -1 * p.coeff n, so 2 * p.coeff n = 0
    have h2 : 2 * p.coeff n = 0 := by linear_combination hkey
    have h20 : (2 : ℂ) * 0 = 0 := by norm_num
    exact mul_left_cancel₀ two_ne_zero (h2.trans h20.symm)
  -- A square-root selector defines the descended function.  It need not be analytic:
  -- evenness makes the value independent of the chosen root.
  let q := FormalMultilinearSeries.ofScalars ℂ (fun n => p.coeff (2 * n))
  let g : ℂ → ℂ := fun w => h (evenFactorRoot w)
  have hfactor : ∀ z, ‖z‖ < 1 → g (z ^ 2) = h z := by
    intro z hz
    have hsquare : evenFactorRoot (z ^ 2) ^ 2 = z ^ 2 := evenFactorRoot_sq _
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with hr | hr
    · simp [g, hr]
    · simpa [g, hr] using heven z hz
  refine ⟨g, ?_, hfactor⟩
  intro w hw
  have hwnorm : ‖w‖ < 1 := by simpa using hw
  by_cases hw0 : w = 0
  · subst w
    -- At the branch point, reindex the local Taylor series using the vanished
    -- odd coefficients.
    have hqrad : 0 < q.radius := evenCoefficients_radius_pos p hp.radius_pos
    have hq : HasFPowerSeriesAt q.sum q 0 :=
      ⟨q.radius, q.hasFPowerSeriesOnBall hqrad⟩
    have heq : q.sum =ᶠ[nhds 0] g := by
      simpa [q, g] using evenCoefficients_sum h p hp hodd
    exact (hq.congr heq).analyticAt.analyticWithinAt
  · -- Away from the branch point, the squaring map has nonzero derivative,
    -- so analyticity descends by the analytic inverse-function theorem.
    let z := evenFactorRoot w
    have hzsq : z ^ 2 = w := evenFactorRoot_sq w
    have hz0 : z ≠ 0 := by
      intro hz
      apply hw0
      rw [← hzsq, hz]
      norm_num
    have hznorm : ‖z‖ < 1 := by
      have hs := congrArg norm hzsq
      rw [norm_pow] at hs
      nlinarith [sq_nonneg ‖z‖]
    have hzmem : z ∈ Metric.ball (0 : ℂ) 1 := by simpa using hznorm
    have hlocal : (g ∘ fun u : ℂ => u ^ 2) =ᶠ[nhds z] h := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzmem] with u hu
      exact hfactor u (by simpa using hu)
    have hhAt : AnalyticAt ℂ h z :=
      hh.analyticAt (Metric.isOpen_ball.mem_nhds hzmem)
    have hcomp : AnalyticAt ℂ (g ∘ fun u : ℂ => u ^ 2) z :=
      hhAt.congr hlocal.symm
    have hsquareAt : AnalyticAt ℂ (fun u : ℂ => u ^ 2) z :=
      analyticAt_id.pow 2
    have hderiv : deriv (fun u : ℂ => u ^ 2) z ≠ 0 := by
      rw [(hasDerivAt_pow 2 z).deriv]
      simp [hz0]
    have hgAt : AnalyticAt ℂ g w := by
      rw [← hzsq]
      exact (analyticAt_comp_iff_of_deriv_ne_zero hsquareAt hderiv).mp hcomp
    exact hgAt.analyticWithinAt

/-- Main theorem: f(z) = z/(e^{2πz}-1) + z/2 factors as g(z²) for some
    analytic g on the open unit disk. -/
theorem apm_a96J10_main :
    ∃ g : ℂ → ℂ, AnalyticOn ℂ g (Metric.ball (0:ℂ) 1) ∧
      ∀ z : ℂ, ‖z‖ < 1 → z ≠ 0 →
        g (z ^ 2) = z / (Complex.exp (2 * Real.pi * z) - 1) + z / 2 := by
  rcases apm_a96J10_even_factors apm_a96J10_f apm_a96J10_f_analytic
      (fun z hz => apm_a96J10_f_even z hz) with ⟨g, hg, hfactor⟩
  refine ⟨g, hg, ?_⟩
  intro z hz hz0
  calc
    g (z ^ 2) = apm_a96J10_f z := hfactor z hz
    _ = z / (Complex.exp (2 * Real.pi * z) - 1) + z / 2 := by
      simp [apm_a96J10_f, hz0]
