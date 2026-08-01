import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.Analysis.Normed.Group.Tannery

open MeasureTheory Filter Set Function

noncomputable section

namespace APM

open scoped Topology

/-- Pointwise sum of the monotone sequence of maps. -/
def pointwiseSum (fns : ℕ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n, fns n x

/-- Pointwise sum of the derivatives. -/
def derivativeSum (fns : ℕ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n, deriv (fun y => fns n y) x

/-- A pointwise-convergent series of monotone real functions is monotone. -/
lemma pointwiseSum_monotone
    (fns : ℕ → ℝ → ℝ) (hmono : ∀ n, Monotone (fns n))
    (hsummable : ∀ x, Summable fun n => fns n x) :
    Monotone (pointwiseSum fns) := by
  intro x y hxy
  exact (hsummable x).tsum_le_tsum (fun n => hmono n hxy) (hsummable y)

/-- Part (1): the derivative of the series exists a.e. and equals the sum of derivatives. -/
theorem deriv_sum_of_monotone
    (f : ℝ → ℝ) (fns : ℕ → ℝ → ℝ)
    (hmono : ∀ n, Monotone (fns n))
    (hsummable : ∀ x, Summable fun n => fns n x)
    (hf : ∀ x, f x = pointwiseSum fns x) :
    ∀ᵐ x ∂volume, HasDerivAt f (derivativeSum fns x) x := by
  let μs : ℕ → Measure ℝ := fun n => (hmono n).stieltjesFunction.measure
  have hfmono : Monotone f := by
    intro x y hxy
    rw [hf x, hf y]
    exact pointwiseSum_monotone fns hmono hsummable hxy
  have hright (x : ℝ) :
      Summable (fun n => rightLim (fns n) x) ∧
        rightLim f x = ∑' n, rightLim (fns n) x := by
    let B : ℕ → ℝ := fun n => fns n (x + 1) - fns n x
    have hB : Summable B := (hsummable (x + 1)).sub (hsummable x)
    have hlim (n : ℕ) :
        Tendsto (fun y => fns n y - fns n x) (nhdsWithin x (Ioi x))
          (nhds (rightLim (fns n) x - fns n x)) :=
      ((hmono n).tendsto_rightLim x).sub_const _
    have hbound : ∀ᶠ y in nhdsWithin x (Ioi x),
        ∀ n, ‖fns n y - fns n x‖ ≤ B n := by
      filter_upwards [Ioo_mem_nhdsGT (show x < x + 1 by linarith)] with y hy
      intro n
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hmono n hy.1.le))]
      exact sub_le_sub_right (hmono n hy.2.le) _
    have hT := tendsto_tsum_of_dominated_convergence hB hlim hbound
    have hsum_eq (y : ℝ) :
        (∑' n, (fns n y - fns n x)) = f y - f x := by
      rw [(hsummable y).tsum_sub (hsummable x), ← pointwiseSum, ← pointwiseSum,
        ← hf y, ← hf x]
    have hrightdiff :
        rightLim f x - f x = ∑' n, (rightLim (fns n) x - fns n x) := by
      apply tendsto_nhds_unique ((hfmono.tendsto_rightLim x).sub_const _)
      exact hT.congr' (Eventually.of_forall fun y => hsum_eq y)
    have hjump_nonneg (n : ℕ) : 0 ≤ rightLim (fns n) x - fns n x :=
      sub_nonneg.mpr ((hmono n).le_rightLim le_rfl)
    have hjump_le (n : ℕ) : rightLim (fns n) x - fns n x ≤ B n := by
      dsimp [B]
      exact sub_le_sub_right ((hmono n).rightLim_le (by linarith)) _
    have hjump_sum : Summable (fun n => rightLim (fns n) x - fns n x) :=
      Summable.of_nonneg_of_le hjump_nonneg hjump_le hB
    constructor
    · have := (hsummable x).add hjump_sum
      simpa only [add_sub_cancel] using this
    · calc
        rightLim f x = f x + (rightLim f x - f x) := by
          ring
        _ = (∑' n, fns n x) + ∑' n, (rightLim (fns n) x - fns n x) := by
          rw [← pointwiseSum, ← hf x, hrightdiff]
        _ = ∑' n, (fns n x + (rightLim (fns n) x - fns n x)) := by
          rw [(hsummable x).tsum_add hjump_sum]
        _ = ∑' n, rightLim (fns n) x := by
          apply tsum_congr
          intro n
          ring
  have hmeasure : hfmono.stieltjesFunction.measure = Measure.sum μs := by
    apply Measure.ext_of_Ioc
    intro a b hab
    rw [StieltjesFunction.measure_Ioc, Measure.sum_apply _ measurableSet_Ioc]
    simp_rw [μs, StieltjesFunction.measure_Ioc, Monotone.stieltjesFunction_eq]
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    · congr 1
      rw [hright b |>.2, hright a |>.2, (hright b |>.1).tsum_sub (hright a |>.1)]
    · intro n
      exact sub_nonneg.mpr ((hmono n).rightLim hab.le)
    · exact (hright b |>.1).sub (hright a |>.1)
  let s : Measure ℝ := Measure.sum fun n => (μs n).singularPart volume
  let d : ℝ → ENNReal := fun x => ∑' n, (μs n).rnDeriv volume x
  have hd_meas : Measurable d := by
    dsimp [d]
    fun_prop
  have hs_sing : s ⟂ₘ volume := by
    dsimp [s]
    exact Measure.MutuallySingular.sum_left.2 fun n =>
      Measure.mutuallySingular_singularPart _ _
  have hdecomp : Measure.sum μs = s + volume.withDensity d := by
    dsimp [s, d]
    symm
    have hdsum : Summable (fun n => (μs n).rnDeriv volume) :=
      Pi.summable.2 fun _ => ENNReal.summable
    rw [show (fun x => ∑' n, (μs n).rnDeriv volume x) =
        ∑' n, (μs n).rnDeriv volume by
      funext x
      exact (tsum_apply hdsum).symm]
    rw [withDensity_tsum (fun n => Measure.measurable_rnDeriv (μs n) volume),
      Measure.sum_add_sum]
    congr 1
    funext n
    exact Measure.singularPart_add_rnDeriv (μs n) volume
  have hd_rn : d =ᵐ[volume] (Measure.sum μs).rnDeriv volume :=
    Measure.eq_rnDeriv hd_meas hs_sing hdecomp
  have hd_rn_f : d =ᵐ[volume] hfmono.stieltjesFunction.measure.rnDeriv volume := by
    simpa only [hmeasure] using hd_rn
  have hsum_finite : ∀ᵐ x ∂volume, d x ≠ ⊤ := by
    filter_upwards [hd_rn_f,
      Measure.rnDeriv_lt_top hfmono.stieltjesFunction.measure volume] with x hx hxtop
    exact hx.trans_ne hxtop.ne
  have hterms_finite : ∀ᵐ x ∂volume, ∀ n, (μs n).rnDeriv volume x ≠ ⊤ := by
    apply ae_all_iff.2
    intro n
    exact Measure.rnDeriv_lt_top (μs n) volume |>.mono fun x hx => hx.ne
  have hf_deriv := hfmono.ae_hasDerivAt
  have hfns_deriv : ∀ᵐ x ∂volume, ∀ n,
      HasDerivAt (fns n) ((μs n).rnDeriv volume x).toReal x := by
    apply ae_all_iff.2
    intro n
    simpa [μs] using (hmono n).ae_hasDerivAt
  filter_upwards [hf_deriv, hfns_deriv, hd_rn_f, hsum_finite, hterms_finite]
    with x hfx hfnx hdrn hdfin htermfin
  have hd_real : (hfmono.stieltjesFunction.measure.rnDeriv volume x).toReal =
      ∑' n, ((μs n).rnDeriv volume x).toReal := by
    rw [← hdrn, show d x = ∑' n, (μs n).rnDeriv volume x by rfl,
      ENNReal.tsum_toReal_eq htermfin]
  rw [derivativeSum, tsum_congr fun n => (hfnx n).deriv, ← hd_real]
  exact hfx

/-- Part (2): convert the `HasDerivAt` statement into an equality of classical derivatives a.e. -/
theorem deriv_sum_of_monotone_ae
    (f : ℝ → ℝ) (fns : ℕ → ℝ → ℝ)
    (hmono : ∀ n, Monotone (fns n))
    (hsummable : ∀ x, Summable fun n => fns n x)
    (hf : ∀ x, f x = pointwiseSum fns x) :
    deriv f =ᵐ[volume] derivativeSum fns := by
  filter_upwards [deriv_sum_of_monotone f fns hmono hsummable hf] with x hx
  exact hx.deriv

end APM
