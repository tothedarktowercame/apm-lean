import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Dividing an analytic zero by a power

Repeated `dslope` is the analytic extension of division by `(z-a)^n` when
the first `n` Taylor coefficients vanish.  This packages precisely that
removable-singularity construction.
-/

open Function

noncomputable section

namespace ConstructionTargets.AnalyticDivision

/-- Repeated divided difference at `a`. -/
def dividedByPower (n : ℕ) (a : ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  (swap dslope a)^[n] f

/-- Repeated divided differences preserve analyticity at the base point. -/
theorem analyticAt_dividedByPower (n : ℕ) (a : ℂ) (f : ℂ → ℂ)
    (hf : AnalyticAt ℂ f a) : AnalyticAt ℂ (dividedByPower n a f) a := by
  let p := FormalMultilinearSeries.ofScalars ℂ
    (fun k => iteratedDeriv k f a / (k.factorial : ℂ))
  have hp : HasFPowerSeriesAt f p a := hf.hasFPowerSeriesAt
  exact (hp.has_fpower_series_iterate_dslope_fslope n).analyticAt

/-- The divided difference of a function analytic at its base point is again
analytic there. -/
theorem analyticAt_dslope (a : ℂ) (f : ℂ → ℂ)
    (hf : AnalyticAt ℂ f a) : AnalyticAt ℂ (dslope f a) a := by
  simpa [dividedByPower] using analyticAt_dividedByPower 1 a f hf

/-- At the base point, the `n`th repeated divided difference is the `n`th
Taylor coefficient. -/
theorem dividedByPower_apply_base (n : ℕ) (a : ℂ) (f : ℂ → ℂ)
    (hf : AnalyticAt ℂ f a) :
    dividedByPower n a f a = iteratedDeriv n f a / (n.factorial : ℂ) := by
  let p := FormalMultilinearSeries.ofScalars ℂ
    (fun k => iteratedDeriv k f a / (k.factorial : ℂ))
  have hp : HasFPowerSeriesAt f p a := hf.hasFPowerSeriesAt
  have h0 := (hp.has_fpower_series_iterate_dslope_fslope n).coeff_zero 1
  simpa [dividedByPower, p, FormalMultilinearSeries.coeff_iterate_fslope] using h0.symm

/-- Away from the base point, repeated divided difference is literal
division by `(z-a)^n`, provided all lower Taylor coefficients vanish. -/
theorem dividedByPower_eq_div {n : ℕ} {a z : ℂ} {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f a)
    (hzero : ∀ k < n, iteratedDeriv k f a = 0)
    (hz : z ≠ a) :
    dividedByPower n a f z = f z / (z - a) ^ n := by
  induction n with
  | zero => simp [dividedByPower]
  | succ n ih =>
      rw [dividedByPower, Function.iterate_succ_apply']
      change dslope ((swap dslope a)^[n] f) a z = _
      rw [dslope_of_ne _ hz]
      have hbase : dividedByPower n a f a = 0 := by
        rw [dividedByPower_apply_base n a f hf, hzero n (Nat.lt_succ_self n)]
        simp
      simp only [slope, smul_eq_mul, vsub_eq_sub]
      change (z - a)⁻¹ * (dividedByPower n a f z - dividedByPower n a f a) = _
      rw [hbase, sub_zero]
      rw [ih (fun k hk => hzero k (Nat.lt.step hk))]
      field_simp [sub_ne_zero.mpr hz]
      ring

end ConstructionTargets.AnalyticDivision
