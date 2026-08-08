import Mathlib

set_option maxHeartbeats 800000

/-!
# APM a93J03

## Statement repairs

None.  The source indexing `n = 1,2,…` is represented by `n + 1` for
`n : ℕ`.

## Encoding questions

None. Lebesgue measure is `volume`, almost-everywhere quantification uses its
standard measure filter, and absolute convergence is `Summable` of the
pointwise absolute values.
-/

open MeasureTheory Filter

def apm_a93j03_exceptionalSet (f : ℕ → ℝ → ℝ) (n : ℕ) : Set ℝ :=
  {x | |f (n + 1) x| > 1 / ((n + 1 : ℕ) : ℝ) ^ 2}

theorem apm_a93j03
    (f : ℕ → ℝ → ℝ)
    (hf : ∀ n : ℕ, Measurable (f (n + 1)))
    (hμ : ∀ n : ℕ,
      volume (apm_a93j03_exceptionalSet f n) ≤
        ((2 : ENNReal) ^ (n + 1))⁻¹) :
    ∀ᵐ x : ℝ ∂volume, Summable (fun n : ℕ => |f (n + 1) x|) := by
  have hsum : (∑' n : ℕ, volume (apm_a93j03_exceptionalSet f n)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hμ)
    have hfun : (fun n : ℕ => ((2 : ENNReal) ^ (n + 1))⁻¹) =
        fun n : ℕ => (2 : ENNReal)⁻¹ * ((2 : ENNReal)⁻¹) ^ n := by
      funext n
      rw [pow_succ, ENNReal.mul_inv (by simp) (by simp), ENNReal.inv_pow]
      exact mul_comm _ _
    rw [hfun, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
      ENNReal.one_sub_inv_two, inv_inv]
    simp
  filter_upwards [MeasureTheory.ae_eventually_notMem hsum] with x hx
  have hmajorant : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
    simpa only [one_div] using
      ((Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)).comp_injective
        Nat.succ_injective
  apply hmajorant.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hx] with n hn
  change ¬|f (n + 1) x| > 1 / ((n + 1 : ℕ) : ℝ) ^ 2 at hn
  simpa only [Real.norm_eq_abs, abs_abs] using le_of_not_gt hn
