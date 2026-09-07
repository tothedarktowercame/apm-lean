import Mathlib.Analysis.SpecificLimits.Basic

/-! # Positive-power tolerance choice -/

open Filter
open scoped Topology ENNReal

/-- A finite constant times a contracting geometric power eventually lies
below every positive `ENNReal` tolerance. -/
theorem ENNReal.exists_const_mul_pow_lt
    (C q ε : ENNReal) (hq : q < 1) (hε : 0 < ε) (hC : C ≠ ⊤) :
    ∃ n : ℕ, C * q ^ n < ε := by
  have ht : Tendsto (fun n : ℕ ↦ C * q ^ n) atTop (nhds 0) := by
    simpa only [mul_zero] using
      Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq) (Or.inr hC)
  exact ((tendsto_order.1 ht).2 ε hε).exists

#print axioms ENNReal.exists_const_mul_pow_lt
