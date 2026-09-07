import ConstructionTargets.SardPositivePowerTolerance

open scoped ENNReal NNReal

/-- A positive contracting `NNReal` radius supplies a geometric scale at which
a finite constant times the positive residual dimension power is below any
positive `ENNReal` tolerance. -/
theorem ENNReal.exists_nnreal_geometric_scale_pow_lt
    (D ε : ENNReal) (q : ℝ≥0) (d : ℕ)
    (hq0 : 0 < q) (hq1 : q < 1) (hd : 0 < d)
    (hε : 0 < ε) (hD : D ≠ ⊤) :
    ∃ j : ℕ, D * ENNReal.ofReal ((q : ℝ) ^ j) ^ d < ε := by
  have hq1' : (q : ENNReal) < 1 := by exact_mod_cast hq1
  have hqd : (q : ENNReal) ^ d < 1 :=
    pow_lt_one₀ (by positivity) hq1' (Nat.ne_of_gt hd)
  obtain ⟨j, hj⟩ := ENNReal.exists_const_mul_pow_lt D ((q : ENNReal) ^ d) ε hqd hε hD
  refine ⟨j, ?_⟩
  rw [ENNReal.ofReal_pow (show 0 ≤ (q : ℝ) by positivity),
    ENNReal.ofReal_coe_nnreal]
  calc
    D * ((q : ENNReal) ^ j) ^ d = D * ((q : ENNReal) ^ d) ^ j := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ < ε := hj

#print axioms ENNReal.exists_nnreal_geometric_scale_pow_lt
