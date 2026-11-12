import ConstructionTargets.AnalyticDivision

open ConstructionTargets.AnalyticDivision

noncomputable section

/-- Dividing the simple zero `z` gives the constant one. -/
example (z : ℂ) : dividedByPower 1 0 (fun w : ℂ => w) z = 1 := by
  by_cases hz : z = 0
  · subst z
    rw [dividedByPower_apply_base]
    · simp [iteratedDeriv_succ']
    · fun_prop
  · rw [dividedByPower_eq_div (n := 1) (by fun_prop) (by
      intro k hk
      interval_cases k
      simp) hz]
    simp [hz]

example : AnalyticAt ℂ (dslope (fun z : ℂ => z ^ 2) 1) 1 := by
  exact analyticAt_dslope 1 _ (by fun_prop)

#print axioms ConstructionTargets.AnalyticDivision.dividedByPower_eq_div
#print axioms ConstructionTargets.AnalyticDivision.analyticAt_dslope
