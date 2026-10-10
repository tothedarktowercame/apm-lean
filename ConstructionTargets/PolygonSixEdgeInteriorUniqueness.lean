import ConstructionTargets.PolygonSixEdgeCircleCover

noncomputable section

namespace ConstructionTargets.PolygonSixEdgeInteriorUniqueness

open PolygonBoundaryCircleRelations
open PolygonSixEdgeCircleCover

theorem circleEdgePoint_interior_injective
    (j k : Fin 6) (t u : Set.Ico (0 : ℝ) 1)
    (h : circleEdgePoint j ⟨t.1, t.2.1, t.2.2.le⟩ =
      circleEdgePoint k ⟨u.1, u.2.1, u.2.2.le⟩) :
    j = k ∧ t = u := by
  letI : Fact (0 < (6 : ℝ)) := ⟨by norm_num⟩
  rw [circleEdgePoint_eq_toCircle, circleEdgePoint_eq_toCircle] at h
  have hadd : (((j : ℕ) : ℝ) + t.1 : AddCircle (6 : ℝ)) =
      (((k : ℕ) : ℝ) + u.1 : AddCircle (6 : ℝ)) :=
    AddCircle.injective_toCircle (by norm_num) h
  have hj0 : 0 ≤ ((j : ℕ) : ℝ) + t.1 := by
    have : 0 ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith [t.2.1]
  have hk0 : 0 ≤ ((k : ℕ) : ℝ) + u.1 := by
    have : 0 ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith [u.2.1]
  have hj6 : ((j : ℕ) : ℝ) + t.1 < 6 := by
    have hj : ((j : ℕ) : ℝ) ≤ 5 := by
      exact_mod_cast Nat.le_pred_of_lt j.2
    linarith [t.2.2]
  have hk6 : ((k : ℕ) : ℝ) + u.1 < 6 := by
    have hk : ((k : ℕ) : ℝ) ≤ 5 := by
      exact_mod_cast Nat.le_pred_of_lt k.2
    linarith [u.2.2]
  have hre : ((j : ℕ) : ℝ) + t.1 = ((k : ℕ) : ℝ) + u.1 :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico ⟨hj0, by simpa using hj6⟩
      ⟨hk0, by simpa using hk6⟩).mp hadd
  fin_cases j <;> fin_cases k <;> simp_all only [Fin.mk.injEq,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  all_goals try { exfalso; linarith [t.2.1, t.2.2, u.2.1, u.2.2] }
  all_goals refine ⟨trivial, ?_⟩
  all_goals apply Subtype.ext; linarith

end ConstructionTargets.PolygonSixEdgeInteriorUniqueness
