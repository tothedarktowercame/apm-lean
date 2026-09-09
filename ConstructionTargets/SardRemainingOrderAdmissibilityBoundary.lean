import ConstructionTargets.SardClassicalRegularityAdmissibility

open SardClassicalRegularityAdmissibilityProbe

theorem remainingOrder_admissible_iff
    (sourceDim targetDim order loss : ℕ) (hloss : loss ≤ order) :
    SardOrderAdmissible sourceDim targetDim (order - loss) ↔
      sourceDim + loss < targetDim + order := by
  unfold SardOrderAdmissible
  omega

theorem codimensionOne_remainingOrder_admissible_iff
    (sourceDim targetDim order loss : ℕ)
    (hsource : 0 < sourceDim) (hloss : loss ≤ order) :
    SardOrderAdmissible (sourceDim - 1) targetDim (order - loss) ↔
      sourceDim + loss ≤ targetDim + order := by
  unfold SardOrderAdmissible
  omega

theorem classical_admissibility_does_not_cover_all_jet_losses :
    SardOrderAdmissible 3 1 3 ∧
      1 ≤ (2 : ℕ) ∧ 2 < (3 : ℕ) ∧
      ¬ SardOrderAdmissible (3 - 1) 1 (3 - 2) := by
  norm_num [SardOrderAdmissible]

#print axioms remainingOrder_admissible_iff
#print axioms codimensionOne_remainingOrder_admissible_iff
#print axioms classical_admissibility_does_not_cover_all_jet_losses
