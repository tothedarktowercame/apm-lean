import Mathlib
import ConstructionTargets.SardCriticalRankStrata

/-! # Null-image aggregation over critical rank strata -/

open Set Function MeasureTheory
noncomputable section

/-- If the image of every exact rank stratum below the target dimension is
null, then the image of the entire nonsurjective locus is null. -/
theorem criticalImage_null_of_rankStrata_null
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] (μ : Measure F) (f : E → F)
    (f' : E → E →ₗ[ℝ] F)
    (hnull : ∀ r : Fin (Module.finrank ℝ F), μ (f '' rankStratum f' r) = 0) :
    μ (f '' criticalSet f') = 0 := by
  rw [criticalSet_eq_iUnion_rankStratum, image_iUnion]
  exact measure_iUnion_null hnull

#print axioms criticalImage_null_of_rankStrata_null
