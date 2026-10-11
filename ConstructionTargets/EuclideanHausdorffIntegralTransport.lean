import Mathlib.Geometry.Euclidean.Volume.Measure

open MeasureTheory

/-! Integral transport from normalized Euclidean Hausdorff measure to Hausdorff measure. -/

noncomputable section

namespace ConstructionTargets.EuclideanHausdorffIntegralTransport

variable {X G : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- `μHE[d]` is definitionally a scalar multiple of `μH[d]`; this is the
corresponding Bochner-integral formula on an arbitrary metric space, including
sphere subtypes. -/
theorem integral_euclideanHausdorffMeasure (d : ℕ) (f : X → G) :
    (∫ x, f x ∂μHE[d]) =
      (Measure.addHaarScalarFactor
          (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[d]).toReal •
        ∫ x, f x ∂μH[d] := by
  rw [Measure.euclideanHausdorffMeasure_def]
  exact integral_smul_measure f _

end ConstructionTargets.EuclideanHausdorffIntegralTransport

#print axioms ConstructionTargets.EuclideanHausdorffIntegralTransport.integral_euclideanHausdorffMeasure
